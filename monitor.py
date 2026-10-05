"""
保有銘柄の「権利付き最終日」と「関連ニュース・適時開示」を監視して Discord に通知する。
株価アラート(alert_check.py)とは別に、同じワークフローの中で続けて実行される。

【権利付き最終日】
  config.yaml の fiscal_month(決算期末月, 1〜12)から自動計算する。
  - 権利確定日は「決算期末月」と「その6か月後の月(中間)」の月末と仮定
  - 権利付き最終日 = 権利確定日(営業日に直したもの)の2営業日前
  - 7日前 / 3日前 / 1日前 / 当日 に通知(取りこぼしても次回実行時に補う)
  ※ 会社によって権利確定日が月末でないことがあるため、あくまで目安です。

【ニュース・適時開示】
  - ニュース : Googleニュース(会社名で検索) ※キーワードに該当した記事だけ通知
  - 適時開示 : TDnet(やのしん非公式WEB-API) ※新しい開示は全て通知
  - 好材料/悪材料の判定は見出しのキーワードによる簡易判定です(精度は粗い)
  - 最初の実行では既存の記事を「既読」にするだけで通知しません

通知には取得単価・保有株数などの金額情報は含めません。
状態は monitor_state.json に保存します。
"""

import calendar
import json
import os
import re
import unicodedata
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta, timezone
from urllib.parse import quote

import jpholiday
import requests
import yaml

CONFIG_PATH = "config.yaml"
STATE_PATH = "monitor_state.json"
WEBHOOK_URL = os.environ.get("DISCORD_WEBHOOK_URL")
JST = timezone(timedelta(hours=9))

NEWS_INTERVAL_MIN = 25          # ニュース確認の最短間隔(分)
RIGHTS_NOTICE_DAYS = [7, 3, 1, 0]  # 権利付き最終日の何日前に通知するか
MAX_SEEN = 150                  # 既読として覚えておく件数(銘柄・種類ごと)
MAX_NOTIFY_PER_TICKER = 5       # 1回の実行で1銘柄につき個別通知する最大件数
HEADERS = {"User-Agent": "stock-alert-monitor/1.0 (personal use)"}

WEEKDAYS = "月火水木金土日"

# ---------------------------------------------------------------- キーワード判定
POSITIVE_KEYWORDS = [
    "上方修正", "増配", "復配", "記念配当", "特別配当", "最高益", "過去最高",
    "増益", "黒字転換", "黒字化", "自社株買い", "自己株式の取得", "自己株式取得",
    "株式分割", "優待新設", "優待拡充", "株主優待を新設", "格上げ",
    "目標株価を引き上げ", "目標株価引き上げ", "大幅高", "急伸", "急騰",
    "年初来高値", "上場来高値",
]
NEGATIVE_KEYWORDS = [
    "下方修正", "減配", "無配", "最終赤字", "営業赤字", "赤字", "減益", "特別損失",
    "減損", "不正", "不適切", "不祥事", "粉飾", "改ざん", "業務停止", "業務改善命令",
    "行政処分", "課徴金", "リコール", "訴訟", "提訴", "格下げ",
    "目標株価を引き下げ", "目標株価引き下げ", "大幅安", "急落", "暴落", "ストップ安",
    "年初来安値", "上場来安値", "公募増資", "新株発行", "第三者割当", "希薄化",
    "株式売出", "優待廃止", "優待制度の廃止", "配当見送り", "事業撤退", "下振れ",
    "業績悪化", "債務超過", "継続企業の前提", "倒産", "破綻", "民事再生", "会社更生",
]
NOTABLE_KEYWORDS = [  # 方向が見出しだけでは分からないが、重要な可能性が高いもの
    "業績予想の修正", "配当予想の修正", "業績予想及び配当予想の修正",
    "TOB", "公開買付", "MBO", "経営統合", "合併", "株式交換", "株式移転",
    "上場廃止", "監理銘柄", "整理銘柄", "特設注意市場銘柄",
]

LABELS = {
    "good": ("🟢", "好材料の可能性"),
    "bad": ("🔴", "悪材料の可能性"),
    "mixed": ("🟡", "好悪混在・要確認"),
    "check": ("🟡", "要確認"),
    "neutral": ("⚪", "中立(キーワードなし)"),
}


def classify(text: str):
    pos = [k for k in POSITIVE_KEYWORDS if k in text]
    neg = [k for k in NEGATIVE_KEYWORDS if k in text]
    note = [k for k in NOTABLE_KEYWORDS if k in text]
    if pos and neg:
        return "mixed", pos + neg
    if pos:
        return "good", pos
    if neg:
        return "bad", neg
    if note:
        return "check", note
    return "neutral", []


# ---------------------------------------------------------------- 権利付き最終日
def is_trading_day(d: date) -> bool:
    if d.weekday() >= 5 or jpholiday.is_holiday(d):
        return False
    if (d.month == 12 and d.day == 31) or (d.month == 1 and d.day <= 3):
        return False  # 年末年始の休場
    return True


def last_trading_day_on_or_before(d: date) -> date:
    while not is_trading_day(d):
        d -= timedelta(days=1)
    return d


def trading_days_before(d: date, n: int) -> date:
    while n > 0:
        d -= timedelta(days=1)
        if is_trading_day(d):
            n -= 1
    return d


def record_months(fiscal_month: int) -> list:
    return sorted({fiscal_month, (fiscal_month + 5) % 12 + 1})


def next_rights_dates(fiscal_month: int, today: date):
    """今日以降でいちばん近い (権利確定日, 権利付き最終日) を返す。"""
    candidates = []
    for year in (today.year, today.year + 1):
        for m in record_months(fiscal_month):
            record = date(year, m, calendar.monthrange(year, m)[1])
            last_cum = trading_days_before(last_trading_day_on_or_before(record), 2)
            if last_cum >= today:
                candidates.append((record, last_cum))
    return min(candidates, key=lambda x: x[1]) if candidates else None


def fmt_date(d: date) -> str:
    return f"{d.month}/{d.day}({WEEKDAYS[d.weekday()]})"


def check_rights(holding: dict, today: date, state: dict) -> list:
    fm = holding.get("fiscal_month")
    if fm in (None, ""):
        return []
    try:
        fm = int(fm)
    except (TypeError, ValueError):
        return []
    if not 1 <= fm <= 12:
        return []

    found = next_rights_dates(fm, today)
    if not found:
        return []
    record, last_cum = found
    days = (last_cum - today).days

    threshold = next((t for t in sorted(RIGHTS_NOTICE_DAYS) if days <= t), None)
    if threshold is None:
        return []

    ticker = holding["ticker"]
    name = holding.get("name", ticker)
    key = f"{last_cum.isoformat()}:{threshold}"
    notified = state["rights_notified"].setdefault(ticker, [])
    if key in notified:
        return []
    notified.append(key)
    del notified[:-10]

    head = "本日が権利付き最終日です" if days == 0 else f"権利付き最終日まであと{days}日"
    return [
        f"📅 【{head}】{name}({ticker})\n"
        f"権利付き最終日: {fmt_date(last_cum)}(この日の大引けまで保有していれば権利が得られます)\n"
        f"権利確定日: {fmt_date(record)}(決算期末{fm}月から自動計算した目安)\n"
        f"※ 会社により権利確定日が異なる場合があります。公式IRで確認してください。"
    ]


# ---------------------------------------------------------------- ニュース・適時開示
KYUJITAI = str.maketrans({"澁": "渋", "澤": "沢", "髙": "高", "﨑": "崎", "國": "国",
                          "學": "学", "會": "会", "櫻": "桜", "眞": "真", "德": "徳",
                          "廣": "広", "關": "関"})


def build_name_variants(name: str) -> list:
    n = unicodedata.normalize("NFKC", name)
    n = re.sub(r"\s+", "", n)
    for w in ("株式会社", "(株)"):
        n = n.replace(w, "")
    variants = {n}
    short = n.replace("ホールディングス", "")
    if len(short) >= 2:
        variants.add(short)
    variants |= {v.translate(KYUJITAI) for v in list(variants)}
    return sorted((v for v in variants if v), key=len)


def fetch_google_news(name: str) -> list:
    q = "(" + " OR ".join(f'"{v}"' for v in build_name_variants(name)) + ") when:3d"
    url = f"https://news.google.com/rss/search?q={quote(q)}&hl=ja&gl=JP&ceid=JP:ja"
    r = requests.get(url, headers=HEADERS, timeout=20)
    r.raise_for_status()
    root = ET.fromstring(r.content)
    items = []
    for it in root.iterfind("./channel/item"):
        title = (it.findtext("title") or "").strip()
        link = (it.findtext("link") or "").strip()
        guid = (it.findtext("guid") or link).strip()
        if title and guid:
            items.append({"id": guid, "title": title, "link": link})
    return items


def fetch_tdnet(code: str) -> list:
    url = f"https://webapi.yanoshin.jp/webapi/tdnet/list/{code}.json?limit=10"
    r = requests.get(url, headers=HEADERS, timeout=20)
    r.raise_for_status()
    items = []
    for it in (r.json().get("items") or []):
        t = it.get("Tdnet") or {}
        title = (t.get("title") or "").strip()
        if not title:
            continue
        pub = t.get("pubdate") or ""
        items.append({
            "id": str(t.get("id") or f"{pub}|{title}"),
            "title": title,
            "link": t.get("document_url") or "",
        })
    return items


def pick_new(state: dict, ticker: str, key: str, items: list):
    """未通知の項目を返す。初回(その銘柄・種類を初めて見るとき)は既読化だけして空を返す。"""
    seen_map = state["seen"].setdefault(ticker, {})
    prev = seen_map.get(key)
    ids = [i["id"] for i in items]
    if prev is None:
        seen_map[key] = ids[:MAX_SEEN]
        return []
    prev_set = set(prev)
    new = [i for i in items if i["id"] not in prev_set]
    id_set = set(ids)
    seen_map[key] = (ids + [p for p in prev if p not in id_set])[:MAX_SEEN]
    return new


def build_item_messages(name, ticker, items, kind, keyword_only):
    msgs = []
    for it in items:
        label_key, words = classify(it["title"])
        if keyword_only and label_key == "neutral":
            continue
        emoji, label = LABELS[label_key]
        head = f"{emoji} 【{kind}/{label}】{name}({ticker})"
        body = it["title"]
        if it["link"]:
            body += f"\n<{it['link']}>"
        if words:
            body += f"\n検出ワード: {', '.join(words)}"
        msgs.append(f"{head}\n{body}")
    return msgs


def check_news(holding: dict, state: dict) -> list:
    ticker = holding["ticker"]
    name = holding.get("name", ticker)
    code = ticker.split(".")[0]
    messages = []

    try:
        news = fetch_google_news(name)
        new = pick_new(state, ticker, "news", news)
        messages += build_item_messages(name, ticker, new, "ニュース", keyword_only=True)
    except Exception as e:
        print(f"{ticker}: ニュース取得に失敗しました ({e})")

    try:
        td = fetch_tdnet(code)
        new = pick_new(state, ticker, "tdnet", td)
        messages += build_item_messages(name, ticker, new, "適時開示", keyword_only=False)
    except Exception as e:
        print(f"{ticker}: 適時開示の取得に失敗しました ({e})")

    return messages


# ---------------------------------------------------------------- 共通
def send_discord(message: str) -> None:
    print(message)
    if not WEBHOOK_URL:
        print("[WEBHOOK未設定のため送信スキップ]")
        return
    resp = requests.post(WEBHOOK_URL, json={"content": message[:1900]}, timeout=10)
    if resp.status_code >= 300:
        print(f"Discord送信失敗: {resp.status_code} {resp.text}")


def send_limited(messages: list, label: str) -> None:
    for m in messages[:MAX_NOTIFY_PER_TICKER]:
        send_discord(m)
    rest = len(messages) - MAX_NOTIFY_PER_TICKER
    if rest > 0:
        send_discord(f"（{label}: ほか{rest}件の新着があります）")


def load_state() -> dict:
    state = {}
    if os.path.exists(STATE_PATH):
        with open(STATE_PATH, encoding="utf-8") as f:
            state = json.load(f)
    state.setdefault("seen", {})
    state.setdefault("rights_notified", {})
    return state


def save_state(state: dict) -> None:
    with open(STATE_PATH, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=2)


def main() -> None:
    now = datetime.now(JST)
    today = now.date()

    with open(CONFIG_PATH, encoding="utf-8") as f:
        config = yaml.safe_load(f) or {}
    holdings = config.get("holdings") or []
    state = load_state()

    # 1) 権利付き最終日(毎回確認。通知済みの分は state で重複を防ぐ)
    for h in holdings:
        send_limited(check_rights(h, today, state), h.get("name", h["ticker"]))

    # 2) ニュース・適時開示(前回確認から一定時間たっているときだけ)
    last = state.get("last_news_check")
    due = True
    if last:
        try:
            due = now - datetime.fromisoformat(last) >= timedelta(minutes=NEWS_INTERVAL_MIN)
        except ValueError:
            due = True

    if due:
        for h in holdings:
            send_limited(check_news(h, state), h.get("name", h["ticker"]))
        state["last_news_check"] = now.isoformat()
    else:
        print(f"ニュース確認はスキップ(前回: {last})")

    save_state(state)


if __name__ == "__main__":
    main()
