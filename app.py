# -*- coding: utf-8 -*-
from __future__ import annotations

import hashlib
import html
import json
import math
import queue
import re
import sys
import threading
import time
import ctypes
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from tkinter import END, E, N, S, W, filedialog, messagebox
from html.parser import HTMLParser
import tkinter as tk
from tkinter import ttk


APP_NAME = "小说爬取器"
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36"
)
REQUEST_TIMEOUT = 18
FETCH_RETRIES = 3
REQUEST_DELAY_SECONDS = 0.03
DEFAULT_CONCURRENCY = 12
MAX_CONCURRENCY = 32
SAVE_EVERY_COMPLETED_CHAPTERS = 12
DELETE_CONFIRM_SECONDS = 2.6
MAX_CHAPTER_PAGES = 30
DEFAULT_READ_CHAIN_LIMIT = 80
MAX_READ_CHAIN_LIMIT = 1000
CONTENT_SCHEMA_VERSION = 3
EVENT_DRAIN_LIMIT = 260
CHAPTER_UI_UPDATES_PER_TICK = 24
EVENT_BUSY_DELAY_MS = 16
EVENT_IDLE_DELAY_MS = 90
TEXT_RENDER_CHUNK_SIZE = 12000
CHAPTER_RETRY_ICON = "↻"
CHAPTER_RETRY_BUSY_ICON = "…"
CRAWL_MODE_CATALOG = "catalog"
CRAWL_MODE_READ_CHAIN = "read_chain"
CRAWL_MODE_OPTIONS = {
    "目录页": CRAWL_MODE_CATALOG,
    "阅读页连续": CRAWL_MODE_READ_CHAIN,
}
CRAWL_MODE_LABELS = {value: label for label, value in CRAWL_MODE_OPTIONS.items()}
FONT_FAMILY = "Microsoft YaHei UI"
UI_FONT_SIZE = 10
UI_FONT = (FONT_FAMILY, UI_FONT_SIZE)
UI_FONT_BOLD = (FONT_FAMILY, UI_FONT_SIZE, "bold")
MONO_FONT = ("Consolas", UI_FONT_SIZE)
WINDOW_WIDTH_RATIO = 0.82
WINDOW_HEIGHT_RATIO = 0.78

COLORS = {
    "root": "#181818",
    "panel": "#181818",
    "editor": "#1e1e1e",
    "surface": "#1f1f1f",
    "surface_hover": "#2a2a2a",
    "border": "#2b2b2b",
    "border_focus": "#3c3c3c",
    "text": "#d4d4d4",
    "text_strong": "#eeeeee",
    "muted": "#9a9a9a",
    "subtle": "#6f6f6f",
    "selection": "#264f78",
    "accent": "#89b4d9",
    "danger": "#f44747",
    "warning": "#cca700",
}


def enable_high_dpi_awareness() -> None:
    if sys.platform != "win32":
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
        return
    except Exception:
        pass
    try:
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass


def enable_dark_title_bar(root: tk.Tk) -> None:
    if sys.platform != "win32":
        return
    try:
        root.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(root.winfo_id()) or root.winfo_id()
        value = ctypes.c_int(1)
        for attribute in (20, 19):
            result = ctypes.windll.dwmapi.DwmSetWindowAttribute(
                ctypes.c_void_p(hwnd),
                ctypes.c_int(attribute),
                ctypes.byref(value),
                ctypes.sizeof(value),
            )
            if result == 0:
                break
    except Exception:
        pass


def apply_app_icon(root: tk.Tk) -> None:
    try:
        if APP_ICON_PATH.exists():
            root.iconbitmap(default=str(APP_ICON_PATH))
    except Exception:
        pass


def apply_initial_window_geometry(root: tk.Tk) -> None:
    root.update_idletasks()
    screen_width = root.winfo_screenwidth()
    screen_height = root.winfo_screenheight()

    max_width = max(960, screen_width - 80)
    max_height = max(640, screen_height - 100)
    width = min(max_width, max(1320, int(screen_width * WINDOW_WIDTH_RATIO)))
    height = min(max_height, max(820, int(screen_height * WINDOW_HEIGHT_RATIO)))
    x = max(0, (screen_width - width) // 2)
    y = max(0, (screen_height - height) // 2)

    root.geometry(f"{width}x{height}+{x}+{y}")
    root.minsize(min(1180, max_width), min(720, max_height))


def app_base_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


BASE_DIR = app_base_dir()
BOOKS_DIR = BASE_DIR / "data" / "books"
ASSETS_DIR = BASE_DIR / "assets"
APP_ICON_PATH = ASSETS_DIR / "app.ico"


def normalize_space(value: str) -> str:
    return re.sub(r"\s+", " ", html.unescape(value or "")).strip()


def sanitize_filename(value: str, fallback: str = "novel") -> str:
    value = normalize_space(value)
    value = re.sub(r'[\\/:*?"<>|]+', "_", value)
    value = value.strip(" ._")
    return value[:90] or fallback


def now_iso() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def normalize_url_for_id(url: str) -> str:
    parsed = urllib.parse.urlsplit(url.strip())
    path = parsed.path or "/"
    if not parsed.query and not path.endswith("/"):
        path = path.rstrip("/")
    return urllib.parse.urlunsplit((parsed.scheme.lower(), parsed.netloc.lower(), path, parsed.query, ""))


def book_id_for(url: str) -> str:
    digest = hashlib.sha1(normalize_url_for_id(url).encode("utf-8", errors="ignore")).hexdigest()
    return digest[:14]


def same_site(left: str, right: str) -> bool:
    a = urllib.parse.urlparse(left)
    b = urllib.parse.urlparse(right)
    return a.scheme in {"http", "https"} and b.scheme in {"http", "https"} and a.netloc == b.netloc


def strip_url_fragment(url: str) -> str:
    parts = urllib.parse.urlsplit(url)
    return urllib.parse.urlunsplit((parts.scheme, parts.netloc, parts.path, parts.query, ""))


def _fetch_html_once(url: str) -> tuple[str, str]:
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.6",
        },
    )
    with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
        raw = response.read()
        final_url = response.geturl()
        encoding = response.headers.get_content_charset()

    if not encoding:
        head = raw[:4096].decode("ascii", errors="ignore")
        match = re.search(r"charset=[\"']?([a-zA-Z0-9_\-]+)", head, re.I)
        if match:
            encoding = match.group(1)

    candidates = [encoding, "utf-8", "gb18030", "gbk", "big5"]
    best_text = ""
    best_bad_count = 10**9
    for candidate in candidates:
        if not candidate:
            continue
        try:
            text = raw.decode(candidate, errors="replace")
        except LookupError:
            continue
        bad_count = text.count("\ufffd")
        if bad_count < best_bad_count:
            best_text = text
            best_bad_count = bad_count
        if bad_count == 0:
            break

    if not best_text:
        best_text = raw.decode("utf-8", errors="replace")
    return best_text, final_url


def fetch_html(url: str) -> tuple[str, str]:
    last_error: Exception | None = None
    for attempt in range(FETCH_RETRIES):
        try:
            return _fetch_html_once(url)
        except Exception as exc:
            last_error = exc
            if attempt < FETCH_RETRIES - 1:
                time.sleep(0.6 * (attempt + 1))
    if last_error:
        raise last_error
    raise RuntimeError("请求失败。")


def decode_web_bytes(raw: bytes, encoding: str | None = None) -> str:
    candidates = [encoding, "utf-8", "gb18030", "gbk", "big5"]
    best_text = ""
    best_bad_count = 10**9
    for candidate in candidates:
        if not candidate:
            continue
        try:
            text = raw.decode(candidate, errors="replace")
        except LookupError:
            continue
        bad_count = text.count("\ufffd")
        if bad_count < best_bad_count:
            best_text = text
            best_bad_count = bad_count
        if bad_count == 0:
            break
    return best_text or raw.decode("utf-8", errors="replace")


def fetch_text_file(url: str, timeout: int = 240) -> tuple[str, str]:
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "text/plain,text/html,*/*;q=0.8",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.6",
        },
    )
    with urllib.request.urlopen(request, timeout=timeout) as response:
        raw = response.read()
        final_url = response.geturl()
        encoding = response.headers.get_content_charset()
    return decode_web_bytes(raw, encoding), final_url


@dataclass
class HtmlNode:
    tag: str
    attrs: dict[str, str] = field(default_factory=dict)
    children: list[str | "HtmlNode"] = field(default_factory=list)
    parent: "HtmlNode | None" = None

    def attr_text(self) -> str:
        return " ".join(
            value.lower()
            for key, value in self.attrs.items()
            if key in {"id", "class", "role", "itemprop", "name"} and value
        )


class TreeBuilder(HTMLParser):
    void_tags = {
        "area",
        "base",
        "br",
        "col",
        "embed",
        "hr",
        "img",
        "input",
        "link",
        "meta",
        "param",
        "source",
        "track",
        "wbr",
    }
    skip_tags = {"script", "style", "noscript", "svg", "canvas"}

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.root = HtmlNode("document")
        self.stack = [self.root]
        self.base_href = ""
        self.title_parts: list[str] = []
        self._title_depth = 0
        self._skip_depth = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        tag = tag.lower()
        attrs_dict = {key.lower(): value or "" for key, value in attrs}
        if tag == "base" and attrs_dict.get("href"):
            self.base_href = attrs_dict["href"]
            return
        if tag in self.skip_tags:
            self._skip_depth += 1
            return
        if self._skip_depth:
            return
        if tag == "title":
            self._title_depth += 1
        if tag == "br":
            self.stack[-1].children.append("\n")
            return
        node = HtmlNode(tag=tag, attrs=attrs_dict, parent=self.stack[-1])
        self.stack[-1].children.append(node)
        if tag not in self.void_tags:
            self.stack.append(node)

    def handle_data(self, data: str) -> None:
        if self._skip_depth:
            return
        if self._title_depth:
            self.title_parts.append(data)
        if data:
            self.stack[-1].children.append(data)

    def handle_endtag(self, tag: str) -> None:
        tag = tag.lower()
        if self._skip_depth:
            if tag in self.skip_tags:
                self._skip_depth = max(0, self._skip_depth - 1)
            return
        if tag == "title" and self._title_depth:
            self._title_depth -= 1
        while len(self.stack) > 1:
            node = self.stack.pop()
            if node.tag == tag:
                break


BLOCK_TAGS = {
    "address",
    "article",
    "aside",
    "blockquote",
    "dd",
    "div",
    "dl",
    "dt",
    "figcaption",
    "figure",
    "footer",
    "h1",
    "h2",
    "h3",
    "h4",
    "h5",
    "h6",
    "header",
    "li",
    "main",
    "nav",
    "ol",
    "p",
    "pre",
    "section",
    "table",
    "tbody",
    "td",
    "tfoot",
    "th",
    "thead",
    "tr",
    "ul",
}
POSITIVE_CONTENT_WORDS = {
    "article",
    "bookcontent",
    "chaptercontent",
    "content",
    "entry",
    "main",
    "novelcontent",
    "post",
    "read",
    "reader",
    "text",
    "txt",
    "zhangjie",
    "正文",
    "内容",
    "章节",
    "阅读",
}
POSITIVE_CATALOG_WORDS = {
    "booklist",
    "catalog",
    "chapter",
    "chapterlist",
    "chapters",
    "dir",
    "directory",
    "list",
    "listmain",
    "volume",
    "正文",
    "目录",
    "章节",
    "卷",
}
NEGATIVE_CONTAINER_WORDS = {
    "ad",
    "ads",
    "banner",
    "baocuo",
    "comment",
    "error",
    "footer",
    "fanye",
    "guess",
    "header",
    "menu",
    "nav",
    "notice",
    "recommend",
    "related",
    "sidebar",
    "top",
    "tuijian",
    "评论",
    "导航",
    "广告",
    "推荐",
    "菜单",
}
NAV_LINK_WORDS = {
    "首页",
    "上一页",
    "下一页",
    "上一章",
    "下一章",
    "尾页",
    "返回",
    "书架",
    "登录",
    "注册",
    "搜索",
    "排行",
    "分类",
    "推荐",
    "投票",
    "下载",
    "作者",
    "简介",
    "最新章节",
    "章节目录",
    "全部章节",
    "加入书架",
    "手机阅读",
}
NOISE_LINE_PATTERNS = [
    r"^上一[章节页].*下一[章节页]$",
    r"^上一[章节页]$",
    r"^下一[章节页]$",
    r"^返回目录$",
    r"^章节目录$",
    r"^加入书架$",
    r"^推荐本书$",
    r"^手机阅读$",
    r"^最新网址[:：]",
    r"^请收藏",
    r"^本章未完",
    r"^.*全手打无错.*$",
    r"^.*\.com.*$",
    r"^.*\.org.*$",
    r"^章节报错",
    r"^目录$",
    r"^存书签$",
    r"^请选择错误类型$",
    r"^更新太慢$",
    r"^缺少章节$",
    r"^章节内容错误$",
    r"^验证码[:：]?$",
    r"^提交关闭$",
    r"^猜你喜欢[:：]?$",
]
CHAPTER_TITLE_PATTERN = re.compile(
    r"(第\s*[0-9零〇一二两三四五六七八九十百千万壹贰叁肆伍陆柒捌玖拾佰仟]+\s*[章节卷集回部篇幕]|"
    r"序章|楔子|番外|后记|Chapter\s*\d+|^\s*\d+\s*[.、_-])",
    re.I,
)


@dataclass
class LinkEntry:
    title: str
    url: str
    index: int
    node: HtmlNode
    chapter_no: int | None = None


def parse_html_tree(html_text: str) -> TreeBuilder:
    parser = TreeBuilder()
    parser.feed(html_text)
    parser.close()
    return parser


def iter_nodes(node: HtmlNode) -> list[HtmlNode]:
    nodes = [node]
    for child in node.children:
        if isinstance(child, HtmlNode):
            nodes.extend(iter_nodes(child))
    return nodes


def find_first_node(root: HtmlNode, predicate) -> HtmlNode | None:
    for node in iter_nodes(root):
        if predicate(node):
            return node
    return None


def node_has_class(node: HtmlNode, class_name: str) -> bool:
    classes = node.attrs.get("class", "").split()
    return class_name in classes


def node_id_equals(node: HtmlNode, value: str) -> bool:
    return node.attrs.get("id", "") == value


def is_sudugu_url(url: str) -> bool:
    host = urllib.parse.urlparse(url).netloc.lower()
    return host == "sudugu.org" or host.endswith(".sudugu.org")


def is_biquge345_url(url: str) -> bool:
    host = urllib.parse.urlparse(url).netloc.lower()
    return host == "biquge345.com" or host.endswith(".biquge345.com")


def is_69shuba_url(url: str) -> bool:
    host = urllib.parse.urlparse(url).netloc.lower()
    return host == "69shuba.tw" or host.endswith(".69shuba.tw")


def is_69shuba_read_url(url: str) -> bool:
    if not is_69shuba_url(url):
        return False
    return bool(re.search(r"^/read/\d+/\d+/?$", urllib.parse.urlparse(url).path))


def shuba69_book_id_from_read_url(url: str) -> str:
    match = re.search(r"^/read/(\d+)/\d+/?$", urllib.parse.urlparse(url).path)
    return match.group(1) if match else ""


def shuba69_read_chapter_belongs_to_book(start_url: str, chapter_url: str) -> bool:
    if not (is_69shuba_url(start_url) and is_69shuba_url(chapter_url)):
        return False
    book_id = shuba69_book_id_from_read_url(start_url)
    if not book_id:
        return False
    return bool(re.search(rf"^/read/{re.escape(book_id)}/\d+/?$", urllib.parse.urlparse(chapter_url).path))


def biquge345_book_id_from_url(url: str) -> str:
    match = re.search(r"/book/(\d+)/?", urllib.parse.urlparse(url).path)
    return match.group(1) if match else ""


def biquge345_chapter_belongs_to_book(toc_url: str, chapter_url: str) -> bool:
    if not same_site(toc_url, chapter_url):
        return False
    book_id = biquge345_book_id_from_url(toc_url)
    if not book_id:
        return False
    return urllib.parse.urlparse(chapter_url).path.startswith(f"/chapter/{book_id}/")


def cleanup_biquge345_title(title: str) -> str:
    title = normalize_space(title)
    if not title:
        return ""
    title = re.split(r"[_\-|]", title)[0]
    title = re.sub(r"(最新章节|全文阅读|无弹窗|笔趣阁|小说).*", "", title)
    return normalize_space(title)[:90]


def plain_text(node: HtmlNode) -> str:
    parts: list[str] = []
    for child in node.children:
        if isinstance(child, str):
            parts.append(child)
        else:
            parts.append(plain_text(child))
    return normalize_space("".join(parts))


def link_text_length(node: HtmlNode) -> int:
    if node.tag == "a":
        return len(plain_text(node))
    total = 0
    for child in node.children:
        if isinstance(child, HtmlNode):
            total += link_text_length(child)
    return total


def has_word(text: str, words: set[str]) -> bool:
    text = text.lower()
    return any(word in text for word in words)


def node_depth(node: HtmlNode) -> int:
    depth = 0
    current = node.parent
    while current is not None:
        depth += 1
        current = current.parent
    return depth


def cleanup_page_title(title: str) -> str:
    title = normalize_space(title)
    title = re.sub(r"(最新章节|全文阅读|无弹窗|章节目录|目录|小说).*", "", title)
    title = re.split(r"[_\-|—]+", title)[0]
    return normalize_space(title)[:90]


def find_first_heading(root: HtmlNode) -> str:
    for node in iter_nodes(root):
        if node.tag in {"h1", "h2"}:
            text = plain_text(node)
            if 1 < len(text) <= 90 and not has_word(text, {"目录", "书架", "搜索"}):
                return text
    return ""


CN_DIGITS = {
    "零": 0,
    "〇": 0,
    "一": 1,
    "二": 2,
    "两": 2,
    "三": 3,
    "四": 4,
    "五": 5,
    "六": 6,
    "七": 7,
    "八": 8,
    "九": 9,
    "壹": 1,
    "贰": 2,
    "叁": 3,
    "肆": 4,
    "伍": 5,
    "陆": 6,
    "柒": 7,
    "捌": 8,
    "玖": 9,
}
CN_UNITS = {"十": 10, "拾": 10, "百": 100, "佰": 100, "千": 1000, "仟": 1000, "万": 10000}


def chinese_number_to_int(value: str) -> int | None:
    value = normalize_space(value)
    if not value:
        return None
    if value.isdigit():
        return int(value)
    total = 0
    section = 0
    number = 0
    seen = False
    for char in value:
        if char.isdigit():
            number = number * 10 + int(char)
            seen = True
        elif char in CN_DIGITS:
            number = CN_DIGITS[char]
            seen = True
        elif char in CN_UNITS:
            unit = CN_UNITS[char]
            seen = True
            if unit == 10000:
                section = (section + number) or 1
                total += section * unit
                section = 0
            else:
                section += (number or 1) * unit
            number = 0
        else:
            return None
    result = total + section + number
    return result if seen else None


def extract_chapter_number(title: str) -> int | None:
    title = normalize_space(title)
    match = re.search(
        r"第\s*([0-9零〇一二两三四五六七八九十百千万壹贰叁肆伍陆柒捌玖拾佰仟]+)\s*[章节卷集回部篇幕]",
        title,
    )
    if match:
        return chinese_number_to_int(match.group(1))
    match = re.search(r"Chapter\s*(\d+)", title, re.I)
    if match:
        return int(match.group(1))
    match = re.search(r"^\s*(\d{1,5})\s*[.、_-]", title)
    if match:
        return int(match.group(1))
    if "序章" in title or "楔子" in title:
        return -1
    if "后记" in title:
        return 999999
    match = re.search(r"番外\s*([0-9零〇一二两三四五六七八九十百千万]+)?", title)
    if match:
        number = chinese_number_to_int(match.group(1) or "0") or 0
        return 900000 + number
    return None


def clean_chapter_title(title: str, book_title: str = "") -> str:
    title = normalize_space(title)
    if ">" in title or "＞" in title:
        parts = [normalize_space(part) for part in re.split(r"[>＞»]+", title) if normalize_space(part)]
        if parts and any(CHAPTER_TITLE_PATTERN.search(part) for part in parts):
            title = parts[-1]
    if book_title and title.startswith(book_title):
        title = title[len(book_title) :].strip(" -_>|＞")
    return normalize_space(title)


def is_chapter_title(title: str) -> bool:
    return bool(CHAPTER_TITLE_PATTERN.search(normalize_space(title)))


def is_navigation_text(title: str) -> bool:
    title = normalize_space(title)
    if not title or len(title) > 100:
        return True
    if title in NAV_LINK_WORDS:
        return True
    return has_word(title, {"首页", "书架", "登录", "注册", "搜索", "投票"})


def toc_scope_path(toc_url: str) -> str:
    path = urllib.parse.urlparse(toc_url).path or "/"
    if path.endswith("/"):
        return path
    if "." in path.rsplit("/", 1)[-1]:
        return path.rsplit("/", 1)[0] + "/"
    return path.rstrip("/") + "/"


def chapter_url_belongs_to_book(toc_url: str, chapter_url: str) -> bool:
    if is_69shuba_read_url(toc_url):
        return shuba69_read_chapter_belongs_to_book(toc_url, chapter_url)
    if not same_site(toc_url, chapter_url):
        return False
    toc_path = urllib.parse.urlparse(toc_url).path.rstrip("/")
    chapter_path = urllib.parse.urlparse(chapter_url).path
    scope = toc_scope_path(toc_url)
    if chapter_path.rstrip("/") == toc_path:
        return False
    return chapter_path.startswith(scope)


def extract_link_entries(node: HtmlNode, base_url: str, final_url: str, book_title: str) -> list[LinkEntry]:
    entries: list[LinkEntry] = []
    index = 0
    for candidate in iter_nodes(node):
        if candidate.tag != "a":
            continue
        href = candidate.attrs.get("href", "")
        if not href or href.startswith(("javascript:", "mailto:", "#")):
            continue
        absolute_url = strip_url_fragment(urllib.parse.urljoin(base_url, href))
        if not same_site(final_url, absolute_url):
            continue
        raw_title = plain_text(candidate)
        title = clean_chapter_title(raw_title, book_title)
        if is_navigation_text(title):
            continue
        index += 1
        entries.append(
            LinkEntry(
                title=title,
                url=absolute_url,
                index=index,
                node=candidate,
                chapter_no=extract_chapter_number(title),
            )
        )
    return entries


def is_chapter_link(entry: LinkEntry, allow_url_fallback: bool) -> bool:
    lowered_url = entry.url.lower()
    if any(value in lowered_url for value in ["#comment", "download", "author"]):
        return False
    if is_chapter_title(entry.title):
        return True
    if allow_url_fallback and re.search(r"/\d+(\.html?|/)?($|\?)", lowered_url):
        return True
    return False


def dedupe_links(entries: list[LinkEntry]) -> list[LinkEntry]:
    result: list[LinkEntry] = []
    seen_urls: set[str] = set()
    seen_number_titles: set[tuple[int | None, str]] = set()
    for entry in entries:
        if entry.url in seen_urls:
            continue
        key = (entry.chapter_no, entry.title)
        if entry.chapter_no is not None and key in seen_number_titles:
            continue
        seen_urls.add(entry.url)
        seen_number_titles.add(key)
        result.append(entry)
    return result


def chapter_sort_key(entry: LinkEntry) -> tuple[int, int, int]:
    if entry.chapter_no is None:
        return (1, entry.index, 0)
    if entry.chapter_no < 0:
        return (0, entry.chapter_no, entry.index)
    if entry.chapter_no >= 900000:
        return (2, entry.chapter_no, entry.index)
    return (1, entry.chapter_no, entry.index)


def choose_catalog_entries(root: HtmlNode, base_url: str, final_url: str, toc_url: str, book_title: str) -> list[LinkEntry]:
    all_nodes = iter_nodes(root)
    scored: list[tuple[float, HtmlNode, list[LinkEntry]]] = []
    for node in all_nodes:
        if node.tag not in {"document", "body", "main", "article", "section", "div", "dl", "ul", "ol", "table"}:
            continue
        entries = extract_link_entries(node, base_url, final_url, book_title)
        allow_url_fallback = len([entry for entry in entries if is_chapter_title(entry.title)]) < 3
        chapter_entries = [entry for entry in entries if is_chapter_link(entry, allow_url_fallback)]
        chapter_entries = dedupe_links(chapter_entries)
        if len(chapter_entries) < 3:
            continue

        numbered_count = len([entry for entry in chapter_entries if entry.chapter_no is not None])
        attr_text = node.attr_text()
        total_links = len(entries)
        score = len(chapter_entries) * 18 + numbered_count * 9
        score -= max(0, total_links - len(chapter_entries)) * 5
        score += min(node_depth(node), 8) * 3
        if has_word(attr_text, POSITIVE_CATALOG_WORDS):
            score += 140
        if has_word(attr_text, NEGATIVE_CONTAINER_WORDS) or node.tag in {"footer", "header", "nav", "aside"}:
            score -= 260
        if node.tag in {"document", "body"}:
            score -= 220
        scored.append((score, node, chapter_entries))

    if not scored:
        entries = extract_link_entries(root, base_url, final_url, book_title)
        return dedupe_links([entry for entry in entries if is_chapter_link(entry, allow_url_fallback=True)])

    scored.sort(key=lambda item: item[0], reverse=True)
    entries = scored[0][2]

    global_entries = extract_link_entries(root, base_url, final_url, book_title)
    scoped_strong_entries = [
        entry
        for entry in global_entries
        if is_chapter_title(entry.title) and chapter_url_belongs_to_book(toc_url, entry.url)
    ]
    if len(scoped_strong_entries) >= 3:
        entries = dedupe_links(entries + scoped_strong_entries)

    scoped = [entry for entry in entries if chapter_url_belongs_to_book(toc_url, entry.url)]
    if len(scoped) >= 3:
        entries = scoped

    numbered = [entry for entry in entries if entry.chapter_no is not None]
    if len(numbered) >= 8 and len(numbered) >= len(entries) * 0.55:
        entries = numbered

    entries = dedupe_links(entries)
    entries.sort(key=chapter_sort_key)
    return entries


def discover_sudugu_chapters_from_html(
    html_text: str,
    final_url: str,
    toc_url: str,
) -> tuple[str, list[dict[str, str]]] | None:
    if not is_sudugu_url(final_url):
        return None

    tree = parse_html_tree(html_text)
    heading = cleanup_page_title(find_first_heading(tree.root))
    page_title = cleanup_page_title("".join(tree.title_parts))
    book_title = heading or page_title or "未命名小说"
    base_url = urllib.parse.urljoin(final_url, tree.base_href or final_url)

    list_node = find_first_node(tree.root, lambda node: node_id_equals(node, "list"))
    if not list_node:
        return None

    entries = extract_link_entries(list_node, base_url, final_url, book_title)
    entries = [
        entry
        for entry in entries
        if chapter_url_belongs_to_book(toc_url, entry.url) and is_chapter_title(entry.title)
    ]

    global_entries = extract_link_entries(tree.root, base_url, final_url, book_title)
    latest_entries = [
        entry
        for entry in global_entries
        if chapter_url_belongs_to_book(toc_url, entry.url) and is_chapter_title(entry.title)
    ]
    entries = dedupe_links(entries + latest_entries)
    entries.sort(key=chapter_sort_key)

    chapters = [
        {"title": entry.title, "url": entry.url, "status": "pending", "content": ""}
        for entry in entries
    ]
    return (book_title, chapters) if chapters else None


def discover_biquge345_chapters_from_html(
    html_text: str,
    final_url: str,
    toc_url: str,
) -> tuple[str, list[dict[str, str]]] | None:
    if not is_biquge345_url(final_url):
        return None

    tree = parse_html_tree(html_text)
    page_title = cleanup_biquge345_title("".join(tree.title_parts))
    heading = cleanup_biquge345_title(find_first_heading(tree.root))
    book_title = page_title or heading or cleanup_page_title("".join(tree.title_parts)) or "未命名小说"
    base_url = urllib.parse.urljoin(final_url, tree.base_href or final_url)

    entries = extract_link_entries(tree.root, base_url, final_url, book_title)
    entries = [
        entry
        for entry in entries
        if biquge345_chapter_belongs_to_book(toc_url, entry.url)
        and (is_chapter_title(entry.title) or extract_chapter_number(entry.title) is not None)
    ]
    entries = dedupe_links(entries)
    entries.sort(key=chapter_sort_key)

    chapters = [
        {"title": entry.title, "url": entry.url, "status": "pending", "content": ""}
        for entry in entries
    ]
    return (book_title, chapters) if chapters else None


def discover_69shuba_read_chapters_from_html(
    html_text: str,
    final_url: str,
    start_url: str,
    read_chain_limit: int = DEFAULT_READ_CHAIN_LIMIT,
    progress_callback=None,
) -> tuple[str, list[dict[str, str]]] | None:
    if not is_69shuba_read_url(final_url):
        return None

    try:
        limit = int(read_chain_limit)
    except (TypeError, ValueError):
        limit = DEFAULT_READ_CHAIN_LIMIT
    limit = max(1, min(MAX_READ_CHAIN_LIMIT, limit))

    current_html = html_text
    current_url = final_url
    visited_urls: set[str] = set()
    chapters: list[dict[str, str]] = []
    book_title = ""

    for index in range(limit):
        normalized_url = strip_url_fragment(current_url)
        if normalized_url in visited_urls:
            break
        visited_urls.add(normalized_url)

        parser = parse_html_tree(current_html)
        if not book_title:
            book_title = cleanup_69shuba_book_title("".join(parser.title_parts)) or "未命名小说"

        fallback_title = f"第{index + 1}章"
        site_content = extract_69shuba_chapter_content(current_html, fallback_title)
        if site_content:
            chapter_title, content = site_content
        else:
            chapter_title, content = extract_chapter_content(current_html, fallback_title)

        chapters.append(
            {
                "title": cleanup_69shuba_chapter_title(chapter_title, fallback_title),
                "url": normalized_url,
                "status": "done",
                "content": content,
                "content_version": CONTENT_SCHEMA_VERSION,
                "page_count": 1,
                "page_urls": [normalized_url],
                "source_mode": "69shuba_read_chain",
            }
        )
        if progress_callback:
            progress_callback(len(chapters), limit, chapters[-1]["title"])

        if len(chapters) >= limit:
            break
        next_url = find_69shuba_next_chapter_url(current_html, current_url, start_url)
        if not next_url or strip_url_fragment(next_url) in visited_urls:
            break
        current_html, current_url = fetch_html(next_url)

    return (book_title or "未命名小说", chapters) if chapters else None


def discover_chapters_from_html(html_text: str, final_url: str, toc_url: str) -> tuple[str, list[dict[str, str]]]:
    site_result = discover_sudugu_chapters_from_html(html_text, final_url, toc_url)
    if not site_result:
        site_result = discover_biquge345_chapters_from_html(html_text, final_url, toc_url)
    if site_result:
        return site_result

    tree = parse_html_tree(html_text)
    page_title = cleanup_page_title("".join(tree.title_parts))
    heading = cleanup_page_title(find_first_heading(tree.root))
    book_title = heading or page_title or "未命名小说"
    base_url = urllib.parse.urljoin(final_url, tree.base_href or final_url)
    entries = choose_catalog_entries(tree.root, base_url, final_url, toc_url, book_title)

    chapters = [
        {"title": entry.title, "url": entry.url, "status": "pending", "content": ""}
        for entry in entries
        if entry.url.rstrip("/") != final_url.rstrip("/")
    ]
    if not chapters:
        raise ValueError("没有在目录页识别到章节链接，请确认输入的是小说目录页地址。")
    return book_title, chapters


def discover_chapters(
    toc_url: str,
    crawl_mode: str = CRAWL_MODE_CATALOG,
    read_chain_limit: int = DEFAULT_READ_CHAIN_LIMIT,
    progress_callback=None,
) -> tuple[str, list[dict[str, str]], str]:
    html_text, final_url = fetch_html(toc_url)
    if crawl_mode == CRAWL_MODE_READ_CHAIN:
        site_result = discover_69shuba_read_chapters_from_html(
            html_text,
            final_url,
            toc_url,
            read_chain_limit=read_chain_limit,
            progress_callback=progress_callback,
        )
        if not site_result:
            raise ValueError("当前阅读页连续模式暂只支持可识别“下一章”的阅读页，例如 69shuba 阅读页。")
        title, chapters = site_result
    else:
        title, chapters = discover_chapters_from_html(html_text, final_url, toc_url)
    return title, chapters, final_url


def should_skip_node(node: HtmlNode) -> bool:
    attr_text = node.attr_text()
    if node.tag in {"nav", "footer", "header", "form", "aside"}:
        return True
    if has_word(attr_text, NEGATIVE_CONTAINER_WORDS) and not has_word(attr_text, POSITIVE_CONTENT_WORDS):
        return True
    return False


def block_text(node: HtmlNode) -> str:
    parts: list[str] = []

    def walk(item: str | HtmlNode) -> None:
        if isinstance(item, str):
            parts.append(item)
            return
        if should_skip_node(item):
            return
        if item.tag in BLOCK_TAGS:
            parts.append("\n")
        for child in item.children:
            walk(child)
        if item.tag in BLOCK_TAGS:
            parts.append("\n")

    walk(node)
    text = html.unescape("".join(parts))
    text = re.sub(r"[ \t\r\f\v\u3000]+", " ", text)
    text = re.sub(r" *\n+ *", "\n", text)
    lines: list[str] = []
    previous = ""
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line == previous:
            continue
        if any(re.search(pattern, line, re.I) for pattern in NOISE_LINE_PATTERNS):
            continue
        if re.search(r".+[>＞»]\s*(第.+[章节卷集回部篇幕]|Chapter\s*\d+)", line, re.I):
            continue
        lines.append(line)
        previous = line
    return "\n\n".join(lines).strip()


def chapter_heading_line_count(text: str) -> int:
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    return len([line for line in lines if len(line) <= 90 and is_chapter_title(line)])


def looks_like_catalog_text(text: str) -> bool:
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    if len(lines) < 12:
        return False
    headings = chapter_heading_line_count(text)
    return headings >= 8 and headings / max(len(lines), 1) > 0.35


def content_node_score(node: HtmlNode) -> float:
    text = plain_text(node)
    length = len(text)
    if length < 120:
        return -1

    link_density = link_text_length(node) / max(length, 1)
    attr_text = node.attr_text()
    content = block_text(node)
    score = float(len(content))
    paragraph_count = len([line for line in content.splitlines() if len(line.strip()) >= 8])
    score += min(paragraph_count, 80) * 18

    if node.tag in {"article", "main"}:
        score += 500
    if has_word(attr_text, POSITIVE_CONTENT_WORDS):
        score += 900
    if has_word(attr_text, NEGATIVE_CONTAINER_WORDS) or node.tag in {"nav", "footer", "header", "aside"}:
        score -= 1600
    if link_density > 0.2:
        score -= link_density * 2800
    if looks_like_catalog_text(content):
        score -= 6000
    if node.tag in {"document", "html", "body"}:
        score -= 1500
    return score


def extract_chapter_content(html_text: str, fallback_title: str) -> tuple[str, str]:
    parser = parse_html_tree(html_text)
    title = clean_chapter_title(find_first_heading(parser.root) or fallback_title)

    candidates = [(content_node_score(node), node) for node in iter_nodes(parser.root)]
    candidates = [candidate for candidate in candidates if candidate[0] >= 0]
    candidates.sort(key=lambda item: item[0], reverse=True)

    content = ""
    for _score, node in candidates:
        candidate = block_text(node)
        if len(candidate) < 50:
            continue
        if looks_like_catalog_text(candidate):
            continue
        content = candidate
        break
    if not content:
        content = block_text(parser.root)

    lines = [line for line in content.splitlines() if normalize_space(line)]
    cleaned_lines: list[str] = []
    title_norms = {normalize_space(title), normalize_space(fallback_title)}
    for line in lines:
        normalized = normalize_space(line)
        if normalized in title_norms:
            continue
        if normalized.startswith("当前位置") or normalized.startswith("您的位置"):
            continue
        cleaned_lines.append(line)
    content = "\n".join(cleaned_lines).strip()

    if len(content) < 20:
        raise ValueError("未能从章节页面提取到正文。")
    if looks_like_catalog_text(content):
        raise ValueError("章节页面疑似提取到目录内容，已跳过以避免污染 TXT。")
    return title or fallback_title, content


def extract_sudugu_chapter_content(html_text: str, fallback_title: str) -> tuple[str, str] | None:
    parser = parse_html_tree(html_text)
    content_node = find_first_node(parser.root, lambda node: node_has_class(node, "con"))
    if not content_node:
        return None

    title_node = find_first_node(parser.root, lambda node: node_has_class(node, "submenu") and node.tag == "div")
    title = fallback_title
    if title_node:
        title = clean_chapter_title(plain_text(title_node), fallback_title)
    content = block_text(content_node)
    if len(content) < 20 or looks_like_catalog_text(content):
        return None
    return title or fallback_title, content


def extract_biquge345_raw_content_fragment(html_text: str) -> str:
    start_match = re.search(r"<div\b(?=[^>]*\bid=[\"']txt[\"'])[^>]*>", html_text, re.I)
    if not start_match:
        return ""

    tail = html_text[start_match.start() :]
    end_match = re.search(r"</div>\s*<div\b[^>]*class=[\"'][^\"']*\bbaocuo\b", tail, re.I)
    if end_match:
        return tail[: end_match.start() + len("</div>")]

    boundary_match = re.search(
        r"<div\b[^>]*(?:id=[\"']fanye1[\"']|class=[\"'][^\"']*\b(?:like|footer|baocuo)\b)",
        tail,
        re.I,
    )
    if boundary_match:
        return tail[: boundary_match.start()]
    return tail


def extract_biquge345_chapter_content(html_text: str, fallback_title: str) -> tuple[str, str] | None:
    parser = parse_html_tree(html_text)

    title_node = find_first_node(parser.root, lambda node: node.tag == "h1")
    title = clean_chapter_title(plain_text(title_node), fallback_title) if title_node else fallback_title

    raw_fragment = extract_biquge345_raw_content_fragment(html_text)
    if raw_fragment:
        content = block_text(parse_html_tree(raw_fragment).root)
    else:
        content_node = find_first_node(
            parser.root,
            lambda node: node_id_equals(node, "txt") or node_has_class(node, "txt"),
        )
        if not content_node:
            return None
        content = block_text(content_node)

    if len(content) < 20 or looks_like_catalog_text(content):
        return None
    return title or fallback_title, content


def cleanup_69shuba_book_title(title: str) -> str:
    title = normalize_space(title)
    if not title:
        return ""
    title = re.split(r"[_|]", title)[0]
    title = re.sub(r"[\(（][^\)）]{1,40}[\)）]\s*$", "", title)
    return normalize_space(title)[:90]


def cleanup_69shuba_chapter_title(title: str, fallback_title: str = "") -> str:
    title = clean_chapter_title(title or fallback_title)
    title = re.sub(r"[\(（]\s*\d+\s*/\s*\d+\s*[\)）]\s*$", "", title)
    return normalize_space(title or fallback_title)


def extract_69shuba_chapter_content(html_text: str, fallback_title: str) -> tuple[str, str] | None:
    parser = parse_html_tree(html_text)

    title_node = find_first_node(
        parser.root,
        lambda node: node_id_equals(node, "nr_title") or node_has_class(node, "nr_title") or node.tag == "h1",
    )
    title = cleanup_69shuba_chapter_title(plain_text(title_node), fallback_title) if title_node else fallback_title

    content_node = find_first_node(
        parser.root,
        lambda node: node_id_equals(node, "nr1")
        or (node_id_equals(node, "nr") and node_has_class(node, "nr_nr")),
    )
    if not content_node:
        return None
    content = block_text(content_node)
    if len(content) < 20 or looks_like_catalog_text(content):
        return None
    return title or fallback_title, content


def find_69shuba_next_chapter_url(html_text: str, current_url: str, start_url: str) -> str | None:
    parser = parse_html_tree(html_text)
    base_url = urllib.parse.urljoin(current_url, parser.base_href or current_url)

    for node in iter_nodes(parser.root):
        if node.tag != "a" or node.attrs.get("id") != "pb_next":
            continue
        href = node.attrs.get("href", "")
        if not href:
            continue
        url = strip_url_fragment(urllib.parse.urljoin(base_url, href))
        if shuba69_read_chapter_belongs_to_book(start_url, url):
            return url

    for text, url, _index in anchor_links(parser.root, base_url, current_url):
        if normalize_space(text) == "下一章" and shuba69_read_chapter_belongs_to_book(start_url, url):
            return url
    return None


def anchor_links(root: HtmlNode, base_url: str, final_url: str) -> list[tuple[str, str, int]]:
    links: list[tuple[str, str, int]] = []
    index = 0
    for node in iter_nodes(root):
        if node.tag != "a":
            continue
        href = node.attrs.get("href", "")
        if not href or href.startswith(("javascript:", "mailto:", "#")):
            continue
        absolute_url = strip_url_fragment(urllib.parse.urljoin(base_url, href))
        if not same_site(final_url, absolute_url):
            continue
        index += 1
        links.append((plain_text(node), absolute_url, index))
    return links


def page_number_from_url(url: str) -> int:
    parsed = urllib.parse.urlsplit(url)
    query = urllib.parse.parse_qs(parsed.query)
    for key in ("page", "p", "chapterpage", "chapter_page"):
        value = query.get(key)
        if value and value[0].isdigit():
            return int(value[0])

    path = parsed.path.rstrip("/")
    filename = path.rsplit("/", 1)[-1]
    stem = filename.rsplit(".", 1)[0]
    match = re.search(r"[-_](\d{1,3})$", stem)
    if match:
        return int(match.group(1))
    match = re.search(r"/(\d{1,3})/?$", parsed.path)
    if match and not re.search(r"\.html?$", parsed.path, re.I):
        return int(match.group(1))
    return 1


def chapter_page_key(url: str) -> str:
    parsed = urllib.parse.urlsplit(url)
    path = parsed.path.rstrip("/")
    directory, _, filename = path.rpartition("/")
    if "." in filename:
        stem, extension = filename.rsplit(".", 1)
        stem = re.sub(r"[-_]\d{1,3}$", "", stem)
        path_key = f"{directory}/{stem}.{extension.lower()}"
    else:
        parts = [part for part in path.split("/") if part]
        if len(parts) >= 2 and re.fullmatch(r"\d{1,3}", parts[-1]):
            parts = parts[:-1]
        path_key = "/" + "/".join(parts)

    query_pairs = urllib.parse.parse_qsl(parsed.query, keep_blank_values=True)
    query_pairs = [
        pair
        for pair in query_pairs
        if pair[0].lower() not in {"page", "p", "chapterpage", "chapter_page"}
    ]
    query = urllib.parse.urlencode(query_pairs)
    return urllib.parse.urlunsplit((parsed.scheme.lower(), parsed.netloc.lower(), path_key, query, ""))


def is_next_page_text(text: str) -> bool:
    text = normalize_space(text).lower()
    if not text:
        return False
    if any(word in text for word in ("下一章", "下章", "后一章", "下一节")):
        return False
    return any(word in text for word in ("下一页", "下页", "下一頁", "下頁", "next", "›", "»"))


def find_next_chapter_page_url(
    html_text: str,
    current_url: str,
    chapter_url: str,
    visited_urls: set[str],
) -> str | None:
    parser = parse_html_tree(html_text)
    base_url = urllib.parse.urljoin(current_url, parser.base_href or current_url)
    current_page_no = page_number_from_url(current_url)
    chapter_key = chapter_page_key(chapter_url)
    same_chapter_candidates: list[tuple[int, int, str]] = []

    if is_sudugu_url(current_url):
        prenext_node = find_first_node(parser.root, lambda node: node_has_class(node, "prenext"))
        if prenext_node:
            for text, url, _index in anchor_links(prenext_node, base_url, current_url):
                if url in visited_urls or url.rstrip("/") == current_url.rstrip("/"):
                    continue
                if is_next_page_text(text):
                    return url

    for text, url, index in anchor_links(parser.root, base_url, current_url):
        if url in visited_urls or url.rstrip("/") == current_url.rstrip("/"):
            continue
        normalized_text = normalize_space(text)
        if is_next_page_text(normalized_text):
            return url
        if chapter_page_key(url) == chapter_key:
            page_no = page_number_from_url(url)
            if page_no > current_page_no:
                same_chapter_candidates.append((page_no, index, url))

    if same_chapter_candidates:
        same_chapter_candidates.sort()
        return same_chapter_candidates[0][2]
    return None


def extract_full_chapter_content(chapter_url: str, fallback_title: str) -> tuple[str, str, list[str]]:
    title = fallback_title
    content_parts: list[str] = []
    page_urls: list[str] = []
    visited_urls: set[str] = set()
    current_url = chapter_url

    for _page_index in range(MAX_CHAPTER_PAGES):
        if current_url in visited_urls:
            break
        visited_urls.add(current_url)
        html_text, final_url = fetch_html(current_url)
        page_urls.append(final_url)

        site_content = None
        if is_sudugu_url(final_url):
            site_content = extract_sudugu_chapter_content(html_text, fallback_title)
        elif is_biquge345_url(final_url):
            site_content = extract_biquge345_chapter_content(html_text, fallback_title)
        elif is_69shuba_url(final_url):
            site_content = extract_69shuba_chapter_content(html_text, fallback_title)
        if site_content:
            page_title, page_content = site_content
        else:
            page_title, page_content = extract_chapter_content(html_text, fallback_title)
        if len(content_parts) == 0:
            title = page_title or fallback_title
        if page_content and page_content not in content_parts:
            content_parts.append(page_content)

        next_url = find_next_chapter_page_url(html_text, final_url, chapter_url, visited_urls)
        if not next_url:
            break
        current_url = next_url

    if not content_parts:
        raise ValueError("未能从章节页面提取到正文。")
    return title, "\n\n".join(content_parts).strip(), page_urls


def public_book_dict(book: dict) -> dict:
    return {key: value for key, value in book.items() if not key.startswith("_")}


def save_book_json(book: dict) -> Path:
    BOOKS_DIR.mkdir(parents=True, exist_ok=True)
    book_id = book.get("id") or book_id_for(book.get("source_url", ""))
    book["id"] = book_id
    path = BOOKS_DIR / f"{book_id}.json"
    path.write_text(json.dumps(public_book_dict(book), ensure_ascii=False, indent=2), encoding="utf-8")
    files = book.setdefault("_files", [])
    if str(path) not in files:
        files.append(str(path))
    return path


def load_saved_books() -> dict[str, dict]:
    BOOKS_DIR.mkdir(parents=True, exist_ok=True)
    loaded: dict[str, dict] = {}
    for path in BOOKS_DIR.glob("*.json"):
        try:
            book = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        source_url = book.get("source_url")
        if not source_url:
            continue
        stable_id = book_id_for(source_url)
        book["id"] = stable_id
        book.setdefault("title", "未命名小说")
        book.setdefault(
            "crawl_mode",
            CRAWL_MODE_READ_CHAIN if is_69shuba_read_url(str(source_url)) else CRAWL_MODE_CATALOG,
        )
        book.setdefault("read_chain_limit", DEFAULT_READ_CHAIN_LIMIT)
        book.setdefault("chapters", [])
        book["chapters"] = normalize_chapter_dicts(
            list(book.get("chapters", [])),
            str(book.get("source_url", "")),
            str(book.get("title", "")),
        )
        book.setdefault("updated_at", "")
        book["_files"] = [str(path)]
        existing = loaded.get(stable_id)
        if not existing or book.get("updated_at", "") >= existing.get("updated_at", ""):
            if existing:
                book["_files"].extend(existing.get("_files", []))
            loaded[stable_id] = book
        elif existing:
            existing.setdefault("_files", []).append(str(path))
    return loaded


def remove_book_files(book: dict) -> None:
    paths = {Path(value) for value in book.get("_files", [])}
    if book.get("id"):
        paths.add(BOOKS_DIR / f"{book['id']}.json")
    for path in paths:
        try:
            resolved = path.resolve()
            if BOOKS_DIR.resolve() in resolved.parents or resolved == BOOKS_DIR.resolve():
                path.unlink(missing_ok=True)
        except Exception:
            continue


def merge_existing_chapters(existing_book: dict | None, new_chapters: list[dict[str, str]]) -> list[dict[str, str]]:
    if not existing_book:
        return new_chapters
    old_by_url = {chapter.get("url"): chapter for chapter in existing_book.get("chapters", []) if chapter.get("url")}
    merged: list[dict[str, str]] = []
    for chapter in new_chapters:
        old = old_by_url.get(chapter.get("url"))
        if old and old.get("content"):
            chapter = dict(chapter)
            chapter["content"] = old.get("content", "")
            chapter["status"] = "cached"
        merged.append(chapter)
    return merged


def chapter_dict_number(chapter: dict) -> int | None:
    return extract_chapter_number(str(chapter.get("title", "")))


def chapter_dict_sort_key(index_and_chapter: tuple[int, dict]) -> tuple[int, int, int]:
    index, chapter = index_and_chapter
    number = chapter_dict_number(chapter)
    if number is None:
        return (1, index, 0)
    if number < 0:
        return (0, number, index)
    if number >= 900000:
        return (2, number, index)
    return (1, number, index)


def normalize_chapter_dicts(chapters: list[dict], source_url: str, book_title: str) -> list[dict]:
    normalized: list[dict] = []
    for chapter in chapters:
        copied = dict(chapter)
        copied["title"] = clean_chapter_title(str(copied.get("title", "未命名章节")), book_title)
        normalized.append(copied)

    scoped = [
        chapter
        for chapter in normalized
        if chapter.get("url") and chapter_url_belongs_to_book(source_url, str(chapter.get("url")))
    ]
    if len(scoped) >= 3:
        normalized = scoped

    numbered = [chapter for chapter in normalized if chapter_dict_number(chapter) is not None]
    if len(numbered) >= 8 and len(numbered) >= len(normalized) * 0.55:
        normalized = numbered

    return [chapter for _index, chapter in sorted(enumerate(normalized), key=chapter_dict_sort_key)]


def build_txt(book: dict) -> str:
    lines = [book.get("title") or "未命名小说", f"来源：{book.get('source_url', '')}", ""]
    wrote_any = False
    chapters = normalize_chapter_dicts(
        list(book.get("chapters", [])),
        str(book.get("source_url", "")),
        str(book.get("title", "")),
    )
    for chapter in chapters:
        if not chapter_has_usable_content(chapter):
            continue
        content = (chapter.get("content") or "").strip()
        title = normalize_space(chapter.get("title", "未命名章节"))
        lines.extend([title, "", content, ""])
        wrote_any = True
    return "\n".join(lines).replace("\r\n", "\n") if wrote_any else ""


def chapter_has_usable_content(chapter: dict) -> bool:
    content = (chapter.get("content") or "").strip()
    return (
        chapter.get("content_version") == CONTENT_SCHEMA_VERSION
        and bool(content)
        and not looks_like_catalog_text(content)
    )


def missing_content_chapters(book: dict) -> list[dict]:
    return [
        chapter
        for chapter in book.get("chapters", [])
        if not chapter_has_usable_content(chapter)
    ]


def sudugu_book_numeric_id(url: str) -> str | None:
    if not is_sudugu_url(url):
        return None
    match = re.search(r"/(\d+)/?", urllib.parse.urlparse(url).path)
    return match.group(1) if match else None


def normalize_txt_content(text: str) -> str:
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    text = re.sub(r"[ \t\u3000]+$", "", text, flags=re.M)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def split_txt_by_chapter_titles(txt_text: str, chapters: list[dict]) -> dict[str, str]:
    text = normalize_txt_content(txt_text)
    positions: list[tuple[int, int, str]] = []
    search_start = 0

    for chapter in chapters:
        title = normalize_space(str(chapter.get("title", "")))
        if not title:
            continue
        pattern = re.compile(rf"(?m)^\s*{re.escape(title)}\s*$")
        match = pattern.search(text, search_start)
        if not match:
            match = pattern.search(text)
        if match:
            positions.append((match.start(), match.end(), title))
            search_start = match.end()

    positions.sort(key=lambda item: item[0])
    result: dict[str, str] = {}
    for index, (_start, end, title) in enumerate(positions):
        next_start = positions[index + 1][0] if index + 1 < len(positions) else len(text)
        content = normalize_txt_content(text[end:next_start])
        if content:
            result[title] = content
    return result


def fill_sudugu_txt_contents(book: dict) -> int:
    book_id = sudugu_book_numeric_id(str(book.get("source_url", "")))
    chapters = book.get("chapters", [])
    if not book_id or not chapters:
        return 0

    page_count = max(1, math.ceil(len(chapters) / 500))
    txt_parts: list[str] = []
    txt_urls: list[str] = []
    scheme = urllib.parse.urlparse(str(book.get("source_url", ""))).scheme or "https"
    host = urllib.parse.urlparse(str(book.get("source_url", ""))).netloc or "www.sudugu.org"
    for page in range(1, page_count + 1):
        txt_url = f"{scheme}://{host}/txt/?id={book_id}&p={page}"
        text, final_url = fetch_text_file(txt_url)
        txt_parts.append(text)
        txt_urls.append(final_url)

    chapter_texts = split_txt_by_chapter_titles("\n\n".join(txt_parts), chapters)
    filled = 0
    for chapter in chapters:
        title = normalize_space(str(chapter.get("title", "")))
        content = chapter_texts.get(title)
        if not content:
            continue
        chapter["content"] = content
        chapter["status"] = "done"
        chapter["content_version"] = CONTENT_SCHEMA_VERSION
        chapter["page_count"] = 1
        chapter["page_urls"] = txt_urls
        chapter["source_mode"] = "sudugu_txt"
        chapter.pop("error", None)
        filled += 1
    return filled


class NovelScraperApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title(APP_NAME)
        self.root.configure(bg=COLORS["root"])
        self.root.option_add("*Font", UI_FONT)
        apply_app_icon(self.root)
        apply_initial_window_geometry(self.root)

        self.events: queue.Queue[tuple[str, dict]] = queue.Queue()
        self.worker: threading.Thread | None = None
        self.books: dict[str, dict] = load_saved_books()
        self.book_items: dict[str, str] = {}
        self.item_refs: dict[str, tuple] = {}
        self.chapter_items: dict[tuple[str, int], str] = {}
        self.pending_chapter_ui_events: dict[tuple[str, int], tuple[str, dict]] = {}
        self.pending_done_events: list[tuple[str, dict]] = []
        self.pending_status_text: str | None = None
        self.hover_chapter_key: tuple[str, int] | None = None
        self.retrying_chapters: set[tuple[str, int]] = set()
        self.content_render_job: str | None = None
        self.content_render_token = 0
        self.content_render_chunks: list[str] = []
        self.content_render_index = 0
        self.delete_pending: dict[str, float] = {}
        self.refreshed_on_open: set[str] = set()
        self.active_book_id: str | None = None
        self.pending_export_book_id: str | None = None
        self.concurrency_var = tk.StringVar(value=str(DEFAULT_CONCURRENCY))
        self.delay_var = tk.StringVar(value=str(REQUEST_DELAY_SECONDS))
        self.crawl_mode_var = tk.StringVar(value=CRAWL_MODE_LABELS[CRAWL_MODE_CATALOG])
        self.read_chain_limit_var = tk.StringVar(value=str(DEFAULT_READ_CHAIN_LIMIT))
        self.read_chain_hint_var = tk.StringVar(value="")

        self._configure_style()
        self._build_ui()
        enable_dark_title_bar(self.root)
        self._load_history_tree()
        self.root.after(100, self._process_events)

    def _configure_style(self) -> None:
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure(".", font=UI_FONT, background=COLORS["root"], foreground=COLORS["text"])
        style.configure("Root.TFrame", background=COLORS["root"])
        style.configure("Panel.TFrame", background=COLORS["panel"])
        style.configure("Toolbar.TFrame", background=COLORS["root"])
        style.configure("Title.TLabel", background=COLORS["panel"], foreground=COLORS["text_strong"], font=UI_FONT_BOLD)
        style.configure("Muted.TLabel", background=COLORS["root"], foreground=COLORS["muted"], font=UI_FONT)
        style.configure("Toolbar.TLabel", background=COLORS["root"], foreground=COLORS["muted"], font=UI_FONT)
        style.configure("Warning.TLabel", background=COLORS["root"], foreground=COLORS["warning"], font=UI_FONT)
        style.configure(
            "Dark.TEntry",
            fieldbackground=COLORS["surface"],
            foreground=COLORS["text"],
            bordercolor=COLORS["border"],
            lightcolor=COLORS["border"],
            darkcolor=COLORS["border"],
            insertcolor=COLORS["text"],
            padding=(8, 4),
        )
        style.configure(
            "TCombobox",
            fieldbackground=COLORS["surface"],
            background=COLORS["surface"],
            foreground=COLORS["text"],
            arrowcolor=COLORS["muted"],
            bordercolor=COLORS["border"],
            lightcolor=COLORS["border"],
            darkcolor=COLORS["border"],
            padding=(6, 3),
            font=UI_FONT,
        )
        style.map(
            "TCombobox",
            fieldbackground=[("readonly", COLORS["surface"])],
            foreground=[("readonly", COLORS["text"])],
            background=[("readonly", COLORS["surface"])],
        )
        style.configure(
            "Accent.TButton",
            background=COLORS["surface_hover"],
            foreground=COLORS["text"],
            bordercolor=COLORS["border"],
            focusthickness=0,
            padding=(12, 5),
            font=UI_FONT,
        )
        style.map(
            "Accent.TButton",
            background=[("active", "#333333"), ("disabled", COLORS["surface"])],
            foreground=[("disabled", COLORS["subtle"])],
        )
        style.configure(
            "Dark.TButton",
            background=COLORS["surface"],
            foreground=COLORS["text"],
            bordercolor=COLORS["border"],
            padding=(12, 5),
            font=UI_FONT,
        )
        style.map(
            "Dark.TButton",
            background=[("active", COLORS["surface_hover"]), ("disabled", COLORS["surface"])],
            foreground=[("disabled", COLORS["subtle"])],
        )
        style.configure(
            "Dark.Treeview",
            background=COLORS["panel"],
            fieldbackground=COLORS["panel"],
            foreground=COLORS["text"],
            bordercolor=COLORS["border"],
            lightcolor=COLORS["border"],
            darkcolor=COLORS["border"],
            rowheight=28,
            font=UI_FONT,
        )
        style.configure(
            "Dark.Treeview.Heading",
            background=COLORS["panel"],
            foreground=COLORS["muted"],
            relief="flat",
            bordercolor=COLORS["border"],
            font=UI_FONT,
        )
        style.map("Dark.Treeview", background=[("selected", COLORS["selection"])], foreground=[("selected", "#ffffff")])
        style.configure(
            "Dark.Vertical.TScrollbar",
            background=COLORS["surface"],
            troughcolor=COLORS["root"],
            bordercolor=COLORS["root"],
            arrowcolor=COLORS["muted"],
            relief="flat",
        )
        style.configure(
            "Dark.Horizontal.TProgressbar",
            troughcolor=COLORS["surface"],
            background=COLORS["selection"],
            bordercolor=COLORS["root"],
            lightcolor=COLORS["selection"],
            darkcolor=COLORS["selection"],
        )
        style.configure("Dark.TPanedwindow", background=COLORS["root"])

    def _build_ui(self) -> None:
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(3, weight=1)

        toolbar = ttk.Frame(self.root, padding=(10, 8), style="Toolbar.TFrame")
        toolbar.grid(row=0, column=0, sticky=E + W)
        toolbar.columnconfigure(1, weight=1)

        ttk.Label(toolbar, text="目录地址", style="Toolbar.TLabel").grid(row=0, column=0, sticky=W, padx=(0, 8))
        self.url_var = tk.StringVar()
        self.url_entry = ttk.Entry(toolbar, textvariable=self.url_var, style="Dark.TEntry")
        self.url_entry.grid(row=0, column=1, sticky=E + W, padx=(0, 8), ipady=2)
        self.url_entry.bind("<Return>", lambda _event: self.start_crawl_from_input())

        self.crawl_mode_combo = ttk.Combobox(
            toolbar,
            textvariable=self.crawl_mode_var,
            values=list(CRAWL_MODE_OPTIONS.keys()),
            width=10,
            state="readonly",
            font=UI_FONT,
        )
        self.crawl_mode_combo.grid(row=0, column=2, sticky=W, padx=(0, 8))
        self.crawl_mode_combo.bind("<<ComboboxSelected>>", lambda _event: self._sync_mode_controls())

        ttk.Label(toolbar, text="并发", style="Toolbar.TLabel").grid(row=0, column=3, sticky=W, padx=(0, 6))
        self.concurrency_spin = tk.Spinbox(
            toolbar,
            from_=1,
            to=MAX_CONCURRENCY,
            width=4,
            textvariable=self.concurrency_var,
            font=UI_FONT,
            bg=COLORS["surface"],
            fg=COLORS["text"],
            insertbackground=COLORS["text"],
            buttonbackground=COLORS["surface"],
            relief="flat",
            highlightthickness=1,
            highlightbackground=COLORS["border"],
            highlightcolor=COLORS["border_focus"],
        )
        self.concurrency_spin.grid(row=0, column=4, sticky=W, padx=(0, 8))

        ttk.Label(toolbar, text="间隔", style="Toolbar.TLabel").grid(row=0, column=5, sticky=W, padx=(0, 6))
        self.delay_entry = ttk.Entry(toolbar, textvariable=self.delay_var, width=6, style="Dark.TEntry")
        self.delay_entry.grid(row=0, column=6, sticky=W, padx=(0, 8), ipady=2)

        self.read_chain_limit_label = ttk.Label(toolbar, text="章数", style="Toolbar.TLabel")
        self.read_chain_limit_label.grid(row=0, column=7, sticky=W, padx=(0, 6))
        self.read_chain_limit_spin = tk.Spinbox(
            toolbar,
            from_=1,
            to=MAX_READ_CHAIN_LIMIT,
            width=5,
            textvariable=self.read_chain_limit_var,
            command=self._update_read_chain_hint,
            font=UI_FONT,
            bg=COLORS["surface"],
            fg=COLORS["text"],
            disabledbackground=COLORS["surface"],
            disabledforeground=COLORS["subtle"],
            insertbackground=COLORS["text"],
            buttonbackground=COLORS["surface"],
            relief="flat",
            highlightthickness=1,
            highlightbackground=COLORS["border"],
            highlightcolor=COLORS["border_focus"],
        )
        self.read_chain_limit_spin.grid(row=0, column=8, sticky=W, padx=(0, 8))
        self.read_chain_limit_var.trace_add("write", lambda *_args: self._update_read_chain_hint())

        self.start_button = ttk.Button(toolbar, text="开始爬取", style="Accent.TButton", command=self.start_crawl_from_input)
        self.start_button.grid(row=0, column=9, padx=(0, 6))

        self.export_button = ttk.Button(toolbar, text="保存TXT", style="Dark.TButton", command=self.export_txt)
        self.export_button.grid(row=0, column=10)

        hint_row = ttk.Frame(self.root, padding=(10, 0, 10, 2), style="Root.TFrame")
        hint_row.grid(row=1, column=0, sticky=E + W)
        hint_row.columnconfigure(0, weight=1)
        self.read_chain_hint_label = ttk.Label(
            hint_row,
            textvariable=self.read_chain_hint_var,
            style="Warning.TLabel",
        )
        self.read_chain_hint_label.grid(row=0, column=0, sticky=W)
        self._sync_mode_controls()

        status_row = ttk.Frame(self.root, padding=(10, 0, 10, 6), style="Root.TFrame")
        status_row.grid(row=2, column=0, sticky=E + W)
        status_row.columnconfigure(0, weight=1)
        self.status_var = tk.StringVar(value="输入小说目录页地址开始爬取；历史小说会保留在左侧书架。")
        ttk.Label(status_row, textvariable=self.status_var, style="Muted.TLabel").grid(row=0, column=0, sticky=W)
        self.progress = ttk.Progressbar(status_row, mode="determinate", maximum=100, style="Dark.Horizontal.TProgressbar")
        self.progress.grid(row=0, column=1, sticky=E, padx=(10, 0))

        main = ttk.Panedwindow(self.root, orient=tk.HORIZONTAL, style="Dark.TPanedwindow")
        main.grid(row=3, column=0, sticky=N + S + E + W, padx=0, pady=0)

        sidebar = ttk.Frame(main, padding=(10, 8), style="Panel.TFrame")
        sidebar.columnconfigure(0, weight=1)
        sidebar.rowconfigure(1, weight=1)
        ttk.Label(sidebar, text="书架目录", style="Title.TLabel").grid(row=0, column=0, sticky=W)

        tree_frame = ttk.Frame(sidebar, style="Panel.TFrame")
        tree_frame.grid(row=1, column=0, sticky=N + S + E + W, pady=(6, 0))
        tree_frame.columnconfigure(0, weight=1)
        tree_frame.rowconfigure(0, weight=1)
        self.library_tree = ttk.Treeview(
            tree_frame,
            columns=("status", "action"),
            show="tree headings",
            style="Dark.Treeview",
            selectmode="browse",
        )
        self.library_tree.heading("#0", text="小说 / 章节")
        self.library_tree.heading("status", text="状态")
        self.library_tree.heading("action", text="")
        self.library_tree.column("#0", width=350, minwidth=240, stretch=True)
        self.library_tree.column("status", width=86, minwidth=78, anchor="center", stretch=False)
        self.library_tree.column("action", width=30, minwidth=26, anchor="center", stretch=False)
        self.library_tree.grid(row=0, column=0, sticky=N + S + E + W)
        tree_scroll = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.library_tree.yview, style="Dark.Vertical.TScrollbar")
        tree_scroll.grid(row=0, column=1, sticky=N + S)
        self.library_tree.configure(yscrollcommand=tree_scroll.set)
        self.library_tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.library_tree.bind("<<TreeviewOpen>>", self.on_tree_open)
        self.library_tree.bind("<Button-1>", self.on_tree_click)
        self.library_tree.bind("<Motion>", self.on_tree_motion)
        self.library_tree.bind("<Leave>", self.on_tree_leave)
        self.library_tree.tag_configure("book", foreground=COLORS["text_strong"], font=UI_FONT_BOLD)
        self.library_tree.tag_configure("chapter_done", foreground=COLORS["text"])
        self.library_tree.tag_configure("chapter_cached", foreground=COLORS["muted"])
        self.library_tree.tag_configure("chapter_pending", foreground=COLORS["subtle"])
        self.library_tree.tag_configure("chapter_fetching", foreground=COLORS["accent"])
        self.library_tree.tag_configure("chapter_error", foreground=COLORS["danger"])
        self.library_tree.tag_configure("delete_pending", foreground=COLORS["danger"], font=UI_FONT_BOLD)

        reader = ttk.Frame(main, padding=(10, 8), style="Panel.TFrame")
        reader.columnconfigure(0, weight=1)
        reader.rowconfigure(1, weight=1)
        self.reader_title = tk.StringVar(value="正文")
        ttk.Label(reader, textvariable=self.reader_title, style="Title.TLabel").grid(row=0, column=0, sticky=W)

        text_frame = ttk.Frame(reader, style="Panel.TFrame")
        text_frame.grid(row=1, column=0, sticky=N + S + E + W, pady=(6, 0))
        text_frame.columnconfigure(0, weight=1)
        text_frame.rowconfigure(0, weight=1)
        self.content_text = tk.Text(
            text_frame,
            wrap="word",
            padx=16,
            pady=12,
            font=UI_FONT,
            relief="flat",
            bg=COLORS["editor"],
            fg=COLORS["text"],
            insertbackground=COLORS["text"],
            selectbackground=COLORS["selection"],
            selectforeground="#ffffff",
            spacing1=2,
            spacing2=1,
            spacing3=5,
            borderwidth=0,
            highlightthickness=1,
            highlightbackground=COLORS["border"],
            highlightcolor=COLORS["border_focus"],
        )
        self.content_text.grid(row=0, column=0, sticky=N + S + E + W)
        content_scroll = ttk.Scrollbar(text_frame, orient=tk.VERTICAL, command=self.content_text.yview, style="Dark.Vertical.TScrollbar")
        content_scroll.grid(row=0, column=1, sticky=N + S)
        self.content_text.configure(yscrollcommand=content_scroll.set)
        self._set_content("输入小说目录页地址后开始爬取。\n\n左侧书架会保存历史记录；展开历史小说会按原目录地址重新爬取。")

        main.add(sidebar, weight=2)
        main.add(reader, weight=5)

    def _load_history_tree(self) -> None:
        for book in sorted(self.books.values(), key=lambda item: item.get("updated_at", ""), reverse=True):
            self._upsert_book_item(book, include_children=True, open_item=False)
        self._refresh_export_state()

    def start_crawl_from_input(self) -> None:
        url = self.url_var.get().strip()
        if not re.match(r"^https?://", url, re.I):
            messagebox.showwarning("地址不正确", "请输入以 http:// 或 https:// 开头的小说目录页或阅读页地址。")
            return
        crawl_mode = CRAWL_MODE_OPTIONS.get(self.crawl_mode_var.get(), CRAWL_MODE_CATALOG)
        read_chain_limit = self._current_read_chain_limit() if crawl_mode == CRAWL_MODE_READ_CHAIN else DEFAULT_READ_CHAIN_LIMIT
        if crawl_mode == CRAWL_MODE_READ_CHAIN:
            confirmed = messagebox.askyesno(
                "确认本地保存",
                f"将从当前阅读页开始，顺着“下一章”最多读取 {read_chain_limit} 章，"
                "并保存到本机缓存；之后可由你导出 TXT。\n\n"
                "请确认你有权保存这些内容，且该操作符合网站规则和你的个人使用范围。",
            )
            if not confirmed:
                self.status_var.set("已取消。")
                return
        self.start_crawl(url, manual=True, crawl_mode=crawl_mode, read_chain_limit=read_chain_limit)

    def _current_concurrency(self) -> int:
        try:
            value = int(self.concurrency_var.get())
        except ValueError:
            value = DEFAULT_CONCURRENCY
        value = max(1, min(MAX_CONCURRENCY, value))
        self.concurrency_var.set(str(value))
        return value

    def _current_request_delay(self) -> float:
        try:
            value = float(self.delay_var.get())
        except ValueError:
            value = REQUEST_DELAY_SECONDS
        value = max(0.0, min(3.0, value))
        self.delay_var.set(f"{value:g}")
        return value

    def _current_read_chain_limit(self) -> int:
        try:
            value = int(self.read_chain_limit_var.get())
        except ValueError:
            value = DEFAULT_READ_CHAIN_LIMIT
        value = max(1, min(MAX_READ_CHAIN_LIMIT, value))
        self.read_chain_limit_var.set(str(value))
        return value

    def _sync_mode_controls(self) -> None:
        crawl_mode = CRAWL_MODE_OPTIONS.get(self.crawl_mode_var.get(), CRAWL_MODE_CATALOG)
        state = "normal" if crawl_mode == CRAWL_MODE_READ_CHAIN else "disabled"
        self.read_chain_limit_spin.configure(state=state)
        self._update_read_chain_hint()

    def _update_read_chain_hint(self) -> None:
        crawl_mode = CRAWL_MODE_OPTIONS.get(self.crawl_mode_var.get(), CRAWL_MODE_CATALOG)
        if crawl_mode != CRAWL_MODE_READ_CHAIN:
            self.read_chain_hint_var.set("")
            return
        raw_value = self.read_chain_limit_var.get().strip() or str(DEFAULT_READ_CHAIN_LIMIT)
        self.read_chain_hint_var.set(
            f"提示：阅读页连续模式会从当前章节开始顺着“下一章”爬取，达到设定章数 {raw_value} 章后停止；开始前请确认章数是否足够。"
        )

    def start_crawl(
        self,
        url: str,
        manual: bool = False,
        book_id: str | None = None,
        crawl_mode: str | None = None,
        read_chain_limit: int | None = None,
    ) -> None:
        if self.worker and self.worker.is_alive():
            self.status_var.set("已有爬取任务正在进行，请等待当前任务完成。")
            return
        self.progress.configure(value=0)
        self.start_button.configure(state="disabled")
        if manual:
            self.status_var.set("正在读取页面……")
            self._set_content("正在读取页面，请稍候……")
        concurrency = self._current_concurrency()
        request_delay = self._current_request_delay()
        crawl_mode = crawl_mode or CRAWL_MODE_OPTIONS.get(self.crawl_mode_var.get(), CRAWL_MODE_CATALOG)
        read_chain_limit = read_chain_limit or self._current_read_chain_limit()
        self.worker = threading.Thread(
            target=self._crawl_worker,
            args=(url, book_id, concurrency, request_delay, crawl_mode, read_chain_limit),
            daemon=True,
        )
        self.worker.start()

    def _crawl_worker(
        self,
        url: str,
        preferred_book_id: str | None,
        concurrency: int,
        request_delay: float,
        crawl_mode: str,
        read_chain_limit: int,
    ) -> None:
        try:
            self._post("status", text="正在分析页面……")

            def discovery_progress(count: int, limit: int, chapter_title: str) -> None:
                self._post("status", text=f"正在顺着下一章收集 {count}/{limit}：{chapter_title}")

            title, chapters, final_url = discover_chapters(
                url,
                crawl_mode=crawl_mode,
                read_chain_limit=read_chain_limit,
                progress_callback=discovery_progress,
            )
            source_url = url
            stable_id = preferred_book_id or book_id_for(source_url)
            existing = self.books.get(stable_id)
            chapters = merge_existing_chapters(existing, chapters)
            book = {
                "id": stable_id,
                "title": title,
                "source_url": source_url,
                "final_url": final_url,
                "created_at": existing.get("created_at") if existing else now_iso(),
                "updated_at": now_iso(),
                "completed": False,
                "crawl_mode": crawl_mode,
                "read_chain_limit": read_chain_limit if crawl_mode == CRAWL_MODE_READ_CHAIN else None,
                "chapters": chapters,
            }
            if existing and existing.get("_files"):
                book["_files"] = existing["_files"]
            save_book_json(book)
            self._post("book", book=book)

            if is_sudugu_url(source_url):
                try:
                    self._post("status", text="正在尝试 sudugu TXT 快速通道……")
                    filled = fill_sudugu_txt_contents(book)
                    book["updated_at"] = now_iso()
                    save_book_json(book)
                    if filled >= max(1, int(len(chapters) * 0.95)):
                        for index, chapter in enumerate(chapters):
                            self._post(
                                "chapter",
                                book_id=stable_id,
                                index=index,
                                chapter=chapter,
                                completed=index + 1,
                                total=len(chapters),
                            )
                        book["completed"] = True
                        book["updated_at"] = now_iso()
                        save_book_json(book)
                        self._post("done", book=book)
                        return
                    if filled:
                        self._post("status", text=f"TXT 快速通道补到 {filled} 章，继续并发补缺。")
                except Exception as exc:
                    self._post("status", text=f"TXT 快速通道不可用，改用并发分页：{exc}")

            total = len(chapters)

            def fetch_chapter_task(index: int, source_chapter: dict) -> tuple[int, dict]:
                chapter = dict(source_chapter)
                if chapter_has_usable_content(chapter):
                    chapter["status"] = "cached"
                    return index, chapter

                try:
                    title_text, content, page_urls = extract_full_chapter_content(chapter["url"], chapter["title"])
                    chapter["title"] = clean_chapter_title(title_text or chapter["title"], title)
                    chapter["content"] = content
                    chapter["page_count"] = len(page_urls)
                    chapter["page_urls"] = page_urls
                    chapter["content_version"] = CONTENT_SCHEMA_VERSION
                    chapter["status"] = "done"
                    chapter.pop("error", None)
                except Exception as exc:
                    chapter["status"] = "error"
                    chapter["error"] = str(exc)
                if request_delay:
                    time.sleep(request_delay)
                return index, chapter

            completed_count = 0
            with ThreadPoolExecutor(max_workers=concurrency) as executor:
                futures = [
                    executor.submit(fetch_chapter_task, index, chapter)
                    for index, chapter in enumerate(chapters)
                ]
                for future in as_completed(futures):
                    index, chapter = future.result()
                    chapters[index] = chapter
                    completed_count += 1
                    book["updated_at"] = now_iso()
                    self._post(
                        "chapter",
                        book_id=stable_id,
                        index=index,
                        chapter=chapter,
                        completed=completed_count,
                        total=total,
                    )
                    if completed_count % SAVE_EVERY_COMPLETED_CHAPTERS == 0:
                        save_book_json(book)

            book["completed"] = all(chapter.get("status") in {"done", "cached", "error"} for chapter in chapters)
            book["updated_at"] = now_iso()
            save_book_json(book)
            self._post("done", book=book)
        except Exception as exc:
            self._post("error", text=str(exc))

    def _post(self, kind: str, **payload: object) -> None:
        self.events.put((kind, payload))

    def _process_events(self) -> None:
        drained = 0
        immediate_events: list[tuple[str, dict]] = []
        try:
            while drained < EVENT_DRAIN_LIMIT:
                kind, payload = self.events.get_nowait()
                drained += 1
                if kind == "status":
                    self.pending_status_text = str(payload.get("text", ""))
                elif kind in {"chapter_status", "chapter"}:
                    key = (str(payload["book_id"]), int(payload["index"]))
                    self.pending_chapter_ui_events[key] = (kind, payload)
                else:
                    immediate_events.append((kind, payload))
        except queue.Empty:
            pass

        for kind, payload in immediate_events:
            if kind == "done" and self.pending_chapter_ui_events:
                self.pending_done_events.append((kind, payload))
                continue
            self._handle_event(kind, payload)

        if self.pending_status_text is not None:
            self.status_var.set(self.pending_status_text)
            self.pending_status_text = None

        applied = 0
        for key in list(self.pending_chapter_ui_events.keys())[:CHAPTER_UI_UPDATES_PER_TICK]:
            kind, payload = self.pending_chapter_ui_events.pop(key)
            self._handle_event(kind, payload)
            applied += 1

        if not self.pending_chapter_ui_events and self.pending_done_events:
            done_events = self.pending_done_events
            self.pending_done_events = []
            for kind, payload in done_events:
                self._handle_event(kind, payload)

        has_more = (
            drained >= EVENT_DRAIN_LIMIT
            or bool(self.pending_chapter_ui_events)
            or bool(self.pending_done_events)
            or not self.events.empty()
        )
        delay = EVENT_BUSY_DELAY_MS if has_more or applied else EVENT_IDLE_DELAY_MS
        self.root.after(delay, self._process_events)

    def _handle_event(self, kind: str, payload: dict) -> None:
        if kind == "status":
            self.status_var.set(str(payload.get("text", "")))
            return
        if kind == "book":
            book = payload["book"]
            self.books[book["id"]] = book
            self.active_book_id = book["id"]
            self._upsert_book_item(book, include_children=True, open_item=True)
            self.status_var.set(f"识别到 {len(book.get('chapters', []))} 个章节，已加入书架。")
            self._refresh_export_state()
            return
        if kind == "chapter_status":
            book_id = str(payload["book_id"])
            book = self.books.get(book_id)
            if not book:
                return
            index = int(payload["index"])
            if index < len(book.get("chapters", [])):
                book["chapters"][index]["status"] = payload.get("status")
                self._refresh_chapter_item(book_id, index)
            self.status_var.set(str(payload.get("text", "")))
            return
        if kind == "chapter":
            book_id = str(payload["book_id"])
            book = self.books.get(book_id)
            if not book:
                return
            index = int(payload["index"])
            book["chapters"][index] = payload["chapter"]
            completed = int(payload["completed"])
            total = int(payload["total"])
            self.progress.configure(value=completed / max(total, 1) * 100)
            self.status_var.set(f"已完成 {completed}/{total}：{book['chapters'][index].get('title', '')}")
            self._refresh_chapter_item(book_id, index)
            selected = self.library_tree.selection()
            if selected and self.item_refs.get(selected[0]) == ("chapter", book_id, index):
                self._show_chapter(book_id, index)
            return
        if kind == "chapter_retry_done":
            book_id = str(payload["book_id"])
            index = int(payload["index"])
            book = self.books.get(book_id)
            if book and "chapter" in payload and index < len(book.get("chapters", [])):
                book["chapters"][index] = payload["chapter"]
            self.retrying_chapters.discard((book_id, index))
            self._refresh_chapter_item(book_id, index)
            if book:
                self._upsert_book_item(book, include_children=False, open_item=True)
            selected = self.library_tree.selection()
            if selected and self.item_refs.get(selected[0]) == ("chapter", book_id, index):
                self._show_chapter(book_id, index)
            chapter = book["chapters"][index] if book and index < len(book.get("chapters", [])) else {}
            if chapter.get("status") == "done":
                self.status_var.set(f"已重新爬取：{chapter.get('title', '')}")
            elif chapter.get("status") == "error":
                self.status_var.set(f"重新爬取失败：{chapter.get('title', '')}")
            return
        if kind == "done":
            book = payload["book"]
            self.books[book["id"]] = book
            self._upsert_book_item(book, include_children=True, open_item=True)
            self.start_button.configure(state="normal")
            self.progress.configure(value=100)
            self.status_var.set("爬取完成，可以保存 TXT。")
            self._refresh_export_state()
            if self.pending_export_book_id == book["id"]:
                self.pending_export_book_id = None
                self.export_button.configure(text="保存TXT")
                missing = missing_content_chapters(book)
                if missing:
                    messagebox.showwarning(
                        "仍有章节缺失",
                        f"仍有 {len(missing)} 个章节没有获取到正文，暂不自动保存。\n"
                        "可以查看左侧失败章节后重新爬取。",
                    )
                else:
                    self.root.after(120, lambda current_book=book: self._save_txt_dialog(current_book))
            return
        if kind == "error":
            self.start_button.configure(state="normal")
            self.pending_export_book_id = None
            self.export_button.configure(text="保存TXT")
            self.status_var.set("爬取失败。")
            messagebox.showerror("爬取失败", str(payload.get("text", "未知错误")))

    def _clear_chapter_item_refs(self, book_id: str) -> None:
        for key, item in list(self.chapter_items.items()):
            if key[0] == book_id:
                self.chapter_items.pop(key, None)
                self.item_refs.pop(item, None)

    def _upsert_book_item(self, book: dict, include_children: bool, open_item: bool) -> None:
        book_id = book["id"]
        status = self._book_status_text(book)
        action = "×"
        item_id = self.book_items.get(book_id)
        if item_id and self.library_tree.exists(item_id):
            self.library_tree.item(
                item_id,
                text=book.get("title", "未命名小说"),
                values=(status, action),
                tags=("book",),
                open=open_item,
            )
        else:
            item_id = self.library_tree.insert(
                "",
                END,
                text=book.get("title", "未命名小说"),
                values=(status, action),
                tags=("book",),
                open=open_item,
            )
            self.book_items[book_id] = item_id
        self.item_refs[item_id] = ("book", book_id)

        if include_children:
            chapters = book.get("chapters", [])
            children = self.library_tree.get_children(item_id)
            needs_rebuild = len(children) != len(chapters) or any(
                (book_id, index) not in self.chapter_items for index in range(len(chapters))
            )
            if needs_rebuild:
                for child in children:
                    self.item_refs.pop(child, None)
                    self.library_tree.delete(child)
                self._clear_chapter_item_refs(book_id)
                for index, chapter in enumerate(chapters):
                    self._insert_chapter_item(item_id, book_id, index, chapter)

    def _insert_chapter_item(self, parent_item: str, book_id: str, index: int, chapter: dict) -> None:
        status = chapter.get("status", "pending")
        if status in {"done", "cached"} and not chapter_has_usable_content(chapter):
            status = "pending"
        tag = {
            "done": "chapter_done",
            "cached": "chapter_cached",
            "fetching": "chapter_fetching",
            "error": "chapter_error",
        }.get(status, "chapter_pending")
        item = self.library_tree.insert(
            parent_item,
            END,
            text=self._chapter_tree_text(index, chapter),
            values=(self._chapter_status_text(chapter), self._chapter_action_text(book_id, index)),
            tags=(tag,),
        )
        self.item_refs[item] = ("chapter", book_id, index)
        self.chapter_items[(book_id, index)] = item

    def _refresh_chapter_item(self, book_id: str, index: int) -> None:
        book = self.books.get(book_id)
        parent_item = self.book_items.get(book_id)
        if not book or not parent_item or not self.library_tree.exists(parent_item):
            return
        if index >= len(book.get("chapters", [])):
            return
        item = self.chapter_items.get((book_id, index))
        if not item or not self.library_tree.exists(item):
            self._upsert_book_item(book, include_children=True, open_item=True)
            item = self.chapter_items.get((book_id, index))
        if not item or not self.library_tree.exists(item):
            return
        chapter = book["chapters"][index]
        status = chapter.get("status", "pending")
        if status in {"done", "cached"} and not chapter_has_usable_content(chapter):
            status = "pending"
        tag = {
            "done": "chapter_done",
            "cached": "chapter_cached",
            "fetching": "chapter_fetching",
            "error": "chapter_error",
        }.get(status, "chapter_pending")
        self.library_tree.item(
            item,
            text=self._chapter_tree_text(index, chapter),
            values=(self._chapter_status_text(chapter), self._chapter_action_text(book_id, index)),
            tags=(tag,),
        )
        self.library_tree.item(parent_item, values=(self._book_status_text(book), "×"))

    def _book_status_text(self, book: dict) -> str:
        chapters = book.get("chapters", [])
        if not chapters:
            return "未爬取"
        done = len([chapter for chapter in chapters if chapter_has_usable_content(chapter)])
        errors = len([chapter for chapter in chapters if chapter.get("status") == "error"])
        if errors:
            return f"{done}/{len(chapters)}，失败{errors}"
        return f"{done}/{len(chapters)}"

    def _chapter_status_text(self, chapter: dict) -> str:
        status = chapter.get("status", "pending")
        if status in {"done", "cached"} and not chapter_has_usable_content(chapter):
            return "待补齐"
        return {
            "pending": "待爬取",
            "cached": "已缓存",
            "fetching": "爬取中",
            "done": "完成",
            "error": "失败",
        }.get(status, "待爬取")

    def _chapter_action_text(self, book_id: str, index: int) -> str:
        key = (book_id, index)
        if key in self.retrying_chapters:
            return CHAPTER_RETRY_BUSY_ICON
        if self.hover_chapter_key == key:
            return CHAPTER_RETRY_ICON
        return ""

    def _chapter_tree_text(self, index: int, chapter: dict) -> str:
        return f"{index + 1:03d}  {chapter.get('title', '未命名章节')}"

    def _chapter_key_from_item(self, item: str) -> tuple[str, int] | None:
        ref = self.item_refs.get(item)
        if not ref or ref[0] != "chapter":
            return None
        return str(ref[1]), int(ref[2])

    def _set_hover_chapter_key(self, key: tuple[str, int] | None) -> None:
        if key == self.hover_chapter_key:
            return
        old_key = self.hover_chapter_key
        self.hover_chapter_key = key
        if old_key:
            self._refresh_chapter_item(*old_key)
        if key:
            self._refresh_chapter_item(*key)

    def on_tree_motion(self, event: tk.Event) -> None:
        item = self.library_tree.identify_row(event.y)
        self._set_hover_chapter_key(self._chapter_key_from_item(item) if item else None)

    def on_tree_leave(self, _event: tk.Event) -> None:
        self._set_hover_chapter_key(None)

    def on_tree_click(self, event: tk.Event) -> str | None:
        item = self.library_tree.identify_row(event.y)
        column = self.library_tree.identify_column(event.x)
        if not item or column != "#2":
            return None
        ref = self.item_refs.get(item)
        if not ref:
            return "break"
        if ref[0] == "book":
            book_id = ref[1]
            self._handle_delete_click(book_id)
        elif ref[0] == "chapter":
            _kind, book_id, index = ref
            self.retry_chapter(str(book_id), int(index))
        return "break"

    def _handle_delete_click(self, book_id: str) -> None:
        item = self.book_items.get(book_id)
        book = self.books.get(book_id)
        if not item or not book:
            return
        now = time.monotonic()
        last = self.delete_pending.get(book_id)
        if last and now - last <= DELETE_CONFIRM_SECONDS:
            remove_book_files(book)
            self.library_tree.delete(item)
            self.books.pop(book_id, None)
            self.book_items.pop(book_id, None)
            self._clear_chapter_item_refs(book_id)
            self.delete_pending.pop(book_id, None)
            if self.active_book_id == book_id:
                self.active_book_id = None
                self.reader_title.set("正文")
                self._set_content("已从书架清除。")
            self.status_var.set(f"已清除：{book.get('title', '未命名小说')}")
            self._refresh_export_state()
            return

        self.delete_pending[book_id] = now
        self.library_tree.item(item, values=("再次点击删除", "✖"), tags=("delete_pending",))
        self.status_var.set("短时间内再次点击红色叉号，将彻底清除这本小说的历史记录。")
        self.root.after(int(DELETE_CONFIRM_SECONDS * 1000), lambda: self._reset_delete_marker(book_id, now))

    def retry_chapter(self, book_id: str, index: int) -> None:
        book = self.books.get(book_id)
        if not book or index >= len(book.get("chapters", [])):
            return
        key = (book_id, index)
        if key in self.retrying_chapters:
            self.status_var.set("这一章正在重新爬取，请稍等。")
            return

        chapter = book["chapters"][index]
        chapter["status"] = "fetching"
        chapter.pop("error", None)
        self.retrying_chapters.add(key)
        self._refresh_chapter_item(book_id, index)
        self.status_var.set(f"正在重新爬取：{chapter.get('title', '')}")
        if self.item_refs.get(self.library_tree.focus()) == ("chapter", book_id, index):
            self._show_chapter(book_id, index)

        thread = threading.Thread(
            target=self._retry_chapter_worker,
            args=(book_id, index),
            daemon=True,
        )
        thread.start()

    def _retry_chapter_worker(self, book_id: str, index: int) -> None:
        book = self.books.get(book_id)
        if not book or index >= len(book.get("chapters", [])):
            self._post("chapter_retry_done", book_id=book_id, index=index)
            return

        chapter = dict(book["chapters"][index])
        book_title = str(book.get("title", ""))
        try:
            title_text, content, page_urls = extract_full_chapter_content(chapter["url"], chapter["title"])
            chapter["title"] = clean_chapter_title(title_text or chapter["title"], book_title)
            chapter["content"] = content
            chapter["page_count"] = len(page_urls)
            chapter["page_urls"] = page_urls
            chapter["content_version"] = CONTENT_SCHEMA_VERSION
            chapter["status"] = "done"
            chapter.pop("error", None)
        except Exception as exc:
            chapter["status"] = "error"
            chapter["error"] = str(exc)

        current_book = self.books.get(book_id)
        if current_book and index < len(current_book.get("chapters", [])):
            current_book["chapters"][index] = chapter
            current_book["updated_at"] = now_iso()
            save_book_json(current_book)

        self._post(
            "chapter_retry_done",
            book_id=book_id,
            index=index,
            chapter=chapter,
        )

    def _reset_delete_marker(self, book_id: str, marker_time: float) -> None:
        if self.delete_pending.get(book_id) != marker_time:
            return
        self.delete_pending.pop(book_id, None)
        book = self.books.get(book_id)
        item = self.book_items.get(book_id)
        if book and item and self.library_tree.exists(item):
            self.library_tree.item(item, values=(self._book_status_text(book), "×"), tags=("book",))

    def on_tree_open(self, _event: tk.Event) -> None:
        selected = self.library_tree.focus()
        ref = self.item_refs.get(selected)
        if not ref or ref[0] != "book":
            return
        book_id = ref[1]
        book = self.books.get(book_id)
        if not book:
            return
        self.active_book_id = book_id
        self.url_var.set(book.get("source_url", ""))
        self.crawl_mode_var.set(CRAWL_MODE_LABELS.get(book.get("crawl_mode"), CRAWL_MODE_LABELS[CRAWL_MODE_CATALOG]))
        self.read_chain_limit_var.set(str(book.get("read_chain_limit") or DEFAULT_READ_CHAIN_LIMIT))
        self._sync_mode_controls()
        if book_id not in self.refreshed_on_open:
            self.refreshed_on_open.add(book_id)
            self.status_var.set(f"正在按历史地址刷新：{book.get('title', '')}")
            self.start_crawl(
                book.get("source_url", ""),
                manual=False,
                book_id=book_id,
                crawl_mode=book.get("crawl_mode", CRAWL_MODE_CATALOG),
                read_chain_limit=int(book.get("read_chain_limit") or DEFAULT_READ_CHAIN_LIMIT),
            )

    def on_tree_select(self, _event: tk.Event) -> None:
        selection = self.library_tree.selection()
        if not selection:
            return
        ref = self.item_refs.get(selection[0])
        if not ref:
            return
        if ref[0] == "book":
            book_id = ref[1]
            self.active_book_id = book_id
            book = self.books.get(book_id)
            if book:
                self.reader_title.set(book.get("title", "正文"))
                self.url_var.set(book.get("source_url", ""))
                self.crawl_mode_var.set(
                    CRAWL_MODE_LABELS.get(book.get("crawl_mode"), CRAWL_MODE_LABELS[CRAWL_MODE_CATALOG])
                )
                self.read_chain_limit_var.set(str(book.get("read_chain_limit") or DEFAULT_READ_CHAIN_LIMIT))
                self._sync_mode_controls()
                self._set_content(self._book_summary(book))
        elif ref[0] == "chapter":
            _kind, book_id, index = ref
            self.active_book_id = book_id
            self._show_chapter(book_id, index)
        self._refresh_export_state()

    def _book_summary(self, book: dict) -> str:
        chapters = book.get("chapters", [])
        done = len([chapter for chapter in chapters if chapter_has_usable_content(chapter)])
        mode = book.get("crawl_mode")
        mode_text = CRAWL_MODE_LABELS.get(mode, CRAWL_MODE_LABELS[CRAWL_MODE_CATALOG])
        limit_text = ""
        if mode == CRAWL_MODE_READ_CHAIN:
            limit_text = f"连续章数：{book.get('read_chain_limit') or DEFAULT_READ_CHAIN_LIMIT}\n"
        return (
            f"{book.get('title', '未命名小说')}\n\n"
            f"目录地址：{book.get('source_url', '')}\n"
            f"爬取模式：{mode_text}\n"
            f"{limit_text}"
            f"章节数量：{len(chapters)}\n"
            f"已获取正文：{done}\n"
            f"更新时间：{book.get('updated_at', '')}\n\n"
            "展开左侧小说名会按历史地址刷新目录和正文；点击章节可阅读。"
        )

    def _show_chapter(self, book_id: str, index: int) -> None:
        book = self.books.get(book_id)
        if not book or index >= len(book.get("chapters", [])):
            return
        chapter = book["chapters"][index]
        self.reader_title.set(chapter.get("title", "未命名章节"))
        if chapter.get("status") == "error":
            content = f"此章节爬取失败：\n\n{chapter.get('error', '')}\n\n{chapter.get('url', '')}"
        elif chapter_has_usable_content(chapter):
            content = chapter["content"]
        elif chapter.get("content"):
            content = "此章节是旧版单页缓存，可能缺少分页内容。\n\n请重新爬取或点击保存 TXT 后选择先补齐缺失章节。"
        elif chapter.get("status") == "fetching":
            content = "正在爬取这一章……"
        else:
            content = "这一章尚未爬取。展开小说名或重新开始爬取后会刷新正文。"
        self._set_content(content)

    def _cancel_content_render(self) -> None:
        self.content_render_token += 1
        if self.content_render_job:
            try:
                self.root.after_cancel(self.content_render_job)
            except tk.TclError:
                pass
        self.content_render_job = None
        self.content_render_chunks = []
        self.content_render_index = 0

    def _set_content(self, text: str) -> None:
        self._cancel_content_render()
        token = self.content_render_token
        self.content_text.configure(state="normal")
        self.content_text.delete("1.0", END)
        self.content_text.yview_moveto(0)
        if not text:
            self.content_text.configure(state="disabled")
            return

        self.content_render_chunks = [
            text[index : index + TEXT_RENDER_CHUNK_SIZE]
            for index in range(0, len(text), TEXT_RENDER_CHUNK_SIZE)
        ]
        self.content_render_index = 0
        self._insert_content_chunk(token)

    def _insert_content_chunk(self, token: int) -> None:
        if token != self.content_render_token:
            return
        if self.content_render_index >= len(self.content_render_chunks):
            self.content_text.configure(state="disabled")
            self.content_render_job = None
            self.content_render_chunks = []
            return

        self.content_text.insert(END, self.content_render_chunks[self.content_render_index])
        self.content_render_index += 1
        if self.content_render_index >= len(self.content_render_chunks):
            self.content_text.configure(state="disabled")
            self.content_render_job = None
            self.content_render_chunks = []
            return
        self.content_render_job = self.root.after(1, lambda current_token=token: self._insert_content_chunk(current_token))

    def _selected_book_for_export(self) -> dict | None:
        selection = self.library_tree.selection()
        if selection:
            ref = self.item_refs.get(selection[0])
            if ref:
                if ref[0] == "book":
                    return self.books.get(ref[1])
                if ref[0] == "chapter":
                    return self.books.get(ref[1])
        if self.active_book_id:
            return self.books.get(self.active_book_id)
        if self.books:
            return next(iter(self.books.values()))
        return None

    def _refresh_export_state(self) -> None:
        self.export_button.configure(state="normal" if self.books else "disabled")

    def export_txt(self) -> None:
        book = self._selected_book_for_export()
        if not book:
            messagebox.showinfo("没有内容", "请先爬取一本小说。")
            return
        missing = missing_content_chapters(book)
        if missing:
            if self.worker and self.worker.is_alive():
                self.pending_export_book_id = book["id"]
                self.export_button.configure(text="完成后保存")
                self.status_var.set(f"已登记保存请求：爬取完成后会保存 TXT，还缺 {len(missing)} 章。")
                messagebox.showinfo(
                    "正在爬取",
                    f"当前还有 {len(missing)} 个章节未获取正文。\n"
                    "我会等本次爬取完成后再保存，避免导出残缺 TXT。",
                )
                return

            should_continue = messagebox.askyesno(
                "章节未完整",
                f"当前还有 {len(missing)} 个章节未获取正文。\n\n"
                "是否先补齐缺失章节，再保存完整 TXT？",
            )
            if should_continue:
                self.pending_export_book_id = book["id"]
                self.export_button.configure(text="补齐后保存")
                self.status_var.set(f"开始补齐缺失章节：还缺 {len(missing)} 章。")
                self.start_crawl(
                    book.get("source_url", ""),
                    manual=False,
                    book_id=book["id"],
                    crawl_mode=book.get("crawl_mode", CRAWL_MODE_CATALOG),
                    read_chain_limit=int(book.get("read_chain_limit") or DEFAULT_READ_CHAIN_LIMIT),
                )
            return

        self._save_txt_dialog(book)

    def _save_txt_dialog(self, book: dict) -> None:
        txt_content = build_txt(book)
        if not txt_content.strip():
            messagebox.showwarning("没有正文", "目前还没有可导出的章节正文。")
            return

        default_name = f"{sanitize_filename(book.get('title', 'novel'))}.txt"
        path = filedialog.asksaveasfilename(
            title="保存 TXT",
            defaultextension=".txt",
            initialfile=default_name,
            filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")],
        )
        if not path:
            return
        Path(path).write_text(txt_content, encoding="utf-8-sig")
        self.status_var.set(f"TXT 已保存：{path}")
        messagebox.showinfo("保存完成", f"TXT 已保存到：\n{path}")


def main() -> None:
    enable_high_dpi_awareness()
    BOOKS_DIR.mkdir(parents=True, exist_ok=True)
    root = tk.Tk()
    NovelScraperApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
