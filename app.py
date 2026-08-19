# ══════════════════════════════════════════════════════════════
#  IPTV Pro Inspector — v5.9.2-patched (Final + Extra Subscription Enrichment)
#  (جميع الإصلاحات + دعم عدد الاتصالات + إصلاح ffmpeg + تمييز الرفض
#   + محاولات إضافية لاستخراج تاريخ الانتهاء وعدد الأجهزة)
# ══════════════════════════════════════════════════════════════
from flask import Flask, render_template, request, jsonify, redirect, Response, stream_with_context
import time, requests, urllib3, threading, re, json, random, uuid, socket, ssl, ipaddress, os
import queue as queuelib
import hashlib
from datetime import datetime, timezone
from urllib.parse import urlparse, quote, urlunparse, urljoin, parse_qs
from concurrent.futures import ThreadPoolExecutor, as_completed
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
app = Flask(__name__)

# ══════════════════════════════════════════════════════════════
#  API Key (اختياري)
# ══════════════════════════════════════════════════════════════
API_KEY = os.environ.get("API_KEY", "")

def require_api_key():
    """إذا تم تعيين API_KEY في البيئة، يجب تمريره كـ ?key= في الطلبات."""
    if API_KEY and request.args.get("key") != API_KEY:
        return jsonify({"error": "Invalid API key"}), 401
    return None

# ══════════════════════════════════════════════════════════════
#  Constants & Limits (الإصلاح 1: حدود الإدخال)
# ══════════════════════════════════════════════════════════════

MAX_TASKS = 500                     # حد أقصى لعدد المهام
MAX_INPUT_LINES = 200               # حد أقصى لعدد الأسطر المدخلة

HEADERS = {
    "User-Agent": "iMPlayer/Mobile (Android)",
    "Accept": "*/*",
    "Accept-Encoding": "gzip, deflate",
    "Connection": "keep-alive"
}

MAG_UA_POOL = [
    "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3",
    "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/538.1 (KHTML, like Gecko) MAG254 stbapp ver: 2 rev: 250 Safari/538.1",
    "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/534.34 (KHTML, like Gecko) MAG250 stbapp ver: 2 rev: 250 Safari/534.34",
]

# توليد SN وUID فريدين من عنوان MAC
def _get_mag_sn_uid(mac_address):
    mac_clean = mac_address.replace(":", "").replace("-", "").upper()
    sn = mac_clean[:12] if len(mac_clean) >= 12 else mac_clean.ljust(12, '0')
    uid = hashlib.sha256(mac_address.encode()).hexdigest()[:32].upper()
    return sn, uid

PORTAL_API_PATHS = [
    "/portal.php", "/server/load.php", "/stalker_portal/server/load.php",
    "/portal/server/load.php", "/c/portal.php", "/c/portal.2.php",
    "/load.php", "/c/load.php", "/stalker/server/load.php", "/mag/server/load.php",
]

# ══════════════════════════════════════════════════════════════
#  Global State
# ══════════════════════════════════════════════════════════════

_PATH_CACHE = {}
_DISC_LOCKS = {}
_PORTAL_SEM = {}
_GLOB_LOCK  = threading.Lock()
_JOBS       = {}
_JOBS_LOCK  = threading.Lock()

# ── إلغاء المهام (الإصلاح 2) ──
_CANCEL_FLAG = {}
_CANCEL_LOCK = threading.Lock()

class CancelException(Exception):
    """يُرفع عند طلب إلغاء المهمة."""
    pass

# ══════════════════════════════════════════════════════════════
#  v5.9 FIX 2 — bounded DNS resolution
# ══════════════════════════════════════════════════════════════

_DNS_CACHE     = {}
_DNS_LOCK      = threading.Lock()
_DNS_CACHE_TTL = 600

def _is_ip_literal(host):
    try:
        ipaddress.ip_address(host)
        return True
    except (ValueError, TypeError):
        return False

def _resolve_host_bounded(hostname, timeout=5):
    if _is_ip_literal(hostname):
        return hostname

    now = time.time()
    with _DNS_LOCK:
        cached = _DNS_CACHE.get(hostname)
        if cached and (now - cached[1] < _DNS_CACHE_TTL):
            return cached[0]

    result_box = {}

    def _resolve():
        try:
            result_box["ip"] = socket.gethostbyname(hostname)
        except Exception as e:
            result_box["exc"] = e

    t = threading.Thread(target=_resolve, daemon=True)
    t.start()
    t.join(timeout)

    if t.is_alive():
        raise socket.timeout(f"DNS resolution timed out for {hostname}")
    if "exc" in result_box:
        raise result_box["exc"]

    ip = result_box.get("ip")
    if ip is None:
        raise socket.gaierror(f"DNS resolution failed for {hostname}")

    with _DNS_LOCK:
        if len(_DNS_CACHE) > 1000:
            _DNS_CACHE.clear()
        _DNS_CACHE[hostname] = (ip, now)
    return ip

class _LockBusy(Exception):
    pass

_DISC_LOCK_TIMEOUT  = 30
_PORTAL_SEM_TIMEOUT = 600

class _BoundedGuard:
    __slots__ = ("_lock", "_timeout")
    def __init__(self, lock, timeout=_DISC_LOCK_TIMEOUT):
        self._lock = lock
        self._timeout = timeout
    def __enter__(self):
        if not self._lock.acquire(timeout=self._timeout):
            raise _LockBusy("timed out waiting for portal lock/semaphore")
        return self
    def __exit__(self, exc_type, exc, tb):
        self._lock.release()
        return False

# ══════════════════════════════════════════════════════════════
#  SAFE REQUEST WRAPPER
# ══════════════════════════════════════════════════════════════

def safe_request(session, url, timeout=5, headers=None, cookies=None,
                 verify=False, allow_redirects=False, stream=False,
                 method='GET', **kwargs):
    parsed = urlparse(url)
    hostname = parsed.hostname
    if not hostname:
        return session.request(method, url, timeout=timeout, headers=headers,
                               cookies=cookies, verify=verify,
                               allow_redirects=allow_redirects, stream=stream, **kwargs)
    try:
        ip = _resolve_host_bounded(hostname, timeout=5)
    except Exception as dns_exc:
        raise requests.exceptions.ConnectionError(f"DNS resolution failed: {dns_exc}")

    req_headers = dict(headers) if headers else {}
    req_headers['Host'] = hostname

    if parsed.scheme == 'http':
        netloc = parsed.netloc
        if ':' in netloc:
            port = netloc.split(':')[-1]
            new_netloc = f"{ip}:{port}"
        else:
            new_netloc = ip
        new_parsed = parsed._replace(netloc=new_netloc)
        new_url = urlunparse(new_parsed)
        return session.request(method, new_url, timeout=timeout, headers=req_headers,
                               cookies=cookies, verify=verify,
                               allow_redirects=allow_redirects, stream=stream, **kwargs)
    else:
        return session.request(method, url, timeout=timeout, headers=req_headers,
                               cookies=cookies, verify=verify,
                               allow_redirects=allow_redirects, stream=stream, **kwargs)

# ══════════════════════════════════════════════════════════════
#  Semaphores / Locks
# ══════════════════════════════════════════════════════════════

def _get_portal_sem(portal_url):
    with _GLOB_LOCK:
        if portal_url not in _PORTAL_SEM:
            _PORTAL_SEM[portal_url] = threading.Semaphore(3)
        return _PORTAL_SEM[portal_url]

def _get_disc_lock(portal_url):
    with _GLOB_LOCK:
        if portal_url not in _DISC_LOCKS:
            _DISC_LOCKS[portal_url] = threading.Lock()
        return _DISC_LOCKS[portal_url]

# ══════════════════════════════════════════════════════════════
#  Job Cleanup
# ══════════════════════════════════════════════════════════════

def _cleanup_old_jobs():
    cutoff = time.time() - 600
    with _JOBS_LOCK:
        stale = [jid for jid, j in _JOBS.items() if j.get("ts", 0) < cutoff]
        for jid in stale:
            _JOBS.pop(jid, None)

# ══════════════════════════════════════════════════════════════
#  v5.9 FIX 7 — unified cache cleanup
# ══════════════════════════════════════════════════════════════

def _cleanup_caches():
    now = time.time()
    with _GLOB_LOCK:
        try:
            stale = [k for k, v in _BRIDGE_LINKS.items() if now - v[1] > 1800]
            for k in stale:
                _BRIDGE_LINKS.pop(k, None)
        except Exception:
            pass
        try:
            stale = [k for k, v in _BRIDGE_AUTH.items() if now - v.get("ts", 0) > 3600]
            for k in stale:
                _BRIDGE_AUTH.pop(k, None)
            while len(_BRIDGE_AUTH) > 50:
                oldest_key = min(_BRIDGE_AUTH, key=lambda k: _BRIDGE_AUTH[k].get("ts", 0))
                _BRIDGE_AUTH.pop(oldest_key, None)
        except Exception:
            pass
        try:
            stale = [k for k, v in _BRIDGE_LIST.items() if now - v.get("ts", 0) > 3600]
            for k in stale:
                _BRIDGE_LIST.pop(k, None)
            while len(_BRIDGE_LIST) > 50:
                oldest_key = min(_BRIDGE_LIST, key=lambda k: _BRIDGE_LIST[k].get("ts", 0))
                _BRIDGE_LIST.pop(oldest_key, None)
        except Exception:
            pass
        try:
            while len(_DISC_LOCKS) > 200:
                first_key = next(iter(_DISC_LOCKS))
                _DISC_LOCKS.pop(first_key, None)
        except Exception:
            pass
        try:
            while len(_PORTAL_SEM) > 200:
                first_key = next(iter(_PORTAL_SEM))
                _PORTAL_SEM.pop(first_key, None)
        except Exception:
            pass
        # ── الإصلاح 7: تنظيف _PATH_CACHE ──
        try:
            stale = []
            for k, v in _PATH_CACHE.items():
                if v is None:
                    stale.append(k)
                elif now - v > 1800:
                    stale.append(k)
            for k in stale:
                _PATH_CACHE.pop(k, None)
            while len(_PATH_CACHE) > 200:
                _PATH_CACHE.pop(next(iter(_PATH_CACHE)), None)
        except Exception:
            pass
    try:
        with _BW_LOCK:
            stale = [k for k, v in _BW_CACHE.items() if now - v.get("ts", 0) > 3600]
            for k in stale:
                _BW_CACHE.pop(k, None)
            while len(_BW_CACHE) > 500:
                oldest_key = min(_BW_CACHE, key=lambda k: _BW_CACHE[k].get("ts", 0))
                _BW_CACHE.pop(oldest_key, None)
    except Exception:
        pass
    try:
        with _SSL_LOCK:
            while len(_SSL_CACHE) > 500:
                oldest_key = min(_SSL_CACHE, key=lambda k: _SSL_CACHE[k].get("ts", 0))
                _SSL_CACHE.pop(oldest_key, None)
    except Exception:
        pass
    try:
        with _GEO_LOCK:
            if len(_GEO_CACHE) > 500:
                excess = len(_GEO_CACHE) - 500
                keys_to_drop = list(_GEO_CACHE.keys())[:excess]
                for k in keys_to_drop:
                    _GEO_CACHE.pop(k, None)
    except Exception:
        pass
    try:
        with _DNS_LOCK:
            if len(_DNS_CACHE) > 1000:
                _DNS_CACHE.clear()
    except Exception:
        pass

# ══════════════════════════════════════════════════════════════
#  Helpers (مع تحسين التواريخ والمهلات)
# ══════════════════════════════════════════════════════════════

def discover_api_path(session, portal_url, headers, cookies):
    for base in (f"{portal_url}/c/", f"{portal_url}/c", f"{portal_url}/"):
        try:
            r = safe_request(session, base, headers=headers, cookies=cookies,
                             timeout=5, verify=False, allow_redirects=True)
            if r.status_code != 200:
                continue
            m = re.search(r'["\']([^"\'\s]*(?:load\.php|portal\.2\.php|portal\.php))', r.text)
            if m:
                p = m.group(1)
                p = urlparse(p).path if p.startswith("http") else p
                if p.startswith("./"):
                    p = p[2:]
                if not p.startswith("/"):
                    p = "/" + p
                return p
        except Exception:
            continue
    return None

def format_timestamp(ts):
    try:
        if not ts or str(ts).strip() in ["", "0", "None", "null"]:
            return "Unlimited"
        return datetime.fromtimestamp(int(ts), tz=timezone.utc).strftime("%Y-%m-%d")
    except Exception:
        return str(ts)

def pretty_date(v):
    if not v:
        return None
    s = str(v).strip()
    if s in ("", "0", "None", "null"):
        return None
    try:
        ts = int(s)
        if 1_000_000_000 <= ts <= 4_000_000_000:
            return datetime.fromtimestamp(ts, tz=timezone.utc).strftime("%Y-%m-%d")
        if 1_000_000_000_000 <= ts <= 4_000_000_000_000:
            return datetime.fromtimestamp(ts / 1000, tz=timezone.utc).strftime("%Y-%m-%d")
    except (ValueError, TypeError, OverflowError):
        pass
    m = re.match(r'^(\d{4})[-/](\d{1,2})[-/](\d{1,2})', s)
    if m:
        return f"{m.group(1)}-{int(m.group(2)):02d}-{int(m.group(3)):02d}"
    m = re.match(r'^(\d{1,2})[-/](\d{1,2})[-/](\d{4})', s)
    if m:
        return f"{m.group(3)}-{int(m.group(2)):02d}-{int(m.group(1)):02d}"
    return None

def _pick(d, keys):
    if not isinstance(d, dict):
        return None
    for k in keys:
        v = d.get(k)
        if v not in (None, "", "None", "null"):
            return v
    return None

def _pick_date(d, keys):
    if not isinstance(d, dict):
        return None
    for k in keys:
        v = d.get(k)
        if v in (None, "", "None", "null"):
            continue
        parsed = pretty_date(v)
        if parsed:
            return parsed
    return None

def _scan_date_in_values(d):
    if not isinstance(d, dict):
        return None
    for v in d.values():
        if isinstance(v, str):
            m = re.search(r'(\d{4})[-/](\d{1,2})[-/](\d{1,2})', v)
            if m:
                return f"{m.group(1)}-{int(m.group(2)):02d}-{int(m.group(3)):02d}"
    return None

def _looks_blocked(obj):
    """يفحص القيم فقط بحثاً عن دليل حظر صريح، ويتجاهل أسماء المفاتيح الفارغة.
    تم توسيع نطاق الفحص ليشمل status وقيم أخرى."""
    if isinstance(obj, dict):
        for k, v in obj.items():
            kl = str(k).lower()
            if kl in ("blocked", "is_blocked", "block_reason", "restricted"):
                if str(v).strip() not in ("", "0", "None", "null",
                                          "False", "false", "[]", "{}"):
                    return True
            if kl == "status":
                if isinstance(v, str):
                    status_l = v.lower().strip()
                    if status_l in ("blocked", "disabled", "suspended",
                                    "expired", "inactive", "banned", "offline",
                                    "موقوف", "محظور", "معطل"):
                        return True
            if isinstance(v, str):
                s = v.lower()
                blocked_phrases = [
                    "your stb is blocked", "call the provider",
                    "stb blocked", "stb is blocked", "account blocked",
                    "account suspended", "account expired", "subscription expired",
                    "device banned", "محظور", "موقوف", "معطل", "ممنوع"
                ]
                if any(phrase in s for phrase in blocked_phrases):
                    return True
            if _looks_blocked(v):
                return True
    elif isinstance(obj, list):
        for v in obj:
            if _looks_blocked(v):
                return True
    elif isinstance(obj, str):
        s = obj.lower()
        blocked_phrases = [
            "your stb is blocked", "call the provider",
            "stb blocked", "stb is blocked", "account blocked",
            "account suspended", "account expired", "subscription expired",
            "device banned", "محظور", "موقوف", "معطل", "ممنوع"
        ]
        if any(phrase in s for phrase in blocked_phrases):
            return True
    return False

# ── الإصلاح 9: parse_m3u_line محسّنة ──
def parse_m3u_line(line):
    line = line.strip()
    parsed = urlparse(line)
    if parsed.scheme in ("http", "https"):
        qs = parse_qs(parsed.query)
        username = qs.get("username", [None])[0]
        password = qs.get("password", [None])[0]
        if username and password:
            base_url = f"{parsed.scheme}://{parsed.netloc}"
            return base_url, username, password
    return None

def normalize_portal_url(p):
    p = p.strip().lstrip('/')
    if not p.startswith(("http://", "https://")):
        p = "http://" + p
    p = p.rstrip('/')
    if p.endswith('/c'):
        p = p[:-2]
    return p.rstrip('/')

# ── الإصلاح 1 (المفقود): _normalize_stream_url ──
def _normalize_stream_url(raw_url, portal_url):
    if not raw_url:
        return None
    if raw_url.startswith(("http://", "https://", "rtmp://", "udp://", "rtsp://")):
        return raw_url
    parsed_portal = urlparse(portal_url)
    base = f"{parsed_portal.scheme}://{parsed_portal.netloc}"
    return urljoin(base, raw_url)

# ── الإصلاح 3: دالة تعقيم النتائج (إزالة كلمات المرور وروابط M3U) ──
def sanitize_result(res):
    res.pop("password", None)
    res.pop("m3u_url", None)
    return res

# ── الإصلاح 9: اختبار بث أوسع (10 قنوات بدل 3) ──
def _check_xtream_stream(session, server_url, username, password, stream_ids, job_id=None):
    hard_fail = False
    for sid in stream_ids[:10]:
        if job_id and is_cancelled(job_id):
            raise CancelException("Cancelled")
        for ext in (".m3u8", ".ts"):
            url = f"{server_url.rstrip('/')}/live/{username}/{password}/{sid}{ext}"
            try:
                r = safe_request(session, url, headers=HEADERS, timeout=8, verify=False, stream=True)
                status = r.status_code
                r.close()
                if status < 400:
                    return True
                if status >= 500:
                    time.sleep(0.3)
                    r2 = safe_request(session, url, headers=HEADERS, timeout=8, verify=False, stream=True)
                    status = r2.status_code
                    r2.close()
                    if status < 400:
                        return True
                if status != 404:
                    hard_fail = True
            except Exception:
                continue
    return False if hard_fail else None

# ══════════════════════════════════════════════════════════════
#  v5.9.2 FIX — اختبار بث MAC بهوية جلسة الـ STB الكاملة
#  (MAG UA + كوكيز mac + Bearer token) لأن خوادم البث تربط
#  الرابط بالجلسة وترفض أي هوية أخرى بـ 403
#  تم تعديل التعامل مع transcoder و ffmpeg + تمييز الرفض
# ══════════════════════════════════════════════════════════════
def _check_mac_stream(session, portal_url, api_path, headers, cookies, cmds, job_id=None, diag=None):
    explicit_blocked = False
    stb_headers = {k: v for k, v in (headers or {}).items()
                   if k.lower() not in ("accept-encoding", "connection")}
    sample_urls = []
    transcoder_mode = False

    def d(msg):
        if diag is not None and len(diag) < 20:
            diag.append(msg)

    def _try(url, tag):
        nonlocal explicit_blocked
        try:
            sr = session.request("GET", url, headers=stb_headers, cookies=cookies,
                                 timeout=10, verify=False, stream=True, allow_redirects=True)
            status = sr.status_code
            if status in (401, 403):
                explicit_blocked = True
            if status < 400:
                got = 0
                try:
                    for chunk in sr.iter_content(16 * 1024):
                        if not chunk:
                            break
                        got += len(chunk)
                        if got >= 32 * 1024:
                            break
                except Exception:
                    pass
            sr.close()
            return status
        except CancelException:
            raise
        except Exception as e:
            d(f"{tag}:{type(e).__name__}")
            return None

    def _prep(u):
        u = str(u or "").strip()
        if not u:
            return None
        # إصلاح أوامر ffmpeg: اقتطاع "ffmpeg" وأي مسافات بعدها
        if u.lower().startswith("ffmpeg"):
            u = re.sub(r'^ffmpeg\s+', '', u, flags=re.IGNORECASE).strip()
        # دعم ffrt://
        if u.startswith("ffrt://"):
            u = "http://" + u[len("ffrt://"):]
        return _normalize_stream_url(u, portal_url)

    def _extract_real_urls(cmd_str, portal_base):
        s = str(cmd_str or "")
        # إزالة أي كلمة ffmpeg في بداية النص حتى لا تتداخل مع الاستخراج
        s_clean = re.sub(r'^ffmpeg\s+', '', s, flags=re.IGNORECASE)
        urls = []
        # روابط http/https مباشرة
        for m in re.finditer(r'https?://[^\s\'"<>]+', s_clean):
            urls.append(m.group(0))
        # مسارات play/live
        for m in re.finditer(r'(/play/live\.(?:php|m3u8)[^\s\'"<>\)]*)', s_clean):
            urls.append(urljoin(portal_base + "/", m.group(1)))
        # مسارات PHP عامة
        for m in re.finditer(r'(/[A-Za-z0-9_/]+\.php\?[^\s\'"<>]+)', s_clean):
            urls.append(urljoin(portal_base + "/", m.group(1)))
        # إزالة التكرار مع الحفاظ على الترتيب
        seen = set()
        uniq = []
        for u in urls:
            if u not in seen:
                seen.add(u)
                uniq.append(u)
        return uniq

    def _is_transcoder_cmd(s):
        """اكتشاف أوامر ffmpeg/transcoder"""
        s_lower = str(s or "").lower()
        return any(kw in s_lower for kw in ["ffmpeg", "avconv", "transcode", "/play/live.php"])

    portal_base = portal_url.rstrip("/")

    for i, cmd in enumerate(cmds[:10]):
        if job_id and is_cancelled(job_id):
            raise CancelException("Cancelled")
        try:
            direct_url = _prep(cmd)
            if direct_url and len(sample_urls) < 3:
                sample_urls.append(("dir", direct_url[:150]))

            # اختبار الرابط المباشر
            s1 = None
            if direct_url and urlparse(direct_url).scheme in ("http", "https"):
                s1 = _try(direct_url, f"cl{i}:dir")
                if s1 is not None and s1 < 400:
                    return True

            # اختبار create_link
            params = {"type": "itv", "action": "create_link", "cmd": cmd,
                      "forced": "1", "JsHttpRequest": "1-xml"}
            r = safe_request(session, f"{portal_url}{api_path}", params=params,
                             headers=headers, cookies=cookies, timeout=5, verify=False)
            if r.status_code >= 500:
                time.sleep(0.3)
                r = safe_request(session, f"{portal_url}{api_path}", params=params,
                                 headers=headers, cookies=cookies, timeout=5, verify=False)
            if r.status_code != 200:
                if r.status_code in (401, 403):
                    explicit_blocked = True
                # لا نعتبر الأخطاء الأخرى فشلاً قاطعاً
                d(f"cl{i}:clHTTP{r.status_code}")
                continue
            js = (r.json() or {}).get("js", "") or {}
            raw_url = (js.get("url") or js.get("cmd")) if isinstance(js, dict) else str(js)
            link_url = _prep(raw_url)
            if link_url and len(sample_urls) < 3:
                sample_urls.append(("link", link_url[:150]))

            # استخراج الروابط الحقيقية من أوامر ffmpeg
            extracted = _extract_real_urls(raw_url, portal_base)
            for j, eu in enumerate(extracted[:3]):
                if job_id and is_cancelled(job_id):
                    raise CancelException("Cancelled")
                if len(sample_urls) < 6:
                    sample_urls.append((f"ext{j}", eu[:150]))
                s = _try(eu, f"cl{i}:ext{j}")
                if s is not None and s < 400:
                    d(f"cl{i}:ext{j}:OK")
                    return True
                # _try ستقوم بتحديث explicit_blocked تلقائياً

            # اكتشاف نمط ffmpeg/transcoder (بعد فشل الروابط المستخرجة)
            if _is_transcoder_cmd(raw_url) or _is_transcoder_cmd(cmd):
                transcoder_mode = True
                d(f"cl{i}:transcoder")
                continue

            s2 = None
            if link_url and urlparse(link_url).scheme in ("http", "https"):
                s2 = _try(link_url, f"cl{i}:link")
                if s2 is not None and s2 < 400:
                    return True
                # _try ستقوم بتحديث explicit_blocked تلقائياً
            d(f"cl{i}:dir:{s1},link:{s2},ext:{len(extracted)}")
        except CancelException:
            raise
        except Exception as e:
            d(f"cl{i}:EXC:{type(e).__name__}")
            continue

    if sample_urls:
        for tag, url in sample_urls[:4]:
            d(f"sample_{tag}:{url}")

    # إذا حصلنا على رفض صريح => البث ميت
    if explicit_blocked:
        return False

    # إذا اكتشفنا نمط transcoder ولم نحصل على رفض صريح => غير مؤكد
    if transcoder_mode:
        d("TRANSCODER_DETECTED")
        return "transcoder_detected"

    # في الحالات الأخرى => غير قابل للاختبار
    return None

# ══════════════════════════════════════════════════════════════
#  Module Detection (VOD / Series / EPG) — مع تحسين المهلات
# ══════════════════════════════════════════════════════════════

def _detect_xtream_modules(session, api_url, first_stream_id=None, job_id=None):
    modules = {"live": True, "vod": False, "series": False, "epg": False}
    try:
        if job_id and is_cancelled(job_id):
            raise CancelException("Cancelled")
        r = safe_request(session, f"{api_url}&action=get_vod_categories",
                         headers=HEADERS, timeout=5, verify=False)
        if r.status_code == 200:
            j = r.json()
            if isinstance(j, list) and len(j) > 0:
                modules["vod"] = True
    except Exception:
        pass
    try:
        if job_id and is_cancelled(job_id):
            raise CancelException("Cancelled")
        r = safe_request(session, f"{api_url}&action=get_series_categories",
                         headers=HEADERS, timeout=5, verify=False)
        if r.status_code == 200:
            j = r.json()
            if isinstance(j, list) and len(j) > 0:
                modules["series"] = True
    except Exception:
        pass
    if first_stream_id:
        try:
            if job_id and is_cancelled(job_id):
                raise CancelException("Cancelled")
            r = safe_request(session, f"{api_url}&action=get_short_epg&stream_id={first_stream_id}",
                             headers=HEADERS, timeout=5, verify=False)
            if r.status_code == 200:
                j = r.json()
                epg_list = j.get("epg_listings") if isinstance(j, dict) else None
                if isinstance(epg_list, list) and len(epg_list) > 0:
                    modules["epg"] = True
        except Exception:
            pass
    return modules

def _detect_mac_modules(session, portal_url, api_path, headers, cookies, first_ch_id=None, job_id=None):
    modules = {"live": True, "vod": False, "series": False, "epg": False}
    try:
        if job_id and is_cancelled(job_id):
            raise CancelException("Cancelled")
        r = safe_request(session, f"{portal_url}{api_path}",
                         params={"type": "vod", "action": "get_categories",
                                 "JsHttpRequest": "1-xml"},
                         headers=headers, cookies=cookies, timeout=5, verify=False)
        if r.status_code == 200:
            js = (r.json() or {}).get("js", None)
            if isinstance(js, list) and len(js) > 0:
                modules["vod"] = True
    except Exception:
        pass
    try:
        if job_id and is_cancelled(job_id):
            raise CancelException("Cancelled")
        r = safe_request(session, f"{portal_url}{api_path}",
                         params={"type": "series", "action": "get_categories",
                                 "JsHttpRequest": "1-xml"},
                         headers=headers, cookies=cookies, timeout=5, verify=False)
        if r.status_code == 200:
            js = (r.json() or {}).get("js", None)
            if isinstance(js, list) and len(js) > 0:
                modules["series"] = True
    except Exception:
        pass
    if first_ch_id:
        try:
            if job_id and is_cancelled(job_id):
                raise CancelException("Cancelled")
            r = safe_request(session, f"{portal_url}{api_path}",
                             params={"type": "itv", "action": "get_epg_info",
                                     "ch_id": first_ch_id, "size": "1",
                                     "JsHttpRequest": "1-xml"},
                             headers=headers, cookies=cookies, timeout=5, verify=False)
            if r.status_code == 200:
                js = (r.json() or {}).get("js", None)
                if js:
                    modules["epg"] = True
        except Exception:
            pass
    return modules

# ── VOD / Series total counters ──────────────────────────────────

def _fetch_xtream_vod_count(session, api_url, job_id=None):
    if job_id and is_cancelled(job_id):
        raise CancelException("Cancelled")
    try:
        r = safe_request(session, f"{api_url}&action=get_vod_streams",
                         headers=HEADERS, timeout=8, verify=False)
        if r.status_code == 200:
            j = r.json()
            if isinstance(j, list):
                return len(j)
    except Exception:
        pass
    return 0

def _fetch_xtream_series_count(session, api_url, job_id=None):
    if job_id and is_cancelled(job_id):
        raise CancelException("Cancelled")
    try:
        r = safe_request(session, f"{api_url}&action=get_series",
                         headers=HEADERS, timeout=8, verify=False)
        if r.status_code == 200:
            j = r.json()
            if isinstance(j, list):
                return len(j)
    except Exception:
        pass
    return 0

def _fetch_mac_vod_count(session, portal_url, api_path, headers, cookies, job_id=None):
    if job_id and is_cancelled(job_id):
        raise CancelException("Cancelled")
    try:
        r = safe_request(session, f"{portal_url}{api_path}",
                         params={"type": "vod", "action": "get_ordered_list",
                                 "p": "1", "JsHttpRequest": "1-xml"},
                         headers=headers, cookies=cookies, timeout=8, verify=False)
        if r.status_code == 200:
            js = (r.json() or {}).get("js", {}) or {}
            if isinstance(js, dict):
                return int(js.get("total_items") or len(js.get("data", [])) or 0)
            elif isinstance(js, list):
                return len(js)
    except Exception:
        pass
    return 0

def _fetch_mac_series_count(session, portal_url, api_path, headers, cookies, job_id=None):
    if job_id and is_cancelled(job_id):
        raise CancelException("Cancelled")
    try:
        r = safe_request(session, f"{portal_url}{api_path}",
                         params={"type": "series", "action": "get_ordered_list",
                                 "p": "1", "JsHttpRequest": "1-xml"},
                         headers=headers, cookies=cookies, timeout=8, verify=False)
        if r.status_code == 200:
            js = (r.json() or {}).get("js", {}) or {}
            if isinstance(js, dict):
                return int(js.get("total_items") or len(js.get("data", [])) or 0)
            elif isinstance(js, list):
                return len(js)
    except Exception:
        pass
    return 0

# ══════════════════════════════════════════════════════════════
#  v5.2 Enhancement Layer — مع تحسينات الإلغاء والخصوصية
# ══════════════════════════════════════════════════════════════

_BW_CACHE   = {}
_BW_LOCK    = threading.Lock()

_GEO_CACHE  = {}
_GEO_LOCK   = threading.Lock()

_SSL_CACHE  = {}
_SSL_LOCK   = threading.Lock()

# ── v5.9 FIX 6: token-bucket GeoIP rate limiter ──
_GEO_BUCKET_LOCK  = threading.Lock()
_GEO_BUCKET       = {"tokens": 45.0, "last": time.time()}
_GEO_CAPACITY     = 45.0
_GEO_REFILL_RATE  = 0.75  # tokens/sec

def _geo_try_consume():
    with _GEO_BUCKET_LOCK:
        now = time.time()
        elapsed = now - _GEO_BUCKET["last"]
        _GEO_BUCKET["tokens"] = min(_GEO_CAPACITY,
                                    _GEO_BUCKET["tokens"] + elapsed * _GEO_REFILL_RATE)
        _GEO_BUCKET["last"] = now
        if _GEO_BUCKET["tokens"] >= 1.0:
            _GEO_BUCKET["tokens"] -= 1.0
            return True
        return False

def _make_retry_session():
    s = requests.Session()
    retry = Retry(total=2, backoff_factor=0.5,
                   status_forcelist=[500, 502, 503, 504])
    adapter = HTTPAdapter(max_retries=retry)
    s.mount("http://", adapter)
    s.mount("https://", adapter)
    return s

def _extract_host_port(server_url):
    try:
        u = server_url
        if not re.match(r'^https?://', u):
            u = "http://" + u
        parsed = urlparse(u)
        host = parsed.hostname
        port = parsed.port
        scheme = parsed.scheme
        if port is None:
            port = 443 if scheme == "https" else 80
        return host, port, scheme
    except Exception:
        return None, None, None

# ── Feature 1: Stream Bandwidth Test ────────────────────────────
#  v5.9.2 FIX: دعم cookies لقياس باندويث بوابات MAC بهوية الجلسة

def _measure_bandwidth(url, cache_key, headers=None, cookies=None):
    with _BW_LOCK:
        cached = _BW_CACHE.get(cache_key)
    if cached and (time.time() - cached["ts"] < 900):
        return cached["kbps"]

    kbps = 0.0
    try:
        sess = _make_retry_session()
        h = headers or {"User-Agent": "VLC/3.0.9"}
        max_bytes = 512 * 1024
        timeout_s = 6
        total_bytes = 0
        start = time.perf_counter()
        r = safe_request(sess, url, headers=h, cookies=cookies,
                         timeout=timeout_s, verify=False, stream=True)
        if r.status_code >= 400:
            raise Exception("bad status")
        for chunk in r.iter_content(64 * 1024):
            if not chunk:
                break
            total_bytes += len(chunk)
            elapsed = time.perf_counter() - start
            if total_bytes >= max_bytes or elapsed >= timeout_s:
                break
        r.close()
        elapsed = max(time.perf_counter() - start, 0.001)
        if total_bytes > 0:
            kbps = round((total_bytes * 8 / 1000.0) / elapsed, 1)
    except Exception:
        kbps = 0.0

    with _BW_LOCK:
        _BW_CACHE[cache_key] = {"kbps": kbps, "ts": time.time()}
    return kbps

def _get_mac_bandwidth_url(session, portal_url, api_path, headers, cookies, cmds):
    for cmd in cmds[:1]:
        try:
            params = {"type": "itv", "action": "create_link", "cmd": cmd,
                      "forced": "1", "JsHttpRequest": "1-xml"}
            r = safe_request(session, f"{portal_url}{api_path}", params=params,
                             headers=headers, cookies=cookies, timeout=5, verify=False)
            if r.status_code != 200:
                continue
            js = (r.json() or {}).get("js", "") or {}
            raw_url = None
            if isinstance(js, dict):
                raw_url = js.get("url") or js.get("cmd")
            else:
                raw_url = str(js)
            if isinstance(raw_url, str) and raw_url.startswith("ffrt://"):
                raw_url = "http://" + raw_url[len("ffrt://"):]
            final_url = _normalize_stream_url(raw_url, portal_url)
            if final_url:
                return final_url
        except Exception:
            continue
    return None

# ── Feature 2: Quality Score Calculator (0-100) ─────────────────

def _compute_score(res):
    try:
        if not res.get("auth_valid"):
            return 0
        score = 20
        if res.get("stream_ok") is True:
            score += 30
        elif res.get("stream_ok") is False:
            score += 5
        bw = res.get("bandwidth_kbps") or 0.0
        if bw > 3000:
            score += 20
        elif bw > 1500:
            score += 15
        elif bw > 800:
            score += 10
        elif bw > 200:
            score += 5
        ch = res.get("channels_count") or 0
        if ch > 5000:
            score += 10
        elif ch > 2000:
            score += 7
        elif ch > 500:
            score += 5
        elif ch > 100:
            score += 2
        mods = res.get("modules") or {}
        if mods.get("vod"):
            score += 3
        if mods.get("series"):
            score += 3
        if mods.get("epg"):
            score += 4
        exp      = res.get("exp_date")
        sub_type = res.get("sub_type")
        if sub_type == "Paid":
            if exp == "Unlimited":
                score += 10
            elif exp and exp != "N/A":
                try:
                    exp_dt = datetime.strptime(exp, "%Y-%m-%d").replace(tzinfo=timezone.utc)
                    days = (exp_dt - datetime.now(timezone.utc)).days
                    if days > 30:
                        score += 10
                    elif days > 7:
                        score += 5
                except Exception:
                    pass
        ms = res.get("api_ms")
        if ms is not None:
            if ms < 200:
                score += 5
            elif ms < 500:
                score += 3
            if ms > 3000:
                score -= 10
            elif ms > 1000:
                score -= 5
        return max(0, min(100, int(score)))
    except Exception:
        return 0

# ── Feature 3: GeoIP Lookup (ip-api.com) ────────────────────────

def _geoip_lookup(hostname):
    if not hostname:
        return None

    with _GEO_LOCK:
        cached = _GEO_CACHE.get(hostname)
    if cached is not None:
        return None if isinstance(cached, str) else cached

    try:
        ip = _resolve_host_bounded(hostname, timeout=5)
    except Exception:
        with _GEO_LOCK:
            _GEO_CACHE[hostname] = "NULL"
        return None

    if not _geo_try_consume():
        with _GEO_LOCK:
            _GEO_CACHE[hostname] = "RATE_LIMITED"
        return None

    result = None
    try:
        sess = _make_retry_session()
        r = safe_request(sess,
                         f"http://ip-api.com/json/{ip}?fields=status,country,countryCode,city,isp,org,query",
                         timeout=5)
        if r.status_code == 200:
            j = r.json()
            if j.get("status") == "success":
                result = {
                    "ip": j.get("query"),
                    "country": j.get("country"),
                    "country_code": j.get("countryCode"),
                    "city": j.get("city"),
                    "isp": j.get("isp"),
                    "org": j.get("org"),
                }
    except Exception:
        result = None

    with _GEO_LOCK:
        _GEO_CACHE[hostname] = result if result is not None else "NULL"
    return result

# ── Feature 4: SSL Certificate Check ────────────────────────────

def _ssl_check(hostname, port=443):
    if not hostname:
        return None
    cache_key = f"{hostname}:{port}"
    with _SSL_LOCK:
        cached = _SSL_CACHE.get(cache_key)
    if cached and (time.time() - cached["ts"] < 3600):
        return cached["data"]

    data = None
    try:
        ip = _resolve_host_bounded(hostname, timeout=5)
        ctx = ssl.create_default_context()
        with socket.create_connection((ip, port), timeout=5) as sock:
            with ctx.wrap_socket(sock, server_hostname=hostname) as ssock:
                cert   = ssock.getpeercert() or {}
                cipher = ssock.cipher()
                tls_version = ssock.version()
                subject = dict(x[0] for x in cert.get("subject", []))
                issuer  = dict(x[0] for x in cert.get("issuer", []))
                not_after = cert.get("notAfter")
                not_after_iso = None
                if not_after:
                    try:
                        dt = datetime.strptime(not_after, "%b %d %H:%M:%S %Y %Z")
                        not_after_iso = dt.strftime("%Y-%m-%d")
                    except Exception:
                        not_after_iso = not_after
                data = {
                    "valid": True,
                    "tls_version": tls_version,
                    "cipher": cipher[0] if cipher else None,
                    "subject": subject.get("commonName", ""),
                    "issuer": issuer.get("commonName", issuer.get("organizationName", "")),
                    "not_after": not_after_iso
                }
    except Exception as e:
        data = {"valid": False, "error": str(e)[:80]}

    with _SSL_LOCK:
        _SSL_CACHE[cache_key] = {"data": data, "ts": time.time()}
    return data

# ── Feature 5: M3U Playlist Analysis ────────────────────────────

def _analyze_m3u(url):
    try:
        sess = _make_retry_session()
        max_bytes = 2 * 1024 * 1024
        timeout_s = 8
        total_bytes = 0
        buf = ""
        partial = True
        start = time.perf_counter()

        with safe_request(sess, url, headers=HEADERS, timeout=timeout_s,
                          verify=False, stream=True) as r:
            if r.status_code >= 400:
                return None
            for chunk in r.iter_content(64 * 1024):
                if not chunk:
                    break
                try:
                    buf += chunk.decode("utf-8", errors="ignore")
                except Exception:
                    pass
                total_bytes += len(chunk)
                elapsed = time.perf_counter() - start
                if "#EXT-X-ENDLIST" in buf:
                    partial = False
                    break
                if total_bytes >= max_bytes or elapsed >= timeout_s:
                    partial = True
                    break
            else:
                partial = False

        lines = buf.split("\n")
        extinf_lines = [l for l in lines if l.strip().upper().startswith("#EXTINF")]
        total_channels = len(extinf_lines)

        groups   = set()
        has_epg  = False
        qualities = {"SD": 0, "HD": 0, "FHD": 0, "4K": 0, "Unknown": 0}

        for line in extinf_lines:
            m = re.search(r'group-title="([^"]*)"', line, re.IGNORECASE)
            if m and m.group(1):
                groups.add(m.group(1))
            if re.search(r'tvg-id="[^"]+"', line, re.IGNORECASE):
                has_epg = True
            up = line.upper()
            if "4K" in up or "UHD" in up:
                qualities["4K"] += 1
            elif "FHD" in up or "1080" in up:
                qualities["FHD"] += 1
            elif "HD" in up or "720" in up:
                qualities["HD"] += 1
            elif "SD" in up:
                qualities["SD"] += 1
            else:
                qualities["Unknown"] += 1

        return {
            "total_channels": total_channels,
            "groups_count": len(groups),
            "has_epg": has_epg,
            "qualities": qualities,
            "partial": partial
        }
    except Exception:
        return None

# ══════════════════════════════════════════════════════════════
#  v5.3 Rescue Chain — Xtream/M3U path only.
#  تم تعديلها لإرجاع عدد القنوات أيضاً.
# ══════════════════════════════════════════════════════════════

def _rescue_try_getphp_m3u(session, base_url, username, password):
    try:
        url = (f"{base_url.rstrip('/')}/get.php"
               f"?username={username}&password={password}"
               f"&type=m3u_plus&output=ts")
        max_bytes = 2 * 1024 * 1024  # زيادة لجلب قائمة أكبر
        total = 0
        buf = ""
        with safe_request(session, url, headers=HEADERS, timeout=8, verify=False, stream=True) as r:
            if r.status_code >= 400:
                return False, None, 0
            for chunk in r.iter_content(16 * 1024):
                if not chunk:
                    break
                try:
                    buf += chunk.decode("utf-8", errors="ignore")
                except Exception:
                    pass
                total += len(chunk)
                if total >= max_bytes:
                    break
        ok = ("#EXTM3U" in buf) and ("#EXTINF" in buf)
        if not ok:
            return False, None, 0
        # حساب عدد القنوات
        total_channels = len([l for l in buf.split("\n") if l.strip().upper().startswith("#EXTINF")])
        first_url = None
        m = re.search(r'^#EXTINF[^\n]*\n\s*(https?://\S+)', buf, re.M)
        if m:
            first_url = m.group(1)
        return True, first_url, total_channels
    except Exception:
        return False, None, 0

# ══════════════════════════════════════════════════════════════
#  Bridge: MAC → M3U   (مع تحسينات الخصوصية والإلغاء)
# ══════════════════════════════════════════════════════════════

_BRIDGE_AUTH  = {}
_BRIDGE_LIST  = {}
_BRIDGE_LINKS = {}

def _bridge_auth(portal_url, mac_address, force=False):
    portal_url = normalize_portal_url(portal_url)
    key = (portal_url, mac_address)
    now = time.time()
    with _GLOB_LOCK:
        entry = _BRIDGE_AUTH.get(key)
    if not force and entry and now - entry["ts"] < 300:
        return entry
    mac_headers = {
        "User-Agent": MAG_UA_POOL[0],
        "X-User-Agent": "Model: MAG254; Link: WiFi",
        "Accept": "*/*",
        "Referer": f"{portal_url}/c/",
    }
    cookies = {"mac": mac_address, "stb_lang": "en"}
    session = requests.Session()
    try:
        with _BoundedGuard(_get_disc_lock(portal_url), timeout=_DISC_LOCK_TIMEOUT):
            if portal_url in _PATH_CACHE:
                discovered = _PATH_CACHE[portal_url]
            else:
                discovered = discover_api_path(session, portal_url, mac_headers, cookies)
                # لا نخزّن None أبداً
                if discovered:
                    _PATH_CACHE[portal_url] = discovered
    except _LockBusy:
        discovered = _PATH_CACHE.get(portal_url)
    paths = [discovered] + PORTAL_API_PATHS if discovered else list(PORTAL_API_PATHS)
    hs_resp, api_path = None, None
    for path in paths:
        try:
            r = safe_request(session,
                f"{portal_url}{path}?type=stb&action=handshake&prelogin=1&token=&JsHttpRequest=1-xml",
                headers=mac_headers, cookies=cookies, timeout=5, verify=False, allow_redirects=True)
            if r.status_code in (200, 401, 403):
                hs_resp, api_path = r, path
                break
        except Exception:
            continue
    if hs_resp is None:
        return None
    token = ""
    try:
        j = hs_resp.json()
        if isinstance(j, dict):
            token = (j.get("js") or {}).get("token", "") or j.get("token", "")
    except Exception:
        pass
    if not token:
        return None
    entry = {"session": session, "headers": mac_headers, "cookies": cookies,
             "api_path": api_path, "token": token, "ts": now}
    with _GLOB_LOCK:
        _BRIDGE_AUTH[key] = entry
    return entry

def _bridge_api(portal_url, mac_address, params, auth=None):
    auth = auth or _bridge_auth(portal_url, mac_address)
    if not auth:
        return None, None
    headers = dict(auth["headers"])
    headers["Authorization"] = f"Bearer {auth['token']}"
    url = f"{normalize_portal_url(portal_url)}{auth['api_path']}"
    try:
        r = safe_request(auth["session"], url, params=params, headers=headers,
                         cookies=auth["cookies"], timeout=8, verify=False)
    except Exception:
        return None, auth
    if r.status_code in (401, 403):
        auth = _bridge_auth(portal_url, mac_address, force=True)
        if not auth:
            return None, None
        headers["Authorization"] = f"Bearer {auth['token']}"
        try:
            r = safe_request(auth["session"], url, params=params, headers=headers,
                             cookies=auth["cookies"], timeout=8, verify=False)
        except Exception:
            return None, auth
    if r.status_code != 200:
        return None, auth
    try:
        return (r.json() or {}).get("js", {}), auth
    except Exception:
        return None, auth

def _bridge_channels(portal_url, mac_address):
    key = (normalize_portal_url(portal_url), mac_address)
    now = time.time()
    with _GLOB_LOCK:
        entry = _BRIDGE_LIST.get(key)
    if entry and now - entry["ts"] < 600:
        return entry
    js, auth = _bridge_api(portal_url, mac_address,
                           {"type": "itv", "action": "get_all_channels",
                            "JsHttpRequest": "1-xml"})
    if js is None:
        return None
    data_list = (js.get("data", []) if isinstance(js, dict)
                 else (js if isinstance(js, list) else []))
    genres = {}
    gj, _ = _bridge_api(portal_url, mac_address,
                        {"type": "itv", "action": "get_genres",
                         "JsHttpRequest": "1-xml"}, auth=auth)
    if isinstance(gj, list):
        for g in gj:
            if isinstance(g, dict) and g.get("id") is not None:
                genres[str(g["id"])] = str(g.get("title", ""))
    entry = {"channels": data_list, "genres": genres, "ts": now}
    with _GLOB_LOCK:
        _BRIDGE_LIST[key] = entry
    return entry

@app.route("/bridge/playlist")
def bridge_playlist():
    auth_error = require_api_key()
    if auth_error:
        return auth_error
    portal = request.args.get("portal", "").strip()
    mac    = request.args.get("mac", "").strip()
    mode   = request.args.get("mode", "live")
    if not portal or not mac:
        return "Missing portal/mac", 400
    entry = _bridge_channels(portal, mac)
    if not entry or not entry["channels"]:
        return "#EXTM3U\n", 200, {"Content-Type": "text/plain; charset=utf-8"}
    base  = request.host_url.rstrip("/")
    lines = ["#EXTM3U"]
    for ch in entry["channels"]:
        if not isinstance(ch, dict):
            continue
        name  = str(ch.get("name", "channel")).replace(",", " ")
        gid   = str(ch.get("tv_genre_id", ""))
        group = entry["genres"].get(gid, "")
        logo  = str(ch.get("logo", ""))
        ch_id = ch.get("id")
        if mode == "live":
            url = f"{base}/bridge/play?portal={quote(portal)}&mac={quote(mac)}&ch={ch_id}"
        else:
            url = _normalize_stream_url(str(ch.get("cmd", "")), portal)
            if not url:
                continue
        attrs = f' group-title="{group}"' if group else ""
        if logo:
            attrs += f' tvg-logo="{logo}"'
        lines.append(f'#EXTINF:-1 tvg-id="{ch_id}"{attrs},{name}')
        lines.append(url)
    body = "\n".join(lines) + "\n"
    return body, 200, {"Content-Type": "text/plain; charset=utf-8"}

@app.route("/bridge/play")
def bridge_play():
    auth_error = require_api_key()
    if auth_error:
        return auth_error
    portal = request.args.get("portal", "").strip()
    mac    = request.args.get("mac", "").strip()
    ch     = request.args.get("ch", "").strip()
    proxy  = request.args.get("proxy", "0") == "1"
    if not portal or not mac or not ch:
        return "Missing params", 400
    key = (normalize_portal_url(portal), mac, ch)
    now = time.time()
    with _GLOB_LOCK:
        cached = _BRIDGE_LINKS.get(key)
    if cached and now - cached[1] < 120:
        url = cached[0]
    else:
        cmd   = None
        entry = _bridge_channels(portal, mac)
        if entry:
            for c in entry["channels"]:
                if isinstance(c, dict) and str(c.get("id")) == ch:
                    cmd = str(c.get("cmd", ""))
                    break
        if not cmd:
            return "Channel not found", 404
        js, _ = _bridge_api(portal, mac,
                            {"type": "itv", "action": "create_link",
                             "cmd": cmd, "forced": "1", "JsHttpRequest": "1-xml"})
        raw = None
        if isinstance(js, dict):
            raw = js.get("url") or js.get("cmd")
        elif js:
            raw = str(js)
        if isinstance(raw, str) and raw.startswith("ffrt://"):
            raw = "http://" + raw[len("ffrt://"):]
        url = _normalize_stream_url(raw, portal)
        if not url:
            return "No stream", 502
        with _GLOB_LOCK:
            _BRIDGE_LINKS[key] = (url, now)
    if proxy:
        auth = _bridge_auth(portal, mac)
        ph = dict(auth["headers"]) if auth else {"User-Agent": MAG_UA_POOL[0]}
        ph = {k: v for k, v in ph.items() if k.lower() not in ("accept-encoding", "connection")}
        pc = auth["cookies"] if auth else {"mac": mac, "stb_lang": "en"}
        def gen():
            try:
                with safe_request(requests.Session(), url, stream=True, timeout=10, verify=False,
                                  headers=ph, cookies=pc) as r:
                    for chunk in r.iter_content(1024 * 64):
                        if chunk:
                            yield chunk
            except Exception:
                return
        return Response(gen(), mimetype="application/octet-stream")
    return redirect(url)

# ══════════════════════════════════════════════════════════════
#  دوال الإلغاء (الإصلاح 2)
# ══════════════════════════════════════════════════════════════

def is_cancelled(job_id):
    with _CANCEL_LOCK:
        return _CANCEL_FLAG.get(job_id, False)

def set_cancel(job_id):
    with _CANCEL_LOCK:
        _CANCEL_FLAG[job_id] = True

def clear_cancel(job_id):
    with _CANCEL_LOCK:
        _CANCEL_FLAG.pop(job_id, None)

# ══════════════════════════════════════════════════════════════
#  Core Checkers with UNIVERSAL EXCEPTION TRAP
# ══════════════════════════════════════════════════════════════

def test_single_server(server_url, username, password, m3u_analysis_enabled=False, job_id=None):
    try:
        if job_id and is_cancelled(job_id):
            raise CancelException("Cancelled")

        server_url = server_url.strip().lstrip('/')
        if not server_url.startswith(("http://", "https://")):
            server_url = "http://" + server_url

        res = {
            "server": server_url, "username": username, "password": password,
            "is_online": False, "auth_valid": False, "status": "Unknown",
            "is_trial": False, "sub_type": "Paid",
            "max_connections": "1", "active_connections": "0",
            "exp_date": "N/A", "created_date": "N/A",
            "api_ms": 9999.0, "channels_count": 0,
            "api_path": "", "stream_ok": None, "m3u_url": "",
            "diag": "", "error": "",
            "modules": {"live": False, "vod": False, "series": False, "epg": False},
            "bandwidth_kbps": 0.0,
            "score": 0,
            "geo": None,
            "ssl_info": None,
            "m3u_analysis": None,
            "rescued": False,
            "rescue_method": "",
            "vod_count": 0,
            "series_count": 0,
            "failure_reason": ""
        }

        # Pre-resolve DNS
        base_url = server_url
        _dns_host, _dns_port, _dns_scheme = _extract_host_port(base_url)
        if _dns_host:
            try:
                _resolve_host_bounded(_dns_host, timeout=5)
            except Exception as dns_exc:
                res["error"] = f"DNS Timeout: {str(dns_exc)[:30]}"
                res["failure_reason"] = "DNS_TIMEOUT"
                return sanitize_result(res)

        api_url = f"{base_url.rstrip('/')}/player_api.php?username={username}&password={password}"
        session = requests.Session()
        resp         = None
        original_exc = None
        start_t      = time.perf_counter()

        # ── Primary attempt ──
        try:
            if job_id and is_cancelled(job_id):
                raise CancelException("Cancelled")
            resp = safe_request(session, api_url, headers=HEADERS, timeout=5,
                                verify=False, allow_redirects=True)
        except requests.exceptions.ConnectionError as ce:
            original_exc = ce
            resp = None
        except Exception as e:
            res["error"] = str(e)[:35]
            res["failure_reason"] = "EXCEPTION"
            return sanitize_result(res)

        if resp is not None and resp.status_code >= 500:
            try:
                time.sleep(0.3)
                if job_id and is_cancelled(job_id):
                    raise CancelException("Cancelled")
                resp = safe_request(session, api_url, headers=HEADERS, timeout=5,
                                    verify=False, allow_redirects=True)
            except Exception as e:
                res["error"] = str(e)[:35]
                res["failure_reason"] = "EXCEPTION"
                return sanitize_result(res)

        # ── RESCUE STEP 2 — Conditional Port Rotation ──
        if resp is None and original_exc is not None:
            try:
                host, _op, _os = _extract_host_port(base_url)
                if host:
                    candidates = []
                    for c_scheme, c_port in (("http", 8080), ("https", 443), ("http", 80)):
                        cand = f"{c_scheme}://{host}:{c_port}"
                        if cand.rstrip('/') != base_url.rstrip('/') and \
                           cand not in [c[0] for c in candidates]:
                            candidates.append((cand, c_port))

                    for cand_base, cand_port in candidates:
                        try:
                            if job_id and is_cancelled(job_id):
                                raise CancelException("Cancelled")
                            _resolve_host_bounded(host, timeout=3)
                            cand_api = (f"{cand_base.rstrip('/')}/player_api.php"
                                       f"?username={username}&password={password}")
                            cand_resp = safe_request(session, cand_api, headers=HEADERS, timeout=4,
                                                     verify=False, allow_redirects=True)
                            base_url = cand_base
                            api_url  = cand_api
                            resp     = cand_resp
                            res["rescue_method"] = f"port:{cand_port}"
                            break
                        except Exception:
                            continue
            except Exception:
                pass

        if resp is None:
            res["error"] = str(original_exc)[:35] if original_exc else "Connection failed"
            res["failure_reason"] = "CONNECTION_FAILED"
            return sanitize_result(res)

        res["api_ms"] = round((time.perf_counter() - start_t) * 1000, 1)

        # ── RESCUE STEP 1 — Alternate API Endpoint (panel_api.php) ──
        if original_exc is None and resp.status_code == 404:
            try:
                alt_api = (f"{base_url.rstrip('/')}/panel_api.php"
                          f"?username={username}&password={password}")
                alt_resp = safe_request(session, alt_api, headers=HEADERS, timeout=5,
                                        verify=False, allow_redirects=True)
                if alt_resp.status_code == 200:
                    api_url = alt_api
                    resp    = alt_resp
                    res["rescue_method"] = "panel_api"
            except Exception:
                pass

        if resp.status_code == 200:
            res["is_online"] = True
            try:
                data = resp.json()
            except Exception:
                res["error"] = "Invalid JSON"
                res["failure_reason"] = "INVALID_JSON"
                return sanitize_result(res)

            user_info = data.get("user_info", {})
            if user_info.get("auth") == 1 or user_info.get("status") in ["Active", "Trial"]:
                res["auth_valid"] = True
                res["modules"]["live"] = True
                status_val = user_info.get("status", "Active")
                if res["rescue_method"]:
                    res["rescued"] = True
                    res["status"]  = "Rescued"
                else:
                    res["status"] = status_val

                is_trial_flag  = user_info.get("is_trial", "0")
                package_name   = str(user_info.get("package_name", "")).lower()
                username_lower = username.lower()

                detected_trial = False
                if str(is_trial_flag) == "1" or status_val.lower() == "trial":
                    detected_trial = True
                elif any(kw in package_name for kw in ["trial", "test", "demo"]):
                    detected_trial = True
                elif any(kw in username_lower for kw in ["trial", "test", "demo"]):
                    detected_trial = True

                res["is_trial"]           = detected_trial
                res["sub_type"]           = "Trial" if detected_trial else "Paid"
                res["max_connections"]    = user_info.get("max_connections", "1")
                res["active_connections"] = user_info.get(
                    "active_cons", user_info.get("active_connections", "0"))
                res["exp_date"]           = format_timestamp(user_info.get("exp_date"))
                ca = user_info.get("created_at")
                res["created_date"] = (format_timestamp(ca)
                                       if ca not in (None, "", "0") else "N/A")
            else:
                # ── الإصلاح 10: تجربة get.php حتى لو كانت auth غير صالحة ──
                res["error"] = "Auth Failed"
                res["failure_reason"] = "AUTH_FAILED"
                rescued_ok = False
                first_url  = None
                channels_count_rescue = 0
                try:
                    if job_id and is_cancelled(job_id):
                        raise CancelException("Cancelled")
                    rescued_ok, first_url, channels_count_rescue = _rescue_try_getphp_m3u(
                        session, base_url, username, password)
                except Exception:
                    rescued_ok = False
                    first_url  = None
                if rescued_ok:
                    res["auth_valid"]      = True
                    res["status"]          = "Rescued"
                    res["rescued"]         = True
                    res["rescue_method"]   = "get.php"
                    res["is_online"]       = True
                    res["modules"]["live"] = True
                    res["channels_count"]  = channels_count_rescue
                    res["error"]           = ""
                    res["failure_reason"]  = ""
                    try:
                        if first_url:
                            sr = safe_request(session, first_url, headers=HEADERS,
                                              stream=True, timeout=6, verify=False)
                            res["stream_ok"] = sr.status_code < 400
                            sr.close()
                    except Exception:
                        res["stream_ok"] = None
                else:
                    return sanitize_result(res)
        else:
            res["error"] = f"HTTP {resp.status_code}"
            res["failure_reason"] = f"HTTP_{resp.status_code}"
            # ── RESCUE STEP 3 — get.php M3U Fallback (تم توسيع الشرط ليشمل 401) ──
            if resp.status_code in (404, 403, 401):
                rescued_ok = False
                first_url  = None
                channels_count_rescue = 0
                try:
                    if job_id and is_cancelled(job_id):
                        raise CancelException("Cancelled")
                    rescued_ok, first_url, channels_count_rescue = _rescue_try_getphp_m3u(
                        session, base_url, username, password)
                except Exception:
                    rescued_ok = False
                    first_url  = None
                if rescued_ok:
                    res["auth_valid"]      = True
                    res["status"]          = "Rescued"
                    res["rescued"]         = True
                    res["rescue_method"]   = "get.php"
                    res["is_online"]       = True
                    res["modules"]["live"] = True
                    res["channels_count"]  = channels_count_rescue
                    res["error"]           = ""
                    res["failure_reason"]  = ""
                    try:
                        if first_url:
                            sr = safe_request(session, first_url, headers=HEADERS,
                                              stream=True, timeout=6, verify=False)
                            res["stream_ok"] = sr.status_code < 400
                            sr.close()
                    except Exception:
                        res["stream_ok"] = None
                else:
                    return sanitize_result(res)
            else:
                return sanitize_result(res)

        # ── Fetch channels and test stream ──
        ids = []
        try:
            if job_id and is_cancelled(job_id):
                raise CancelException("Cancelled")
            ch_resp = safe_request(session, f"{api_url}&action=get_live_streams",
                                   headers=HEADERS, timeout=10, verify=False)
            if ch_resp.status_code == 200:
                channels = ch_resp.json()
                if isinstance(channels, list):
                    res["channels_count"] = len(channels)
                    for ch in channels[:15]:
                        if isinstance(ch, dict) and ch.get("stream_id") \
                                and ch["stream_id"] not in ids:
                            ids.append(ch["stream_id"])
                        if len(ids) >= 10:
                            break
                    if ids:
                        res["stream_ok"] = _check_xtream_stream(
                            session, base_url, username, password, ids, job_id)
        except CancelException:
            raise
        except Exception:
            pass

        # ── Module detection ──
        try:
            if job_id and is_cancelled(job_id):
                raise CancelException("Cancelled")
            first_sid = ids[0] if ids else None
            mods = _detect_xtream_modules(session, api_url, first_sid, job_id)
            mods["live"] = True
            res["modules"] = mods
        except CancelException:
            raise
        except Exception:
            pass

        # ── VOD / Series counters ──
        try:
            if res["modules"].get("vod"):
                res["vod_count"] = _fetch_xtream_vod_count(session, api_url, job_id)
        except CancelException:
            raise
        except Exception:
            res["vod_count"] = 0
        try:
            if res["modules"].get("series"):
                res["series_count"] = _fetch_xtream_series_count(session, api_url, job_id)
        except CancelException:
            raise
        except Exception:
            res["series_count"] = 0

        # ── v5.2 Enhancement Layer ──
        if res["auth_valid"]:
            host, port, scheme = None, None, None
            try:
                host, port, scheme = _extract_host_port(base_url)
            except Exception:
                pass

            # Bandwidth (cache key يشمل اليوزر لمنع الخلط)
            try:
                if res["stream_ok"] is True and ids:
                    cache_key = (host or base_url, username, "xtream")
                    bw_url = f"{base_url.rstrip('/')}/live/{username}/{password}/{ids[0]}.m3u8"
                    res["bandwidth_kbps"] = _measure_bandwidth(bw_url, cache_key, headers=HEADERS)
            except Exception:
                res["bandwidth_kbps"] = 0.0

            # GeoIP
            try:
                res["geo"] = _geoip_lookup(host)
            except Exception:
                res["geo"] = None

            # SSL
            try:
                if scheme == "https" or port == 443:
                    res["ssl_info"] = _ssl_check(host, port or 443)
                else:
                    res["ssl_info"] = None
            except Exception:
                res["ssl_info"] = None

            # M3U analysis
            try:
                if m3u_analysis_enabled:
                    m3u_link = f"{base_url.rstrip('/')}/get.php?username={username}&password={password}&type=m3u_plus&output=ts"
                    if m3u_link:
                        res["m3u_analysis"] = _analyze_m3u(m3u_link)
            except Exception:
                res["m3u_analysis"] = None

            # Score
            try:
                res["score"] = _compute_score(res)
            except Exception:
                res["score"] = 0

        return sanitize_result(res)

    except CancelException:
        return sanitize_result({
            "server": server_url,
            "username": username,
            "password": password,
            "auth_valid": False,
            "error": "CANCELLED",
            "failure_reason": "CANCELLED",
            "is_online": False,
            "status": "Cancelled",
            "api_ms": 0,
            "modules": {"live": False, "vod": False, "series": False, "epg": False},
            "diag": "",
            "rescued": False,
            "rescue_method": "",
            "bandwidth_kbps": 0.0,
            "score": 0,
            "geo": None,
            "ssl_info": None,
            "m3u_analysis": None,
            "vod_count": 0,
            "series_count": 0,
            "channels_count": 0,
            "exp_date": "N/A",
            "created_date": "N/A",
            "max_connections": "1",
            "active_connections": "0",
            "m3u_url": "",
            "stream_ok": None,
            "api_path": ""
        })

    except Exception as outer_exc:
        return sanitize_result({
            "server": server_url,
            "username": username,
            "password": password,
            "auth_valid": False,
            "is_trial": False,
            "sub_type": "Paid",
            "error": f"CRITICAL: {str(outer_exc)[:200]}",
            "failure_reason": "CRITICAL",
            "is_online": False,
            "status": "Error",
            "api_ms": 9999.0,
            "modules": {"live": False, "vod": False, "series": False, "epg": False},
            "diag": "",
            "rescued": False,
            "rescue_method": "",
            "bandwidth_kbps": 0.0,
            "score": 0,
            "geo": None,
            "ssl_info": None,
            "m3u_analysis": None,
            "vod_count": 0,
            "series_count": 0,
            "channels_count": 0,
            "exp_date": "N/A",
            "created_date": "N/A",
            "max_connections": "1",
            "active_connections": "0",
            "m3u_url": "",
            "stream_ok": None,
            "api_path": ""
        })

def test_mac_portal(portal_url, mac_address, job_id=None):
    try:
        if job_id and is_cancelled(job_id):
            raise CancelException("Cancelled")

        portal_url = normalize_portal_url(portal_url)

        res = {
            "server": portal_url,
            "username": f"MAC: {mac_address}",
            "password": "Stalker Portal",
            "is_online": False, "auth_valid": False, "status": "Failed",
            "is_trial": False, "sub_type": "",
            "max_connections": "N/A", "active_connections": "0",
            "exp_date": "N/A", "created_date": "N/A",
            "api_ms": 9999.0, "channels_count": 0,
            "api_path": "", "stream_ok": None, "m3u_url": "",
            "diag": "", "error": "",
            "modules": {"live": False, "vod": False, "series": False, "epg": False},
            "bandwidth_kbps": 0.0,
            "score": 0,
            "geo": None,
            "ssl_info": None,
            "m3u_analysis": None,
            "vod_count": 0,
            "series_count": 0,
            "failure_reason": ""
        }

        # Pre-resolve DNS
        _mac_host, _mac_port, _mac_scheme = _extract_host_port(portal_url)
        if _mac_host:
            try:
                _resolve_host_bounded(_mac_host, timeout=5)
            except Exception as dns_exc:
                res["error"] = f"DNS Timeout: {str(dns_exc)[:30]}"
                res["failure_reason"] = "DNS_TIMEOUT"
                return sanitize_result(res)

        chosen_ua = random.choice(MAG_UA_POOL)
        mac_headers = {
            "User-Agent": chosen_ua,
            "X-User-Agent": "Model: MAG254; Link: WiFi",
            "Accept": "*/*", "Pragma": "no-cache",
            "Accept-Encoding": "gzip", "Connection": "keep-Alive",
            "Referer": f"{portal_url}/c/",
        }
        cookies = {"mac": mac_address, "stb_lang": "en", "timezone": "Europe/Amsterdam"}
        session = requests.Session()

        # Discovery lock with bounded guard
        try:
            with _BoundedGuard(_get_disc_lock(portal_url), timeout=_DISC_LOCK_TIMEOUT):
                if portal_url in _PATH_CACHE:
                    discovered = _PATH_CACHE[portal_url]
                else:
                    discovered = discover_api_path(session, portal_url, mac_headers, cookies)
                    # لا نخزّن None أبداً
                    if discovered:
                        if len(_PATH_CACHE) > 200:
                            _PATH_CACHE.clear()
                        _PATH_CACHE[portal_url] = discovered
        except _LockBusy:
            discovered = _PATH_CACHE.get(portal_url)
        paths = [discovered] + PORTAL_API_PATHS if discovered else list(PORTAL_API_PATHS)

        def _try_handshake(base_url, path_list):
            last   = None
            consec = 0
            for path in path_list:
                for _ in range(2):
                    try:
                        if job_id and is_cancelled(job_id):
                            raise CancelException("Cancelled")
                        r = safe_request(session,
                            f"{base_url}{path}?type=stb&action=handshake"
                            f"&prelogin=1&token=&JsHttpRequest=1-xml",
                            headers=mac_headers, cookies=cookies,
                            timeout=5, verify=False, allow_redirects=True)
                        last = r.status_code
                        if r.status_code >= 500:
                            consec += 1
                            time.sleep(0.3)
                            continue
                        consec = 0
                        if r.status_code in (200, 401, 403):
                            return r, path, last
                    except CancelException:
                        raise
                    except Exception:
                        consec += 1
                        continue
                if consec >= 3:
                    break
            return None, None, last

        # ── الإصلاح 5: معالجة _LockBusy في semaphore ──
        try:
            with _BoundedGuard(_get_portal_sem(portal_url), timeout=_PORTAL_SEM_TIMEOUT):
                start_t = time.perf_counter()
                hs_resp, api_path, last_status = _try_handshake(portal_url, paths)
                if hs_resp is None:
                    time.sleep(1.0)
                    hs_resp, api_path, last_status = _try_handshake(portal_url, paths[:2])
                if hs_resp is None and portal_url.startswith("http://"):
                    alt = "https://" + portal_url[7:].replace(":80", "", 1)
                    hs_resp, api_path, ls2 = _try_handshake(alt, paths)
                    if hs_resp is not None:
                        portal_url = alt
                        res["server"] = alt
                        last_status  = ls2

                res["api_ms"] = round((time.perf_counter() - start_t) * 1000, 1)
                if hs_resp is None:
                    res["error"] = f"HTTP {last_status}" if last_status else "Portal unreachable"
                    res["failure_reason"] = "PORTAL_UNREACHABLE"
                    return sanitize_result(res)

                res["is_online"] = True
                res["api_path"]  = api_path

                token = ""
                try:
                    j = hs_resp.json()
                    if isinstance(j, dict):
                        token = ((j.get("js") or {}).get("token", "")
                                 or j.get("token", ""))
                except Exception:
                    pass
                if not token:
                    res["error"] = "No Token (MAC rejected)"
                    res["failure_reason"] = "NO_TOKEN"
                    return sanitize_result(res)

                auth_headers = dict(mac_headers)
                auth_headers["Authorization"] = f"Bearer {token}"

                # توليد SN وUID فريدين من عنوان MAC
                sn, uid = _get_mag_sn_uid(mac_address)

                mag_params = {
                    "type": "stb", "action": "get_profile", "hd": "1",
                    "ver": ("ImageDescription: 0.2.18-r23-254; ImageDate: Wed Oct 31 "
                            "15:22:54 EEST 2018; PORTAL version: 5.5.0; API Version: "
                            "JS API version: 343; STB API version: 146; "
                            "Player Engine version: 0x58C"),
                    "num_banks": "2", "sn": sn, "client_type": "STB",
                    "image_version": "218", "video_out": "hdmi",
                    "device_id": uid, "device_id2": uid,
                    "signature": "845519FCE3386C1807AD3469AAD6D2773080C6F94CB59CD0405FAEDE02F",
                    "auth_second_step": "1", "hw_version": "2.6-IB-00",
                    "not_valid_token": "0",
                    "metrics": json.dumps({"mac": mac_address, "sn": sn,
                                           "type": "STB", "model": "MAG254",
                                           "uid": uid, "random": ""}),
                    "hw_version_2": "aff4d6ab1ab4e0660f09f89809c6e9782fa43263",
                    "timestamp": str(int(time.time())), "api_signature": "262",
                }

                prof = {}
                profile_ok = False
                pr = None
                try:
                    if job_id and is_cancelled(job_id):
                        raise CancelException("Cancelled")
                    pr = safe_request(session, f"{portal_url}{api_path}", params=mag_params,
                                      headers=auth_headers, cookies=cookies,
                                      timeout=5, verify=False)
                    profile_ok = (pr.status_code == 200)
                except CancelException:
                    raise
                except Exception:
                    pass
                if not profile_ok:
                    try:
                        if job_id and is_cancelled(job_id):
                            raise CancelException("Cancelled")
                        pr = safe_request(session,
                            f"{portal_url}{api_path}?type=stb&action=get_profile&hd=1",
                            headers=auth_headers, cookies=cookies, timeout=5, verify=False)
                        profile_ok = (pr.status_code == 200)
                    except CancelException:
                        raise
                    except Exception:
                        pass
                if profile_ok and pr is not None:
                    try:
                        prof = (pr.json() or {}).get("js", {}) or {}
                        # فحص الحظر المحتمل في استجابة profile
                        if _looks_blocked(prof):
                            res["status"] = "Blocked"
                            res["error"] = "STB Blocked (provider)"
                            res["failure_reason"] = "STB_BLOCKED"
                            res["auth_valid"] = False
                            return sanitize_result(res)
                        new_tok = prof.get("token", "")
                        if new_tok:
                            auth_headers["Authorization"] = f"Bearer {new_tok}"
                    except Exception:
                        pass
                if not profile_ok:
                    res["error"] = "MAC Blocked / Expired"
                    res["failure_reason"] = "MAC_BLOCKED"
                    return sanitize_result(res)

                res["auth_valid"] = True
                res["status"]     = "Active MAC"
                res["modules"]["live"] = True
                diag = []

                date_keys = [
                    "expire_date", "exp_date", "expiration_date", "expires",
                    "end_date", "valid_to", "account_expire",
                    "phone", "status_expiration", "tariff_expiration"
                ]
                created_keys = [
                    "created", "created_at", "account_created",
                    "registration_date", "reg_date", "date_created"
                ]

                acc = {}
                try:
                    if job_id and is_cancelled(job_id):
                        raise CancelException("Cancelled")
                    ar = safe_request(session, f"{portal_url}{api_path}",
                                      params={"type": "account_info", "action": "get_profile"},
                                      headers=auth_headers, cookies=cookies,
                                      timeout=5, verify=False)
                    diag.append(f"acc:{ar.status_code}")
                    if ar.status_code == 200:
                        acc = (ar.json() or {}).get("js", {}) or {}
                except CancelException:
                    raise
                except Exception:
                    diag.append("acc:ERR")
                created = _pick_date(acc, created_keys)
                if created:
                    res["created_date"] = created

                sub = {}
                try:
                    if job_id and is_cancelled(job_id):
                        raise CancelException("Cancelled")
                    sr = safe_request(session, f"{portal_url}{api_path}",
                                      params={"type": "account_info",
                                              "action": "get_active_subscription"},
                                      headers=auth_headers, cookies=cookies,
                                      timeout=5, verify=False)
                    diag.append(f"sub:{sr.status_code}")
                    if sr.status_code == 200:
                        sj = (sr.json() or {}).get("js", {}) or {}
                        if isinstance(sj, dict):
                            sub = sj
                            if isinstance(sj.get("subscriptions"), list) and sj["subscriptions"]:
                                first = sj["subscriptions"][0]
                                if isinstance(first, dict):
                                    sub.update(first)
                except CancelException:
                    raise
                except Exception:
                    diag.append("sub:ERR")

                main = {}
                try:
                    if job_id and is_cancelled(job_id):
                        raise CancelException("Cancelled")
                    mr = safe_request(session, f"{portal_url}{api_path}",
                                      params={"type": "account_info", "action": "get_main_info",
                                              "JsHttpRequest": "1-xml"},
                                      headers=auth_headers, cookies=cookies,
                                      timeout=5, verify=False)
                    diag.append(f"main:{mr.status_code}")
                    if mr.status_code == 200:
                        main = (mr.json() or {}).get("js", {}) or {}
                except CancelException:
                    raise
                except Exception:
                    diag.append("main:ERR")

                # فحص الحظر في البيانات المجمعة
                if _looks_blocked({"p": prof, "a": acc, "s": sub, "m": main}):
                    res["status"] = "Blocked"
                    res["error"] = "STB Blocked (provider)"
                    res["failure_reason"] = "STB_BLOCKED"
                    res["auth_valid"] = False
                    return sanitize_result(res)

                # ── استخراج عدد الاتصالات (جديد) ──
                conn_keys_max = ["max_connections", "max_cons", "max_users",
                                 "max_clients", "connection_limit", "allowed_connections",
                                 "max_conn"]
                conn_keys_active = ["active_connections", "active_cons", "online",
                                    "current_connections", "connections", "current_users",
                                    "active_users", "number_of_connections"]

                def _extract_first(dicts_list, keys):
                    for d in dicts_list:
                        if not isinstance(d, dict):
                            continue
                        for k in keys:
                            if k in d:
                                v = d[k]
                                if v is not None and str(v).strip() not in ("", "0", "None", "null"):
                                    try:
                                        return str(int(v))
                                    except:
                                        return str(v)
                    return None

                max_conn = _extract_first([sub, main, acc, prof], conn_keys_max)
                active_conn = _extract_first([sub, main, acc, prof], conn_keys_active)
                if max_conn:
                    res["max_connections"] = max_conn
                if active_conn:
                    res["active_connections"] = active_conn

                plan_name = str(
                    _pick(sub,  ["tariff_plan_name", "plan_name", "tariff_name", "name"])
                    or _pick(main, ["tariff_plan_name", "tariff_name", "plan_name"])
                    or _pick(acc,  ["tariff_plan_name", "plan_name", "tariff_name"])
                    or ""
                )

                exp = (_pick_date(sub, date_keys)
                       or _pick_date(main, date_keys)
                       or _pick_date(acc,  date_keys))
                if not exp:
                    exp = (_scan_date_in_values(sub)
                           or _scan_date_in_values(main)
                           or _scan_date_in_values(acc))
                if exp:
                    res["exp_date"] = exp

                # ── محاولات إضافية لاستخراج بيانات الاشتراك (جديد) ──
                def _safe_get_json(params, tag):
                    try:
                        if job_id and is_cancelled(job_id):
                            raise CancelException("Cancelled")
                        rr = safe_request(session, f"{portal_url}{api_path}",
                                          params=params,
                                          headers=auth_headers, cookies=cookies,
                                          timeout=5, verify=False)
                        if rr.status_code == 200:
                            diag.append(f"{tag}:{rr.status_code}")
                            jj = (rr.json() or {}).get("js", {}) or {}
                            return jj
                        else:
                            diag.append(f"{tag}:{rr.status_code}")
                            return {}
                    except CancelException:
                        raise
                    except Exception:
                        diag.append(f"{tag}:ERR")
                        return {}

                # استخراج sub_id / account_id لاستخدامها في الطلبات الإضافية
                sub_id = _pick(sub, ["sub_id", "subscription_id", "id"])
                if not sub_id:
                    sub_id = _pick(main, ["sub_id", "subscription_id", "id"])
                if not sub_id:
                    sub_id = _pick(acc, ["sub_id", "subscription_id", "id"])
                if not sub_id:
                    sub_id = _pick(prof, ["sub_id", "subscription_id", "id"])

                account_id = _pick(sub, ["account_id", "user_id"])
                if not account_id:
                    account_id = _pick(main, ["account_id", "user_id"])
                if not account_id:
                    account_id = _pick(acc, ["account_id", "user_id"])
                if not account_id:
                    account_id = _pick(prof, ["account_id", "user_id"])

                extra_sub_params = {"type": "account_info", "action": "get_subscription",
                                    "JsHttpRequest": "1-xml"}
                extra_user_params = {"type": "account_info", "action": "get_user_info",
                                     "JsHttpRequest": "1-xml"}
                extra_acc_params = {"type": "account_info", "action": "get_account_info",
                                    "JsHttpRequest": "1-xml"}

                if sub_id:
                    extra_sub_params["sub_id"] = sub_id
                if account_id:
                    extra_sub_params["account_id"] = account_id

                extra_sub = _safe_get_json(extra_sub_params, "extra_sub")
                extra_user = _safe_get_json(extra_user_params, "extra_user")
                extra_acc = _safe_get_json(extra_acc_params, "extra_acc")

                # دمج البيانات الإضافية
                extra_data = {}
                for d in [extra_sub, extra_user, extra_acc]:
                    if isinstance(d, dict):
                        extra_data.update(d)

                # تحديث تاريخ الانتهاء إذا وجد في البيانات الإضافية
                exp_extra = (_pick_date(extra_data, date_keys)
                             or _scan_date_in_values(extra_data))
                if exp_extra:
                    res["exp_date"] = exp_extra
                    exp = exp_extra

                # تحديث تاريخ الإنشاء إذا لم يكن موجوداً
                if not created:
                    created_extra = _pick_date(extra_data, created_keys)
                    if created_extra:
                        res["created_date"] = created_extra
                        created = created_extra

                # تحديث عدد الأجهزة إذا وجد
                max_conn_extra = _extract_first([extra_data], conn_keys_max)
                active_conn_extra = _extract_first([extra_data], conn_keys_active)
                if max_conn_extra:
                    res["max_connections"] = max_conn_extra
                if active_conn_extra:
                    res["active_connections"] = active_conn_extra

                trial_kw = ["trial", "test", "demo", "\u062a\u062c\u0631\u0628\u0629"]
                if plan_name and any(k in plan_name.lower() for k in trial_kw):
                    res["is_trial"], res["sub_type"] = True, "Trial"
                elif plan_name or exp:
                    res["is_trial"], res["sub_type"] = False, "Paid"

                found = [n for n, v in
                         (("exp", exp), ("created", created), ("plan", plan_name)) if v]
                res["diag"] = (" | ".join(diag)
                               + (" | found:" + ",".join(found) if found else " | found:none"))
                if not found:
                    keys = []
                    for src in (sub, main, acc):
                        if isinstance(src, dict) and src:
                            keys += list(src.keys())[:8]
                    if keys:
                        res["diag"] += " | keys:" + ",".join(dict.fromkeys(keys))[:140]

                # ── الآن نخرج من القفل لمواصلة العمليات البطيئة ──
            # نهاية with semaphore

        except _LockBusy:
            res["error"] = "Portal busy (semaphore timeout)"
            res["failure_reason"] = "PORTAL_BUSY"
            return sanitize_result(res)

        # ── بعد الخروج من القفل، نستكمل العمليات البطيئة ──
        first_ch_id = None
        cmds = []
        try:
            if job_id and is_cancelled(job_id):
                raise CancelException("Cancelled")
            cr = safe_request(session, f"{portal_url}{api_path}",
                              params={"type": "itv", "action": "get_all_channels"},
                              headers=auth_headers, cookies=cookies,
                              timeout=10, verify=False)
            if cr.status_code == 200:
                cj = (cr.json() or {}).get("js", {}) or {}
                data_list = []
                if isinstance(cj, dict):
                    res["channels_count"] = int(
                        cj.get("total_items") or len(cj.get("data", [])) or 0)
                    data_list = cj.get("data", []) or []
                elif isinstance(cj, list):
                    res["channels_count"] = len(cj)
                    data_list = cj
                # v5.9.2 FIX: عينة موزّعة على كامل القائمة بدل أول 20 قناة فقط
                sample = []
                if data_list:
                    step = max(1, len(data_list) // 15)
                    i = 0
                    while i < len(data_list) and len(sample) < 20:
                        sample.append(data_list[i])
                        i += step
                for ch in sample:
                    if isinstance(ch, dict) and first_ch_id is None and ch.get("id"):
                        first_ch_id = ch.get("id")
                    c = isinstance(ch, dict) and ch.get("cmd") or None
                    if c and ("http" in str(c) or str(c).startswith("ffrt")) and c not in cmds:
                        cmds.append(str(c))
                    if len(cmds) >= 10:
                        break
                if cmds:
                    stream_diag = []
                    stream_result = _check_mac_stream(
                        session, portal_url, api_path,
                        auth_headers, cookies, cmds, job_id, diag=stream_diag)
                    # لا نعتبر transcoder_detected نجاحاً
                    if stream_result == "transcoder_detected":
                        res["stream_ok"] = None  # غير مؤكد
                        res["rescue_method"] = (res.get("rescue_method", "") + " transcoder_detected").strip()
                    else:
                        res["stream_ok"] = stream_result
                    if stream_diag:
                        res["diag"] = (res["diag"] + " | stream: " + ",".join(stream_diag))[:500]
        except CancelException:
            raise
        except Exception:
            pass

        # Module detection
        try:
            if job_id and is_cancelled(job_id):
                raise CancelException("Cancelled")
            mods = _detect_mac_modules(session, portal_url, api_path,
                                       auth_headers, cookies, first_ch_id, job_id)
            mods["live"] = True
            res["modules"] = mods
        except CancelException:
            raise
        except Exception:
            pass

        # VOD / Series counters
        try:
            if res["modules"].get("vod"):
                res["vod_count"] = _fetch_mac_vod_count(
                    session, portal_url, api_path, auth_headers, cookies, job_id)
        except CancelException:
            raise
        except Exception:
            res["vod_count"] = 0
        try:
            if res["modules"].get("series"):
                res["series_count"] = _fetch_mac_series_count(
                    session, portal_url, api_path, auth_headers, cookies, job_id)
        except CancelException:
            raise
        except Exception:
            res["series_count"] = 0

        # Enhancement Layer
        if res["auth_valid"]:
            host, port, scheme = None, None, None
            try:
                host, port, scheme = _extract_host_port(portal_url)
            except Exception:
                pass

            # Bandwidth — v5.9.2 FIX: بهوية جلسة الـ STB الكاملة
            # cache key يشمل الماك لمنع الخلط
            try:
                if res["stream_ok"] is True and cmds:
                    bw_url = _get_mac_bandwidth_url(session, portal_url, api_path,
                                                    auth_headers, cookies, cmds)
                    if bw_url:
                        cache_key = (host or portal_url, mac_address, "mac")
                        stb_bw_headers = {k: v for k, v in auth_headers.items()
                                          if k.lower() not in ("accept-encoding", "connection")}
                        res["bandwidth_kbps"] = _measure_bandwidth(
                            bw_url, cache_key, headers=stb_bw_headers, cookies=cookies)
            except Exception:
                res["bandwidth_kbps"] = 0.0

            # GeoIP
            try:
                res["geo"] = _geoip_lookup(host)
            except Exception:
                res["geo"] = None

            # SSL
            try:
                if scheme == "https" or port == 443:
                    res["ssl_info"] = _ssl_check(host, port or 443)
                else:
                    res["ssl_info"] = None
            except Exception:
                res["ssl_info"] = None

            # M3U analysis not applicable for MAC
            res["m3u_analysis"] = None

            # Score
            try:
                res["score"] = _compute_score(res)
            except Exception:
                res["score"] = 0

        return sanitize_result(res)

    except CancelException:
        return sanitize_result({
            "server": portal_url,
            "username": f"MAC: {mac_address}",
            "password": "Stalker Portal",
            "auth_valid": False,
            "error": "CANCELLED",
            "failure_reason": "CANCELLED",
            "is_online": False,
            "status": "Cancelled",
            "api_ms": 0,
            "modules": {"live": False, "vod": False, "series": False, "epg": False},
            "diag": "",
            "bandwidth_kbps": 0.0,
            "score": 0,
            "geo": None,
            "ssl_info": None,
            "m3u_analysis": None,
            "vod_count": 0,
            "series_count": 0,
            "channels_count": 0,
            "exp_date": "N/A",
            "created_date": "N/A",
            "max_connections": "N/A",
            "active_connections": "0",
            "m3u_url": "",
            "stream_ok": None,
            "api_path": "",
            "rescued": False,
            "rescue_method": ""
        })

    except Exception as outer_exc:
        return sanitize_result({
            "server": portal_url,
            "username": f"MAC: {mac_address}",
            "password": "Stalker Portal",
            "auth_valid": False,
            "is_trial": False,
            "sub_type": "",
            "error": f"CRITICAL: {str(outer_exc)[:200]}",
            "failure_reason": "CRITICAL",
            "is_online": False,
            "status": "Error",
            "api_ms": 9999.0,
            "modules": {"live": False, "vod": False, "series": False, "epg": False},
            "diag": "",
            "bandwidth_kbps": 0.0,
            "score": 0,
            "geo": None,
            "ssl_info": None,
            "m3u_analysis": None,
            "vod_count": 0,
            "series_count": 0,
            "channels_count": 0,
            "exp_date": "N/A",
            "created_date": "N/A",
            "max_connections": "N/A",
            "active_connections": "0",
            "m3u_url": "",
            "stream_ok": None,
            "api_path": "",
            "rescued": False,
            "rescue_method": ""
        })

# ══════════════════════════════════════════════════════════════
#  JSON Safe Serializer
# ══════════════════════════════════════════════════════════════

def json_serial(obj):
    if isinstance(obj, datetime):
        return obj.isoformat()
    if isinstance(obj, set):
        return list(obj)
    if isinstance(obj, bytes):
        return obj.decode('utf-8', errors='ignore')
    try:
        return str(obj)
    except Exception:
        return "<unserializable>"

# ══════════════════════════════════════════════════════════════
#  Routes
# ══════════════════════════════════════════════════════════════

@app.route("/")
def index():
    return render_template("index.html")

@app.route("/check", methods=["POST"])
def check_servers():
    auth_error = require_api_key()
    if auth_error:
        return auth_error
    _cleanup_old_jobs()
    _cleanup_caches()
    data        = request.json
    scan_type   = data.get("type", "xtream")
    servers_raw = data.get("servers", "")
    creds_raw   = data.get("creds", "")
    m3u_raw     = data.get("m3u", "")
    mac_portal  = data.get("macPortal", "")
    mac_list    = data.get("macs", "")
    m3u_analysis_enabled = bool(data.get("m3u_analysis_enabled", False))

    tasks = []

    # ── تحديد القوائم مع تطبيق حدود الإدخال ──
    if scan_type == "xtream":
        servers_list = list(dict.fromkeys(
            s.strip().lstrip('/') for s in servers_raw.split("\n") if s.strip()
        ))[:MAX_INPUT_LINES]
        creds_lines  = list(dict.fromkeys(
            c.strip() for c in creds_raw.split("\n") if ":" in c
        ))[:MAX_INPUT_LINES]
        for s in servers_list:
            for line in creds_lines:
                try:
                    u, p = line.split(":", 1)
                    tasks.append(("xtream", s, u.strip(), p.strip()))
                except Exception:
                    continue
    elif scan_type == "m3u":
        for line in [l.strip() for l in m3u_raw.split("\n") if l.strip()][:MAX_INPUT_LINES]:
            parsed = parse_m3u_line(line)
            if parsed:
                s, u, p = parsed
                tasks.append(("xtream", s, u, p))
    elif scan_type == "mac":
        portals = list(dict.fromkeys(
            normalize_portal_url(p) for p in mac_portal.split("\n") if p.strip()
        ))[:MAX_INPUT_LINES]
        macs    = list(dict.fromkeys(
            m.strip() for m in mac_list.split("\n") if m.strip()
        ))[:MAX_INPUT_LINES]
        for portal in portals:
            for mac in macs:
                tasks.append(("mac", portal, mac, ""))

    # ── تطبيق حد المهام ──
    if len(tasks) > MAX_TASKS:
        tasks = tasks[:MAX_TASKS]

    if not tasks:
        return jsonify({"error": "الرجاء إدخال بيانات صحيحة."})

    job_id = str(uuid.uuid4())[:8]
    q      = queuelib.Queue()

    with _JOBS_LOCK:
        _JOBS[job_id] = {"q": q, "total": len(tasks), "done": 0, "ts": time.time()}

    def _worker():
        try:
            def _run_xtream(a, b, c):
                return test_single_server(a, b, c, m3u_analysis_enabled, job_id)
            def _run_mac(a, b, c):
                return test_mac_portal(a, b, job_id)
            fn_map = {"xtream": _run_xtream, "mac": _run_mac}
            with ThreadPoolExecutor(max_workers=20) as ex:
                fmap = {}
                for t in tasks:
                    if is_cancelled(job_id):
                        break
                    t_type, a, b, c = t
                    f = ex.submit(fn_map[t_type], a, b, c)
                    fmap[f] = None
                for f in as_completed(fmap):
                    if is_cancelled(job_id):
                        break
                    try:
                        result = f.result()
                        with _JOBS_LOCK:
                            if job_id in _JOBS:
                                _JOBS[job_id]["done"] += 1
                        q.put(result)
                    except Exception as e:
                        q.put({
                            "error": f"Worker future error: {str(e)[:100]}",
                            "server": "unknown",
                            "username": "unknown",
                            "failure_reason": "FUTURE_ERROR"
                        })
        except Exception as worker_exc:
            q.put({"error": f"Worker crash: {str(worker_exc)[:100]}", "failure_reason": "WORKER_CRASH"})
        finally:
            clear_cancel(job_id)
            q.put(None)

    threading.Thread(target=_worker, daemon=True).start()
    return jsonify({"job_id": job_id, "total": len(tasks)})

@app.route("/cancel/<job_id>", methods=["POST"])
def cancel_job(job_id):
    auth_error = require_api_key()
    if auth_error:
        return auth_error
    with _JOBS_LOCK:
        if job_id not in _JOBS:
            return jsonify({"error": "job not found"}), 404
    set_cancel(job_id)
    return jsonify({"status": "cancelling"})

@app.route("/stream/<job_id>")
def stream_results(job_id):
    auth_error = require_api_key()
    if auth_error:
        return auth_error
    with _JOBS_LOCK:
        job = _JOBS.get(job_id)

    if not job:
        def _err():
            yield f'data: {json.dumps({"error": "job_not_found"})}\n\n'
        return Response(stream_with_context(_err()),
                        mimetype="text/event-stream")

    def _gen():
        q = job["q"]
        while True:
            try:
                item = q.get(timeout=30)
            except queuelib.Empty:
                yield 'data: {"ping":1}\n\n'
                continue
            if item is None:
                yield f'data: {json.dumps({"__done__": True})}\n\n'
                with _JOBS_LOCK:
                    _JOBS.pop(job_id, None)
                break
            try:
                yield f"data: {json.dumps(item, default=json_serial)}\n\n"
            except Exception as ser_exc:
                yield f'data: {json.dumps({"error": f"Serialization error: {str(ser_exc)[:50]}"})}\n\n'

    return Response(
        stream_with_context(_gen()),
        mimetype="text/event-stream",
        headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"}
    )

if __name__ == "__main__":
    app.run(
        host="0.0.0.0",
        port=int(os.environ.get("PORT", 5000)),
        debug=False,
        threaded=True
    )
