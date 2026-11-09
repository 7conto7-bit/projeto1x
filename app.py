# -*- coding: utf-8 -*-
import os
import re
import hmac
import json
import time
import struct
import threading
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone, timedelta
from functools import wraps

import requests
from flask import Flask, request, render_template_string, jsonify, Response, redirect, url_for

app = Flask(__name__)

# Fuso horário de Brasília (UTC-3)
BRT = timezone(timedelta(hours=-3))
GRAPH_API_VERSION = "v21.0"

# ==============================================================================
# PARÂMETROS DE SEGURANÇA OPERACIONAL (ANTI-CHECKPOINT & ANTI-CANIBALIZAÇÃO)
# ==============================================================================
# Intervalo mínimo após o 1º lote do dia (3h30 = 210 min, igual à operação manual de 3-4h)
MIN_GAP_AFTER_BATCH1_MINS = 210
# Intervalo de descanso longo após 2 lotes no dia (12h = 720 min, igual à operação manual de 12-24h)
LONG_REST_AFTER_BATCH2_MINS = 720
# Descanso de emergência quando um lote sofre queda brusca de alcance (<500 views/post)
THROTTLE_PROTECTION_REST_MINS = 1080  # 18 horas
# Limite seguro de posts em 24h por conta para não acionar filtro anti-spam da Meta
SAFE_DAILY_POSTS_CAP = 20
# Limite máximo de lotes em uma janela de 24h
MAX_BATCHES_PER_24H = 2

# ==============================================================================
# CONFIGURAÇÃO UPSTASH REDIS (PERSISTÊNCIA DEFINITIVA NA VERCEL)
# ==============================================================================
UPSTASH_URL = os.environ.get("UPSTASH_REDIS_REST_URL", "").strip().rstrip("/")
UPSTASH_TOKEN = os.environ.get("UPSTASH_REDIS_REST_TOKEN", "").strip()
REDIS_STATE_KEY = "ig_monitor:state_v1"

# Intervalo mínimo entre leituras diretas no Redis (em segundos) para poupar comandos
REDIS_READ_TTL = 300  # 5 minutos

# ==============================================================================
# ARQUIVOS .JSON (FALLBACK LOCAL + /TMP NA VERCEL)
# ==============================================================================
BASE_DIR = os.path.abspath(os.path.dirname(__file__))
BUNDLED_MONITOR_FILE = os.path.join(BASE_DIR, "contas_monitoradas.json")
CODIGO1_ACCOUNTS_FILE = os.path.join(BASE_DIR, "contas_conectadas.json")

if os.environ.get("VERCEL") or not os.access(BASE_DIR, os.W_OK):
    RUNTIME_ACCOUNTS_FILE = os.path.join("/tmp", "contas_monitoradas.json")
else:
    RUNTIME_ACCOUNTS_FILE = BUNDLED_MONITOR_FILE

ACCOUNTS_LOCK = threading.RLock()
SYNC_LOCK = threading.Lock()

# Cache em memória do processo
MEMORY_CACHE_ACCOUNTS = {}
MEMORY_CUSTOM_TOKENS = {}  # uid_str -> access_token (contas adicionadas via painel web)
MEMORY_DELETED_IDS = set()
MEMORY_LAST_SYNC_TS = 0.0
MEMORY_LAST_SYNC_STR = "Ainda não sincronizado"
MEMORY_GLOBAL_PEAK_MIN = 0.0
MEMORY_GLOBAL_PEAK_HOUR = 0.0
LAST_REDIS_FETCH_TS = 0.0

# Cache em memória para durações de vídeos já descobertas (media_id -> float seconds)
MEDIA_DURATION_CACHE = {}

# Flag que garante que o estado existente no Upstash foi lido com sucesso nesta instância
REDIS_BOOTSTRAPPED = False


def format_number_br(val):
    if val is None or val == "":
        return "—"
    try:
        n = int(round(float(val)))
        return f"{n:,}".replace(",", ".")
    except Exception:
        return str(val)


def format_rate_br(val):
    """Formata taxas de visualizações por minuto/hora no padrão brasileiro."""
    if val is None or val == "":
        return "0"
    try:
        num = float(val)
        if num <= 0:
            return "0"
        if num >= 100:
            n = int(round(num))
            return f"{n:,}".replace(",", ".")
        if num >= 10:
            s = f"{num:,.1f}".replace(",", "X").replace(".", ",").replace("X", ".")
            return s[:-2] if s.endswith(",0") else s
        s = f"{num:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")
        if s.endswith(",00"):
            return s[:-3]
        if s.endswith("0") and "," in s:
            return s[:-1]
        return s
    except Exception:
        return str(val)


def format_duration_sec(val):
    """Formata a duração do vídeo em segundos (ex: '15s')."""
    try:
        sec = float(val or 0)
        if sec <= 0:
            return "— s"
        sec_int = int(round(sec))
        return f"{sec_int}s"
    except Exception:
        return "— s"


app.jinja_env.filters["fmt_num"] = format_number_br
app.jinja_env.filters["fmt_rate"] = format_rate_br
app.jinja_env.filters["fmt_dur"] = format_duration_sec


# ==============================================================================
# UTILITÁRIOS DE CONVERSÃO, EXTRAÇÃO DE DURAÇÃO MP4, TIMESTAMPS E VELOCIDADE
# ==============================================================================

def _safe_int(val):
    try:
        if val is None or val == "":
            return 0
        if isinstance(val, str):
            val = val.replace(".", "").replace(",", "").strip()
        return max(0, int(float(val)))
    except Exception:
        return 0


def _safe_float(val):
    try:
        if val is None or val == "":
            return 0.0
        if isinstance(val, str):
            val = val.replace(",", ".").strip()
        return max(0.0, float(val))
    except Exception:
        return 0.0


def _extract_quota_from_detail(acc_dict):
    """Extrai o uso da cota de 24h (ex: 33 de 'Cota 24h: 33/100 usados') caso não esteja salvo em campo próprio."""
    if not isinstance(acc_dict, dict):
        return 0
    q_direct = _safe_int(acc_dict.get("quota_usage_24h"))
    if q_direct > 0:
        return q_direct
    detail = str(acc_dict.get("account_status_detail") or "")
    m = re.search(r"Cota 24h:\s*(\d+)\s*/\s*(\d+)", detail)
    if m:
        return _safe_int(m.group(1))
    return 0


def _parse_mp4_mvhd_duration(data_bytes):
    """
    Procura a assinatura do átomo 'mvhd' nos bytes iniciais/finais de um arquivo MP4
    e extrai a duração exata em segundos a partir de timescale e duration.
    """
    if not data_bytes:
        return 0.0
    idx = 0
    while True:
        pos = data_bytes.find(b"mvhd", idx)
        if pos == -1 or pos + 24 > len(data_bytes):
            break
        version = data_bytes[pos + 4]
        try:
            if version == 0 and pos + 24 <= len(data_bytes):
                timescale, duration = struct.unpack(">II", data_bytes[pos + 16:pos + 24])
                if timescale > 0 and 0 < (duration / timescale) < 7200:
                    return round(duration / timescale, 1)
            elif version == 1 and pos + 36 <= len(data_bytes):
                timescale, duration = struct.unpack(">IQ", data_bytes[pos + 24:pos + 36])
                if timescale > 0 and 0 < (duration / timescale) < 7200:
                    return round(duration / timescale, 1)
        except Exception:
            pass
        idx = pos + 4
    return 0.0


def _probe_video_duration_seconds(media_item):
    """
    Obtém a duração em segundos de um Reel/Vídeo sem precisar baixar o vídeo inteiro.
    """
    if not isinstance(media_item, dict):
        return 0.0

    mid = str(media_item.get("id") or "").strip()
    if mid and mid in MEDIA_DURATION_CACHE and MEDIA_DURATION_CACHE[mid] > 0:
        return MEDIA_DURATION_CACHE[mid]

    for key in ("duration_sec", "video_duration", "duration"):
        val = _safe_float(media_item.get(key))
        if val > 0:
            if mid:
                MEDIA_DURATION_CACHE[mid] = round(val, 1)
            return round(val, 1)

    media_type = str(media_item.get("media_type") or media_item.get("media_product_type") or "").upper()
    if "IMAGE" in media_type or "CAROUSEL" in media_type:
        return 0.0

    media_url = (media_item.get("media_url") or "").strip()
    if not media_url:
        return 0.0

    try:
        r = requests.get(
            media_url,
            headers={"Range": "bytes=0-65535", "User-Agent": "Mozilla/5.0"},
            timeout=5,
            stream=True
        )
        chunk = r.raw.read(65536) if hasattr(r, "raw") else r.content[:65536]
        r.close()
        dur = _parse_mp4_mvhd_duration(chunk)
        if dur > 0:
            if mid:
                MEDIA_DURATION_CACHE[mid] = dur
            return dur

        content_range = r.headers.get("Content-Range", "")
        if "/" in content_range:
            total_size = _safe_int(content_range.split("/")[-1])
            if total_size > 65536:
                start_byte = max(0, total_size - 65536)
                r_tail = requests.get(
                    media_url,
                    headers={"Range": f"bytes={start_byte}-{total_size - 1}", "User-Agent": "Mozilla/5.0"},
                    timeout=5
                )
                dur_tail = _parse_mp4_mvhd_duration(r_tail.content)
                if dur_tail > 0:
                    if mid:
                        MEDIA_DURATION_CACHE[mid] = dur_tail
                    return dur_tail
    except Exception:
        pass

    return 0.0


def _parse_br_datetime_to_ts(dt_str):
    if not dt_str or not isinstance(dt_str, str):
        return None
    s = dt_str.strip()
    for fmt in ("%d/%m/%Y %H:%M:%S", "%d/%m/%Y %H:%M"):
        try:
            dt = datetime.strptime(s, fmt).replace(tzinfo=BRT)
            return dt.timestamp()
        except Exception:
            continue
    return None


def _parse_ig_post_timestamp_to_brt(ts_str):
    """
    Converte o timestamp dos posts do Instagram (UTC) para o fuso de Brasília (BRT / UTC-3).
    """
    if not ts_str or not isinstance(ts_str, str):
        return None, "—"
    s = ts_str.strip()
    now_ts = time.time()

    if "T" in s or "+" in s:
        try:
            clean_iso = s.replace("+0000", "+00:00").replace("Z", "+00:00")
            dt_utc = datetime.fromisoformat(clean_iso)
            if dt_utc.tzinfo is None:
                dt_utc = dt_utc.replace(tzinfo=timezone.utc)
            dt_brt = dt_utc.astimezone(BRT)
            return dt_brt.timestamp(), dt_brt.strftime("%d/%m %H:%M")
        except Exception:
            pass

    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M"):
        try:
            dt_naive = datetime.strptime(s[:19].strip(), fmt)
            dt_utc = dt_naive.replace(tzinfo=timezone.utc)
            dt_brt = dt_utc.astimezone(BRT)
            ts_val = dt_brt.timestamp()
            if ts_val > now_ts + 600:
                dt_brt = dt_naive.replace(tzinfo=BRT)
                ts_val = dt_brt.timestamp()
            return ts_val, dt_brt.strftime("%d/%m %H:%M")
        except Exception:
            continue

    for fmt in ("%d/%m/%Y %H:%M:%S", "%d/%m/%Y %H:%M", "%d/%m %H:%M"):
        try:
            dt_brt = datetime.strptime(s, fmt).replace(tzinfo=BRT)
            return dt_brt.timestamp(), dt_brt.strftime("%d/%m %H:%M")
        except Exception:
            continue

    return None, s


def _format_age_human(seconds):
    if seconds is None or seconds < 0:
        return "agora"
    mins = int(seconds // 60)
    if mins < 1:
        return "agora"
    if mins < 60:
        return f"{mins}min"
    hours = mins // 60
    rem_mins = mins % 60
    if hours < 24:
        return f"{hours}h{rem_mins:02d}m" if rem_mins else f"{hours}h"
    days = hours // 24
    rem_hours = hours % 24
    return f"{days}d {rem_hours}h" if rem_hours else f"{days}d"


def _merge_views_history(old_hist, new_hist, current_views=0, current_ts=None):
    by_bucket = {}
    for src in (old_hist, new_hist):
        if not isinstance(src, list):
            continue
        for item in src:
            if not isinstance(item, dict):
                continue
            ts = _safe_float(item.get("ts"))
            v = _safe_int(item.get("views"))
            if ts > 0 and v >= 0:
                bucket = int(ts // 30)
                if bucket not in by_bucket or v > by_bucket[bucket]["views"]:
                    by_bucket[bucket] = {"ts": round(ts, 2), "views": v}

    if current_ts and current_ts > 0 and current_views > 0:
        bucket = int(current_ts // 30)
        if bucket not in by_bucket or current_views > by_bucket[bucket]["views"]:
            by_bucket[bucket] = {"ts": round(float(current_ts), 2), "views": int(current_views)}

    ordered = sorted(by_bucket.values(), key=lambda x: x["ts"])

    running_max = 0
    cleaned = []
    for pt in ordered:
        running_max = max(running_max, _safe_int(pt.get("views")))
        cleaned.append({"ts": pt["ts"], "views": running_max})

    if len(cleaned) > 288:
        cleaned = cleaned[-288:]
    return cleaned


def _compute_account_velocity_rates(acc_dict):
    if not isinstance(acc_dict, dict):
        return 0.0, 0.0

    hist = acc_dict.get("views_history")
    if not isinstance(hist, list) or len(hist) < 2:
        return 0.0, 0.0

    now_ts = time.time()
    latest = hist[-1]
    latest_ts = _safe_float(latest.get("ts"))
    latest_views = _safe_int(latest.get("views"))

    if latest_ts <= 0 or (now_ts - latest_ts) > 7200:
        return 0.0, 0.0

    ref_min_pt = None
    for pt in reversed(hist[:-1]):
        dt_sec = latest_ts - _safe_float(pt.get("ts"))
        if dt_sec >= 45:
            ref_min_pt = pt
            break
    if ref_min_pt is None:
        ref_min_pt = hist[0]

    dt_min_sec = latest_ts - _safe_float(ref_min_pt.get("ts"))
    dv_min = max(0, latest_views - _safe_int(ref_min_pt.get("views")))
    current_vpm = 0.0
    if 30 <= dt_min_sec <= 2700 and dv_min > 0:
        current_vpm = dv_min / (dt_min_sec / 60.0)

    points_last_hour = [
        pt for pt in hist[:-1]
        if 60 <= (latest_ts - _safe_float(pt.get("ts"))) <= 3900
    ]
    if points_last_hour:
        ref_hour_pt = points_last_hour[0]
    else:
        ref_hour_pt = ref_min_pt

    dt_hour_sec = latest_ts - _safe_float(ref_hour_pt.get("ts"))
    dv_hour = max(0, latest_views - _safe_int(ref_hour_pt.get("views")))
    current_vph = 0.0
    if dt_hour_sec >= 30 and dv_hour > 0:
        if dt_hour_sec >= 3300:
            current_vph = dv_hour / (dt_hour_sec / 3600.0)
        else:
            projected_hour = dv_hour / (dt_hour_sec / 3600.0)
            current_vph = max(float(dv_hour), projected_hour)

    return round(current_vpm, 2), round(current_vph, 2)


def _compute_global_peaks_from_accounts(accounts_dict, prev_peak_min=0.0, prev_peak_hour=0.0):
    """
    Calcula o recorde de views/min e views/hora de TODAS as contas somadas.
    Combina o pico histórico persistido com a soma atual das taxas de todas as contas.
    """
    if not isinstance(accounts_dict, dict):
        return round(_safe_float(prev_peak_min), 2), round(_safe_float(prev_peak_hour), 2)

    sum_cur_min = 0.0
    sum_cur_hour = 0.0

    for acc in accounts_dict.values():
        if isinstance(acc, dict):
            sum_cur_min += _safe_float(acc.get("views_per_min"))
            sum_cur_hour += _safe_float(acc.get("views_per_hour"))

    best_min = max(_safe_float(prev_peak_min), MEMORY_GLOBAL_PEAK_MIN, sum_cur_min)
    best_hour = max(_safe_float(prev_peak_hour), MEMORY_GLOBAL_PEAK_HOUR, sum_cur_hour)
    return round(best_min, 2), round(best_hour, 2)


# ==============================================================================
# DETECTOR DE LOTES (CLUSTERS DE POSTAGEM) E MOTOR DE INTELIGÊNCIA ANTI-QUEDA
# ==============================================================================

def _group_posts_into_batches(posts_with_ts, max_gap_seconds=2700):
    """
    Agrupa os vídeos da conta em 'Lotes' reais (qualquer sequência de vídeos onde o intervalo
    entre um vídeo e o seguinte foi <= 45 minutos pertence ao mesmo lote).
    Retorna a lista de lotes ordenada do mais recente para o mais antigo.
    """
    if not posts_with_ts:
        return []

    chronological = sorted(posts_with_ts, key=lambda x: x["ts"])
    batches = []
    current_batch = [chronological[0]]

    for item in chronological[1:]:
        prev_ts = current_batch[-1]["ts"]
        if (item["ts"] - prev_ts) <= max_gap_seconds:
            current_batch.append(item)
        else:
            batches.append(current_batch)
            current_batch = [item]
    if current_batch:
        batches.append(current_batch)

    summary_batches = []
    for b in reversed(batches):
        b_views = sum(x["views"] for x in b)
        b_gain = sum(x["gain"] for x in b)
        b_count = len(b)
        summary_batches.append({
            "start_ts": b[0]["ts"],
            "end_ts": b[-1]["ts"],
            "count": b_count,
            "total_views": b_views,
            "avg_views": int(round(b_views / max(1, b_count))),
            "max_views": max(x["views"] for x in b),
            "recent_gain": b_gain
        })
    return summary_batches


def _analyze_account_intelligence(acc_dict):
    """
    Motor de Decisão Operacional v2 (Anti-Checkpoint + Anti-Canibalização).
    """
    if not isinstance(acc_dict, dict):
        return {}

    now_ts = time.time()
    status_badge = acc_dict.get("account_status_badge", "success")
    status_text = str(acc_dict.get("account_status") or "Ativa")
    v_min = _safe_float(acc_dict.get("views_per_min"))
    v_hour = _safe_float(acc_dict.get("views_per_hour"))
    peak_min = max(_safe_float(acc_dict.get("peak_views_per_min")), v_min)
    peak_hour = max(_safe_float(acc_dict.get("peak_views_per_hour")), v_hour)
    total_views = _safe_int(acc_dict.get("total_views"))
    followers = _safe_int(acc_dict.get("followers_count"))
    media_count = _safe_int(acc_dict.get("media_count"))
    quota_24h = _extract_quota_from_detail(acc_dict)

    activity_index_pct = 0.0
    if peak_hour > 0:
        activity_index_pct = round(min(100.0, (v_hour / peak_hour) * 100.0), 1)

    hourly_avg_vpm = (v_hour / 60.0) if v_hour > 0 else 0.0
    accel_ratio = round(v_min / hourly_avg_vpm, 2) if hourly_avg_vpm >= 1.0 else (1.0 if v_min > 0 else 0.0)

    if v_min <= 0.5:
        trend_label = "💤 Parada"
        trend_color = "#64748b"
    elif accel_ratio >= 1.18:
        trend_label = f"📈 Acelerando ({accel_ratio:.1f}x)"
        trend_color = "#4ade80"
    elif accel_ratio <= 0.78:
        trend_label = f"📉 Esfriando ({accel_ratio:.1f}x)"
        trend_color = "#fbbf24"
    else:
        trend_label = f"⚡ Estável ({accel_ratio:.1f}x)"
        trend_color = "#38bdf8"

    posts = acc_dict.get("posts_list") if isinstance(acc_dict.get("posts_list"), list) else []
    newest_post_ts = None
    recent_batch_count_3h = 0
    recent_batch_views_3h = 0
    posts_last_24h_count = 0
    posts_last_12h_count = 0
    hits_10k = 0
    virals_100k = 0
    dead_posts_count = 0
    top_post_views = 0
    winning_hours_counter = Counter()
    posts_with_ts_for_clustering = []

    for p in posts:
        if not isinstance(p, dict):
            continue
        p_views = _safe_int(p.get("views"))
        gain_recent = _safe_int(p.get("recent_views_gain"))
        top_post_views = max(top_post_views, p_views)
        if p_views >= 10000:
            hits_10k += 1
        if p_views >= 100000:
            virals_100k += 1

        raw_ts = p.get("timestamp_raw") or p.get("timestamp") or ""
        p_ts, brt_str = _parse_ig_post_timestamp_to_brt(raw_ts)
        p["timestamp_brt"] = brt_str

        age_sec = max(60.0, now_ts - p_ts) if p_ts else None
        age_hours = (age_sec / 3600.0) if age_sec else None
        p["age_human"] = _format_age_human(age_sec) if age_sec else "—"

        if p_ts:
            posts_with_ts_for_clustering.append({
                "id": p.get("id"),
                "ts": p_ts,
                "views": p_views,
                "gain": gain_recent
            })
            if p_views >= 10000:
                hr_brt = datetime.fromtimestamp(p_ts, tz=BRT).hour
                winning_hours_counter[hr_brt] += (3 if p_views >= 100000 else 1)

            if newest_post_ts is None or p_ts > newest_post_ts:
                newest_post_ts = p_ts
            if age_sec <= 10800:  # 3h
                recent_batch_count_3h += 1
                recent_batch_views_3h += p_views
            if age_sec <= 43200:  # 12h
                posts_last_12h_count += 1
            if age_sec <= 86400:  # 24h
                posts_last_24h_count += 1

        if p_views >= 100000:
            p["diag_label"] = "🔥 Megaviral (+100k)"
            p["diag_badge"] = "success"
        elif p_views >= 25000:
            p["diag_label"] = "🚀 Hit Validado"
            p["diag_badge"] = "info"
        elif age_hours is not None and age_hours <= 2.0:
            if p_views >= 450 or gain_recent >= 80:
                p["diag_label"] = "⚡ Tração Inicial Forte"
                p["diag_badge"] = "success"
            else:
                p["diag_label"] = "⏳ Em Maturação (<2h)"
                p["diag_badge"] = "warning"
        elif age_hours is not None and age_hours > 2.0 and p_views < 400:
            p["diag_label"] = "💀 Morte Súbita (<400)"
            p["diag_badge"] = "error"
            dead_posts_count += 1
        elif p_views >= 5000:
            p["diag_label"] = "✅ Entrega Saudável"
            p["diag_badge"] = "info"
        else:
            p["diag_label"] = "😐 Alcance Baixo"
            p["diag_badge"] = "warning"

    batches = _group_posts_into_batches(posts_with_ts_for_clustering)
    batches_24h = [b for b in batches if (now_ts - b["end_ts"]) <= 86400]
    batches_12h = [b for b in batches if (now_ts - b["end_ts"]) <= 43200]
    batches_24h_count = len(batches_24h)
    batches_12h_count = len(batches_12h)

    last_batch = batches[0] if batches else None
    last_batch_count = last_batch["count"] if last_batch else 0
    last_batch_views = last_batch["total_views"] if last_batch else 0
    last_batch_avg_views = last_batch["avg_views"] if last_batch else 0
    last_batch_gain = last_batch["recent_gain"] if last_batch else 0

    older_posts = [
        x["views"] for x in posts_with_ts_for_clustering
        if not last_batch or x["ts"] < last_batch["start_ts"]
    ]
    historical_avg_views = int(round(sum(older_posts) / len(older_posts))) if older_posts else 0

    effective_posts_24h = max(posts_last_24h_count, quota_24h)

    total_listed_posts = len(posts)
    hit_rate_10k_pct = round((hits_10k / total_listed_posts) * 100.0, 1) if total_listed_posts > 0 else 0.0
    dead_rate_pct = round((dead_posts_count / total_listed_posts) * 100.0, 1) if total_listed_posts > 0 else 0.0
    top_post_share_pct = round((top_post_views / total_views) * 100.0, 1) if total_views > 0 else 0.0
    followers_per_1k_views = round((followers / total_views) * 1000.0, 2) if total_views > 0 else 0.0

    best_window_str = "Sem dados suficientes"
    if winning_hours_counter:
        best_hr = winning_hours_counter.most_common(1)[0][0]
        prep_hr = (best_hr - 1) % 24
        end_hr = (best_hr + 2) % 24
        best_window_str = f"Pico {best_hr:02d}h–{end_hr:02d}h (Postar ~{prep_hr:02d}:15)"
    elif total_listed_posts > 0:
        best_window_str = "Em calibração (testar 11h / 18h)"

    mins_since_last_post = None
    last_post_age_str = "Sem posts"
    if newest_post_ts:
        mins_since_last_post = max(0, int((now_ts - newest_post_ts) // 60))
        last_post_age_str = f"há {_format_age_human(now_ts - newest_post_ts)}"

    last_batch_throttled = False
    if last_batch and mins_since_last_post is not None and mins_since_last_post >= 120:
        if last_batch_avg_views < 450:
            last_batch_throttled = True
        elif historical_avg_views >= 8000 and last_batch_avg_views < 1300 and last_batch_gain < 60:
            last_batch_throttled = True

    action_code = "WAIT"
    action_badge = "info"
    action_title = "AGUARDAR"
    action_detail = ""
    priority_score = 0
    can_post_now = False
    recommended_batch_size = 0

    if status_badge == "error" or "Caiu" in status_text or "Desconectada" in status_text or "Bloqueada" in status_text:
        action_code = "RECONNECT"
        action_badge = "error"
        action_title = "🔌 RECONECTAR CONTA / TOKEN"
        action_detail = "Sessão inválida ou checkpoint no Instagram. Faça login no aparelho e aguarde 12h antes de voltar a postar."
        priority_score = -100
        can_post_now = False

    elif status_text == "Limite Diário Atingido":
        action_code = "QUOTA_FULL"
        action_badge = "warning"
        action_title = "🛑 COTA 24H DA META ATINGIDA"
        action_detail = "Limite oficial atingido. Aguarde a liberação da janela de 24h."
        priority_score = -50
        can_post_now = False

    elif total_listed_posts >= 15 and total_views < 15000 and v_min < 3.0:
        action_code = "PAUSE_ZOMBIE"
        action_badge = "error"
        action_title = "🛑 PAUSAR 48H (CONTA TRAVADA)"
        action_detail = (
            f"Média de {int(total_views / max(1, total_listed_posts))} views/post ({dead_posts_count} vídeos <400 views). "
            f"Não gaste criativos bons aqui; dê 48h de descanso."
        )
        priority_score = 5
        can_post_now = False

    elif last_batch_throttled and mins_since_last_post is not None and mins_since_last_post < THROTTLE_PROTECTION_REST_MINS:
        wait_left_h = round((THROTTLE_PROTECTION_REST_MINS - mins_since_last_post) / 60.0, 1)
        action_code = "THROTTLE_REST"
        action_badge = "error"
        action_title = f"🛡️ FREIO ANTI-QUEDA (DESCANSAR {wait_left_h}h)"
        action_detail = (
            f"O último lote ({last_batch_count} vídeos {last_post_age_str}) caiu para média de "
            f"{format_number_br(last_batch_avg_views)} views/post. Forçar novo lote agora causa Checkpoint! "
            f"Deixe a conta descansar pelo menos 18h."
        )
        priority_score = 10
        can_post_now = False

    elif (
        (batches_24h_count >= MAX_BATCHES_PER_24H or effective_posts_24h >= SAFE_DAILY_POSTS_CAP)
        and mins_since_last_post is not None
        and mins_since_last_post < LONG_REST_AFTER_BATCH2_MINS
    ):
        wait_left_mins = max(30, LONG_REST_AFTER_BATCH2_MINS - mins_since_last_post)
        wait_left_str = _format_age_human(wait_left_mins * 60)
        action_code = "DAILY_CYCLE_REST"
        action_badge = "warning"
        action_title = f"🌙 DESCANSO DE CICLO 12H–24H (FALTAM {wait_left_str})"
        action_detail = (
            f"A conta já recebeu {batches_24h_count} lote(s) ({effective_posts_24h} vídeos) nas últimas 24h "
            f"(último {last_post_age_str}). Para evitar Checkpoint e imitar seu padrão vencedor, "
            f"aguarde {wait_left_str} antes do próximo lote!"
        )
        priority_score = 30
        can_post_now = False

    elif mins_since_last_post is not None and mins_since_last_post < MIN_GAP_AFTER_BATCH1_MINS:
        wait_left = max(15, MIN_GAP_AFTER_BATCH1_MINS - mins_since_last_post)
        wait_str = _format_age_human(wait_left * 60)
        if v_min >= 50 or last_batch_views >= 2000:
            action_code = "COOLDOWN_HOT"
            action_badge = "warning"
            action_title = f"⏳ MATURANDO 1º LOTE (AGUARDAR {wait_str})"
            action_detail = (
                f"Último lote ({last_batch_count} vídeos {last_post_age_str}) somou "
                f"{format_number_br(last_batch_views)} views (média {format_number_br(last_batch_avg_views)}/post). "
                f"Respeite a janela de 3h30–4h entre lotes!"
            )
            priority_score = 60
        else:
            action_code = "COOLDOWN_MATURING"
            action_badge = "info"
            action_title = f"⏳ AGUARDAR JANELA 3H30 ({wait_str} RESTANTES)"
            action_detail = (
                f"Lote enviado {last_post_age_str} ({last_batch_count} vídeos). "
                f"Espere completar 3h30 para validar a entrega antes do 2º lote do dia."
            )
            priority_score = 45
        can_post_now = False

    elif v_min >= 60 or (v_hour >= 3500 and activity_index_pct >= 45) or (last_batch_avg_views >= 3000):
        if batches_12h_count == 0 and effective_posts_24h <= 12:
            recommended_batch_size = 9
            lote_tipo = "1º Lote do Ciclo (8–10 vídeos)"
        else:
            recommended_batch_size = 6
            lote_tipo = "2º Lote do Dia (6 vídeos)"

        action_code = "SURF_TRACTION"
        action_badge = "success"
        action_title = f"🔥 ENVIAR {lote_tipo.upper()}"
        action_detail = (
            f"Janela segura liberada (último lote {last_post_age_str} com média de "
            f"{format_number_br(last_batch_avg_views)} views/post | {batches_24h_count}/2 lotes em 24h). "
            f"Conta a {format_rate_br(v_min)}/min!"
        )
        priority_score = 100 + int(min(50, v_min / 10))
        can_post_now = True

    elif v_min >= 15 or total_views >= 250000:
        if batches_12h_count == 0 and effective_posts_24h == 0:
            action_code = "FEED_WARM"
            action_badge = "success"
            action_title = "🚀 ABRIR CICLO DIÁRIO (LOTE 8–9 VÍDEOS)"
            action_detail = (
                f"Conta descansada 12h+ ({last_post_age_str}) e saudável ({format_number_br(total_views)} views). "
                f"Pronta para o 1º lote forte do dia."
            )
            priority_score = 92
            can_post_now = True
            recommended_batch_size = 9
        else:
            action_code = "REACTIVATE_CHAMPION"
            action_badge = "success"
            action_title = "🎯 2º LOTE MODERADO (6 VÍDEOS)"
            action_detail = (
                f"Intervalo de 3h30+ cumprido ({last_post_age_str}) e {batches_24h_count}/2 lotes em 24h. "
                f"Envie 6 vídeos e depois dê 12h+ de descanso."
            )
            priority_score = 84
            can_post_now = True
            recommended_batch_size = 6
    else:
        action_code = "LOW_TRACTION"
        action_badge = "warning"
        action_title = "🧪 TESTE DE AQUECIMENTO (3–4 VÍDEOS)"
        action_detail = (
            f"Baixa velocidade atual ({format_rate_br(v_min)}/min). "
            f"Envie lote curto no horário de pico ({best_window_str})."
        )
        priority_score = 35
        can_post_now = True
        recommended_batch_size = 4

    return {
        "activity_index_pct": activity_index_pct,
        "accel_ratio": accel_ratio,
        "trend_label": trend_label,
        "trend_color": trend_color,
        "hit_rate_10k_pct": hit_rate_10k_pct,
        "hits_10k": hits_10k,
        "virals_100k": virals_100k,
        "dead_posts_count": dead_posts_count,
        "dead_rate_pct": dead_rate_pct,
        "top_post_share_pct": top_post_share_pct,
        "followers_per_1k_views": followers_per_1k_views,
        "best_window_str": best_window_str,
        "last_post_age_str": last_post_age_str,
        "mins_since_last_post": mins_since_last_post,
        "recent_batch_count_3h": recent_batch_count_3h,
        "recent_batch_views_3h": recent_batch_views_3h,
        "batches_24h_count": batches_24h_count,
        "batches_12h_count": batches_12h_count,
        "posts_last_24h_count": effective_posts_24h,
        "last_batch_count": last_batch_count,
        "last_batch_views": last_batch_views,
        "last_batch_avg_views": last_batch_avg_views,
        "historical_avg_views": historical_avg_views,
        "last_batch_throttled": last_batch_throttled,
        "action_code": action_code,
        "action_badge": action_badge,
        "action_title": action_title,
        "action_detail": action_detail,
        "priority_score": priority_score,
        "can_post_now": can_post_now,
        "recommended_batch_size": recommended_batch_size
    }


def _parse_ig_post_timestamp_to_ts_and_str(raw_ts):
    return _parse_ig_post_timestamp_to_brt(raw_ts)


# ==============================================================================
# FUNÇÕES DE PERSISTÊNCIA NO UPSTASH REDIS (COM RETRY, TOKENS E LISTA DE EXCLUÍDAS)
# ==============================================================================

def is_upstash_configured():
    return bool(UPSTASH_URL and UPSTASH_TOKEN)


def upstash_command(*args, retries=3):
    if not is_upstash_configured():
        return False, None

    for attempt in range(1, retries + 1):
        try:
            r = requests.post(
                UPSTASH_URL,
                headers={
                    "Authorization": f"Bearer {UPSTASH_TOKEN}",
                    "Content-Type": "application/json"
                },
                json=list(args),
                timeout=12
            )
            if r.status_code == 200:
                data = r.json()
                if "error" not in data:
                    return True, data.get("result")
                print(f"[ERRO UPSTASH PAYLOAD] {data.get('error')}", flush=True)
            else:
                print(f"[AVISO UPSTASH] Tentativa {attempt}/{retries} - HTTP {r.status_code}: {r.text}", flush=True)
        except Exception as e:
            print(f"[ERRO UPSTASH] Tentativa {attempt}/{retries} falhou: {e}", flush=True)

        if attempt < retries:
            time.sleep(0.8 * attempt)

    return False, None


def load_state_from_upstash():
    if not is_upstash_configured():
        return False, {}

    ok, raw_state = upstash_command("GET", REDIS_STATE_KEY)
    if not ok:
        return False, {}

    if raw_state is None:
        return True, {}

    if isinstance(raw_state, str):
        try:
            parsed = json.loads(raw_state)
            if isinstance(parsed, dict):
                return True, parsed
        except Exception as e:
            print(f"[ERRO UPSTASH PARSE STATE]: {e}", flush=True)
            return False, {}
    elif isinstance(raw_state, dict):
        return True, raw_state

    return False, {}


def save_state_to_upstash(state_data):
    """
    Salva o estado completo no Upstash Redis usando 1 comando (SET),
    respeitando as contas removidas (`deleted_ids`), preservando `custom_tokens`
    e mantendo os recordes globais somados (`global_peak_views_per_min` e `global_peak_views_per_hour`).
    """
    global LAST_REDIS_FETCH_TS, REDIS_BOOTSTRAPPED, MEMORY_LAST_SYNC_TS, MEMORY_LAST_SYNC_STR
    global MEMORY_DELETED_IDS, MEMORY_CUSTOM_TOKENS, MEMORY_GLOBAL_PEAK_MIN, MEMORY_GLOBAL_PEAK_HOUR
    if not is_upstash_configured() or not isinstance(state_data, dict):
        return False

    try:
        if not REDIS_BOOTSTRAPPED:
            ok_read, remote_state = load_state_from_upstash()
            if not ok_read:
                print(
                    "[PROTEÇÃO ANTI-ZERAMENTO] Abortando escrita no Upstash pois a leitura prévia falhou.",
                    flush=True
                )
                return False

            if isinstance(remote_state, dict):
                for d_id in remote_state.get("deleted_ids", []):
                    MEMORY_DELETED_IDS.add(str(d_id).strip())

                MEMORY_GLOBAL_PEAK_MIN = max(
                    MEMORY_GLOBAL_PEAK_MIN,
                    _safe_float(remote_state.get("global_peak_views_per_min"))
                )
                MEMORY_GLOBAL_PEAK_HOUR = max(
                    MEMORY_GLOBAL_PEAK_HOUR,
                    _safe_float(remote_state.get("global_peak_views_per_hour"))
                )

                remote_tokens = remote_state.get("custom_tokens", {})
                if isinstance(remote_tokens, dict):
                    for t_uid, t_val in remote_tokens.items():
                        uid_s = str(t_uid).strip()
                        if uid_s and t_val and uid_s not in MEMORY_DELETED_IDS:
                            MEMORY_CUSTOM_TOKENS[uid_s] = str(t_val).strip()

                remote_accs = remote_state.get("accounts", {})
                if isinstance(remote_accs, dict):
                    for r_uid, r_acc in remote_accs.items():
                        uid_s = str(r_uid).strip()
                        if uid_s in MEMORY_DELETED_IDS:
                            continue
                        if isinstance(r_acc, dict):
                            MEMORY_CACHE_ACCOUNTS[uid_s] = merge_best_account_data(
                                r_acc, MEMORY_CACHE_ACCOUNTS.get(uid_s, {})
                            )
                if float(remote_state.get("last_global_sync_ts") or 0) > MEMORY_LAST_SYNC_TS:
                    MEMORY_LAST_SYNC_TS = float(remote_state["last_global_sync_ts"])
                    MEMORY_LAST_SYNC_STR = remote_state.get("last_global_sync_str", MEMORY_LAST_SYNC_STR)

            REDIS_BOOTSTRAPPED = True

        for d_id in state_data.get("deleted_ids", []):
            MEMORY_DELETED_IDS.add(str(d_id).strip())

        if isinstance(state_data.get("custom_tokens"), dict):
            for t_uid, t_val in state_data["custom_tokens"].items():
                uid_s = str(t_uid).strip()
                if uid_s and t_val and uid_s not in MEMORY_DELETED_IDS:
                    MEMORY_CUSTOM_TOKENS[uid_s] = str(t_val).strip()

        for d_id in list(MEMORY_DELETED_IDS):
            MEMORY_CACHE_ACCOUNTS.pop(d_id, None)
            MEMORY_CUSTOM_TOKENS.pop(d_id, None)

        new_accs = state_data.get("accounts", {}) if isinstance(state_data.get("accounts"), dict) else {}
        cleaned_accs = {}

        all_uids = (set(MEMORY_CACHE_ACCOUNTS.keys()) | set(str(k) for k in new_accs.keys())) - MEMORY_DELETED_IDS
        for uid_str in all_uids:
            mem_acc = MEMORY_CACHE_ACCOUNTS.get(uid_str, {})
            inc_acc = new_accs.get(uid_str, {})
            clean_merged = merge_best_account_data(mem_acc, inc_acc)
            clean_merged.pop("access_token", None)
            cleaned_accs[uid_str] = clean_merged
            MEMORY_CACHE_ACCOUNTS[uid_str] = clean_merged

        sorted_accs = sort_accounts_by_views_desc(cleaned_accs)
        g_peak_min, g_peak_hour = _compute_global_peaks_from_accounts(
            sorted_accs,
            prev_peak_min=_safe_float(state_data.get("global_peak_views_per_min")),
            prev_peak_hour=_safe_float(state_data.get("global_peak_views_per_hour"))
        )
        MEMORY_GLOBAL_PEAK_MIN = g_peak_min
        MEMORY_GLOBAL_PEAK_HOUR = g_peak_hour

        state_to_save = {
            "last_global_sync_ts": max(
                float(state_data.get("last_global_sync_ts") or 0),
                float(MEMORY_LAST_SYNC_TS or 0)
            ),
            "last_global_sync_str": (
                state_data.get("last_global_sync_str")
                if (state_data.get("last_global_sync_str") and state_data.get("last_global_sync_str") != "Ainda não sincronizado")
                else (MEMORY_LAST_SYNC_STR or "—")
            ),
            "global_peak_views_per_min": g_peak_min,
            "global_peak_views_per_hour": g_peak_hour,
            "deleted_ids": sorted(list(MEMORY_DELETED_IDS)),
            "custom_tokens": dict(MEMORY_CUSTOM_TOKENS),
            "accounts": sorted_accs
        }

        ok_set, _ = upstash_command("SET", REDIS_STATE_KEY, json.dumps(state_to_save, ensure_ascii=False))
        if ok_set:
            state_data["accounts"] = sorted_accs
            state_data["global_peak_views_per_min"] = g_peak_min
            state_data["global_peak_views_per_hour"] = g_peak_hour
            state_data["deleted_ids"] = sorted(list(MEMORY_DELETED_IDS))
            state_data["custom_tokens"] = dict(MEMORY_CUSTOM_TOKENS)
            LAST_REDIS_FETCH_TS = time.time()
            REDIS_BOOTSTRAPPED = True
            return True
        return False
    except Exception as e:
        print(f"[ERRO AO SALVAR NO UPSTASH]: {e}", flush=True)
        return False


# ==============================================================================
# FUNÇÕES DE ARQUIVO E MERGE DE DADOS (BLINDAGEM ANTI-ZERAMENTO + RECORDES)
# ==============================================================================

def load_json(filepath, default):
    if os.path.exists(filepath):
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return default
    return default


def save_json(filepath, data):
    tmp_path = f"{filepath}.tmp"
    try:
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=4, ensure_ascii=False)
        os.replace(tmp_path, filepath)
    except Exception:
        try:
            with open(filepath, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=4, ensure_ascii=False)
        except Exception:
            pass


def sort_accounts_by_views_desc(accounts_dict):
    if not isinstance(accounts_dict, dict):
        return {}
    sorted_items = sorted(
        accounts_dict.items(),
        key=lambda item: (
            int((item[1] or {}).get("total_views") or 0),
            int((item[1] or {}).get("followers_count") or 0)
        ),
        reverse=True
    )
    return dict(sorted_items)


def merge_best_account_data(base_acc, new_acc):
    if not isinstance(base_acc, dict):
        base_acc = {}
    if not isinstance(new_acc, dict):
        new_acc = {}

    merged = dict(base_acc)
    for k, v in new_acc.items():
        if v is not None and v != "":
            merged[k] = v

    old_followers = _safe_int(base_acc.get("followers_count"))
    new_followers = _safe_int(new_acc.get("followers_count"))
    merged["followers_count"] = max(old_followers, new_followers)

    old_views = _safe_int(base_acc.get("total_views"))
    new_views = _safe_int(new_acc.get("total_views"))
    merged["total_views"] = max(old_views, new_views)

    old_media = _safe_int(base_acc.get("media_count"))
    new_media = _safe_int(new_acc.get("media_count"))
    merged["media_count"] = max(old_media, new_media)

    old_posts = base_acc.get("posts_list") if isinstance(base_acc.get("posts_list"), list) else []
    new_posts = new_acc.get("posts_list") if isinstance(new_acc.get("posts_list"), list) else []

    if len(new_posts) > 0 or len(old_posts) > 0:
        posts_by_id = {}
        for p in old_posts:
            if isinstance(p, dict) and p.get("id"):
                pid = str(p["id"])
                p_copy = dict(p)
                p_copy["views"] = _safe_int(p.get("views"))
                p_copy["duration_sec"] = _safe_float(p.get("duration_sec"))
                if p_copy["duration_sec"] > 0:
                    MEDIA_DURATION_CACHE[pid] = p_copy["duration_sec"]
                posts_by_id[pid] = p_copy

        for p in new_posts:
            if isinstance(p, dict) and p.get("id"):
                pid = str(p["id"])
                new_v = _safe_int(p.get("views"))
                new_dur = _safe_float(p.get("duration_sec"))
                if pid in posts_by_id:
                    old_v = _safe_int(posts_by_id[pid].get("views"))
                    old_dur = _safe_float(posts_by_id[pid].get("duration_sec"))
                    prev_gain = _safe_int(posts_by_id[pid].get("recent_views_gain"))
                    best_p = dict(posts_by_id[pid])
                    best_p.update(p)
                    best_p["views"] = max(old_v, new_v)
                    best_p["duration_sec"] = max(old_dur, new_dur, MEDIA_DURATION_CACHE.get(pid, 0.0))
                    if best_p["duration_sec"] > 0:
                        MEDIA_DURATION_CACHE[pid] = best_p["duration_sec"]
                    if new_v > old_v and old_v > 0:
                        best_p["recent_views_gain"] = (new_v - old_v)
                    else:
                        best_p["recent_views_gain"] = max(prev_gain, _safe_int(p.get("recent_views_gain")))
                    posts_by_id[pid] = best_p
                else:
                    p_copy = dict(p)
                    p_copy["views"] = new_v
                    p_copy["duration_sec"] = max(new_dur, MEDIA_DURATION_CACHE.get(pid, 0.0))
                    if p_copy["duration_sec"] > 0:
                        MEDIA_DURATION_CACHE[pid] = p_copy["duration_sec"]
                    p_copy["recent_views_gain"] = _safe_int(p.get("recent_views_gain"))
                    posts_by_id[pid] = p_copy

        merged_posts_list = sorted(posts_by_id.values(), key=lambda x: _safe_int(x.get("views")), reverse=True)
        merged["posts_list"] = merged_posts_list

        sum_posts_views = sum(_safe_int(x.get("views")) for x in merged_posts_list)
        merged["total_views"] = max(merged["total_views"], sum_posts_views)
        merged["media_count"] = max(merged["media_count"], len(merged_posts_list))
    else:
        merged["posts_list"] = []

    old_ts = str(base_acc.get("metrics_updated_at") or "").strip()
    new_ts = str(new_acc.get("metrics_updated_at") or "").strip()
    invalid_markers = ("", "—", "Sem coleta antes da queda")
    if new_ts not in invalid_markers:
        merged["metrics_updated_at"] = new_ts
    elif old_ts not in invalid_markers:
        merged["metrics_updated_at"] = old_ts
    else:
        merged["metrics_updated_at"] = old_ts or new_ts or "—"

    old_user = str(base_acc.get("username") or "").strip()
    new_user = str(new_acc.get("username") or "").strip()
    if (not new_user or new_user.startswith("user_")) and old_user and not old_user.startswith("user_"):
        merged["username"] = old_user

    snap_ts = _parse_br_datetime_to_ts(merged.get("metrics_updated_at"))
    merged["views_history"] = _merge_views_history(
        base_acc.get("views_history"),
        new_acc.get("views_history"),
        current_views=merged["total_views"],
        current_ts=snap_ts
    )
    v_min, v_hour = _compute_account_velocity_rates(merged)
    merged["views_per_min"] = v_min
    merged["views_per_hour"] = v_hour

    prev_peak_min = max(
        _safe_float(base_acc.get("peak_views_per_min")),
        _safe_float(new_acc.get("peak_views_per_min"))
    )
    prev_peak_hour = max(
        _safe_float(base_acc.get("peak_views_per_hour")),
        _safe_float(new_acc.get("peak_views_per_hour"))
    )
    merged["peak_views_per_min"] = round(max(prev_peak_min, v_min), 2)
    merged["peak_views_per_hour"] = round(max(prev_peak_hour, v_hour), 2)

    merged["intel"] = _analyze_account_intelligence(merged)

    return merged


def get_env_accounts():
    """
    Lê as contas de ACCOUNTS_CONFIG_JSON, mescla com `contas_conectadas.json`
    e também inclui contas/tokens adicionados diretamente pelo painel web (`MEMORY_CUSTOM_TOKENS`).
    """
    raw = os.environ.get("ACCOUNTS_CONFIG_JSON", "").strip()
    accounts_dict = {}

    if raw:
        try:
            data = json.loads(raw)
            if isinstance(data, dict) and "accounts" in data and isinstance(data["accounts"], dict):
                data = data["accounts"]

            if isinstance(data, list):
                for item in data:
                    if isinstance(item, dict):
                        uid = str(item.get("ig_user_id", "")).strip()
                        if uid and uid not in MEMORY_DELETED_IDS:
                            accounts_dict[uid] = dict(item)
            elif isinstance(data, dict):
                for uid, item in data.items():
                    if isinstance(item, dict):
                        item_copy = dict(item)
                        uid_clean = str(item_copy.get("ig_user_id") or uid).strip()
                        if uid_clean and uid_clean not in MEMORY_DELETED_IDS:
                            item_copy["ig_user_id"] = uid_clean
                            accounts_dict[uid_clean] = item_copy
        except Exception as e:
            print(f"[ERRO] Falha ao ler ACCOUNTS_CONFIG_JSON: {e}", flush=True)

    if os.path.exists(CODIGO1_ACCOUNTS_FILE):
        try:
            c1_data = load_json(CODIGO1_ACCOUNTS_FILE, {})
            if isinstance(c1_data, dict):
                c1_accs = c1_data.get("accounts", c1_data if "last_global_sync_ts" not in c1_data else {})
                if isinstance(c1_accs, dict):
                    for uid, item in c1_accs.items():
                        if isinstance(item, dict):
                            uid_str = str(item.get("ig_user_id") or uid).strip()
                            if uid_str in MEMORY_DELETED_IDS:
                                continue
                            if uid_str in accounts_dict:
                                token_backup = accounts_dict[uid_str].get("access_token") or item.get("access_token")
                                accounts_dict[uid_str] = merge_best_account_data(item, accounts_dict[uid_str])
                                if token_backup:
                                    accounts_dict[uid_str]["access_token"] = token_backup
                            else:
                                item_copy = dict(item)
                                item_copy["ig_user_id"] = uid_str
                                accounts_dict[uid_str] = item_copy
        except Exception as e:
            print(f"[ERRO] Falha ao ler contas_conectadas.json: {e}", flush=True)

    # Inclui ou atualiza tokens adicionados pelo formulário web
    for uid_str, tok in list(MEMORY_CUSTOM_TOKENS.items()):
        if not uid_str or uid_str in MEMORY_DELETED_IDS:
            continue
        if uid_str in accounts_dict:
            if tok:
                accounts_dict[uid_str]["access_token"] = tok
        else:
            cached = dict(MEMORY_CACHE_ACCOUNTS.get(uid_str, {}))
            cached["ig_user_id"] = uid_str
            if tok:
                cached["access_token"] = tok
            accounts_dict[uid_str] = cached

    return accounts_dict


def get_saved_state(force_redis=False):
    global MEMORY_LAST_SYNC_TS, MEMORY_LAST_SYNC_STR, LAST_REDIS_FETCH_TS, REDIS_BOOTSTRAPPED
    global MEMORY_DELETED_IDS, MEMORY_CUSTOM_TOKENS, MEMORY_GLOBAL_PEAK_MIN, MEMORY_GLOBAL_PEAK_HOUR

    with ACCOUNTS_LOCK:
        merged_accounts = {}
        last_ts = MEMORY_LAST_SYNC_TS
        last_str = MEMORY_LAST_SYNC_STR
        best_global_min = MEMORY_GLOBAL_PEAK_MIN
        best_global_hour = MEMORY_GLOBAL_PEAK_HOUR

        for fpath in (BUNDLED_MONITOR_FILE, RUNTIME_ACCOUNTS_FILE):
            if os.path.exists(fpath):
                fdata = load_json(fpath, {})
                if isinstance(fdata, dict):
                    best_global_min = max(best_global_min, _safe_float(fdata.get("global_peak_views_per_min")))
                    best_global_hour = max(best_global_hour, _safe_float(fdata.get("global_peak_views_per_hour")))
                    for d_id in fdata.get("deleted_ids", []):
                        MEMORY_DELETED_IDS.add(str(d_id).strip())
                    if isinstance(fdata.get("custom_tokens"), dict):
                        for t_uid, t_val in fdata["custom_tokens"].items():
                            uid_s = str(t_uid).strip()
                            if uid_s and t_val and uid_s not in MEMORY_DELETED_IDS:
                                MEMORY_CUSTOM_TOKENS[uid_s] = str(t_val).strip()

        now = time.time()
        should_query_redis = (
            is_upstash_configured()
            and (force_redis or not REDIS_BOOTSTRAPPED or (now - LAST_REDIS_FETCH_TS >= REDIS_READ_TTL))
        )

        redis_state = {}
        ok_redis = False
        if should_query_redis:
            ok_redis, redis_state = load_state_from_upstash()
            if ok_redis:
                LAST_REDIS_FETCH_TS = now
                REDIS_BOOTSTRAPPED = True
                if isinstance(redis_state, dict):
                    best_global_min = max(best_global_min, _safe_float(redis_state.get("global_peak_views_per_min")))
                    best_global_hour = max(best_global_hour, _safe_float(redis_state.get("global_peak_views_per_hour")))
                    for d_id in redis_state.get("deleted_ids", []):
                        MEMORY_DELETED_IDS.add(str(d_id).strip())
                    if isinstance(redis_state.get("custom_tokens"), dict):
                        for t_uid, t_val in redis_state["custom_tokens"].items():
                            uid_s = str(t_uid).strip()
                            if uid_s and t_val and uid_s not in MEMORY_DELETED_IDS:
                                MEMORY_CUSTOM_TOKENS[uid_s] = str(t_val).strip()

        for d_id in list(MEMORY_DELETED_IDS):
            MEMORY_CACHE_ACCOUNTS.pop(d_id, None)
            MEMORY_CUSTOM_TOKENS.pop(d_id, None)

        env_accs = get_env_accounts()
        for uid, acc in env_accs.items():
            uid_s = str(uid).strip()
            if uid_s in MEMORY_DELETED_IDS:
                continue
            clean_acc = dict(acc)
            clean_acc.pop("access_token", None)
            merged_accounts[uid_s] = merge_best_account_data(merged_accounts.get(uid_s, {}), clean_acc)

        if os.path.exists(BUNDLED_MONITOR_FILE):
            bundled = load_json(BUNDLED_MONITOR_FILE, {})
            if isinstance(bundled, dict):
                b_accs = bundled.get("accounts", bundled if "last_global_sync_ts" not in bundled else {})
                if isinstance(b_accs, dict):
                    for uid, acc in b_accs.items():
                        if isinstance(acc, dict):
                            uid_s = str(acc.get("ig_user_id") or uid).strip()
                            if uid_s in MEMORY_DELETED_IDS:
                                continue
                            acc_clean = dict(acc)
                            acc_clean.pop("access_token", None)
                            merged_accounts[uid_s] = merge_best_account_data(merged_accounts.get(uid_s, {}), acc_clean)
                if float(bundled.get("last_global_sync_ts") or 0) > last_ts:
                    last_ts = float(bundled["last_global_sync_ts"])
                    last_str = bundled.get("last_global_sync_str", last_str)

        if os.path.exists(RUNTIME_ACCOUNTS_FILE):
            runtime = load_json(RUNTIME_ACCOUNTS_FILE, {})
            if isinstance(runtime, dict):
                r_accs = runtime.get("accounts", runtime if "last_global_sync_ts" not in runtime else {})
                if isinstance(r_accs, dict):
                    for uid, acc in r_accs.items():
                        if isinstance(acc, dict):
                            uid_s = str(acc.get("ig_user_id") or uid).strip()
                            if uid_s in MEMORY_DELETED_IDS:
                                continue
                            acc_clean = dict(acc)
                            acc_clean.pop("access_token", None)
                            merged_accounts[uid_s] = merge_best_account_data(merged_accounts.get(uid_s, {}), acc_clean)
                if float(runtime.get("last_global_sync_ts") or 0) > last_ts:
                    last_ts = float(runtime["last_global_sync_ts"])
                    last_str = runtime.get("last_global_sync_str", last_str)

        if ok_redis and isinstance(redis_state, dict):
            redis_accs = redis_state.get("accounts", {})
            if isinstance(redis_accs, dict):
                for uid, acc in redis_accs.items():
                    if isinstance(acc, dict):
                        uid_s = str(acc.get("ig_user_id") or uid).strip()
                        if uid_s in MEMORY_DELETED_IDS:
                            continue
                        acc_clean = dict(acc)
                        acc_clean.pop("access_token", None)
                        merged_accounts[uid_s] = merge_best_account_data(
                            merged_accounts.get(uid_s, {}), acc_clean
                        )
            if float(redis_state.get("last_global_sync_ts") or 0) > last_ts:
                last_ts = float(redis_state["last_global_sync_ts"])
                last_str = redis_state.get("last_global_sync_str", last_str)

        for uid, acc in list(MEMORY_CACHE_ACCOUNTS.items()):
            uid_s = str(uid).strip()
            if uid_s in MEMORY_DELETED_IDS:
                MEMORY_CACHE_ACCOUNTS.pop(uid_s, None)
                continue
            if isinstance(acc, dict):
                merged_accounts[uid_s] = merge_best_account_data(merged_accounts.get(uid_s, {}), acc)

        for uid, acc in merged_accounts.items():
            MEMORY_CACHE_ACCOUNTS[str(uid)] = acc

        MEMORY_LAST_SYNC_TS = last_ts
        MEMORY_LAST_SYNC_STR = last_str

        sorted_accs = sort_accounts_by_views_desc(merged_accounts)
        g_peak_min, g_peak_hour = _compute_global_peaks_from_accounts(
            sorted_accs,
            prev_peak_min=best_global_min,
            prev_peak_hour=best_global_hour
        )
        MEMORY_GLOBAL_PEAK_MIN = g_peak_min
        MEMORY_GLOBAL_PEAK_HOUR = g_peak_hour

        result_state = {
            "last_global_sync_ts": last_ts,
            "last_global_sync_str": last_str,
            "global_peak_views_per_min": g_peak_min,
            "global_peak_views_per_hour": g_peak_hour,
            "deleted_ids": sorted(list(MEMORY_DELETED_IDS)),
            "custom_tokens": dict(MEMORY_CUSTOM_TOKENS),
            "accounts": sorted_accs
        }

        if should_query_redis and REDIS_BOOTSTRAPPED:
            save_json(RUNTIME_ACCOUNTS_FILE, result_state)
            if RUNTIME_ACCOUNTS_FILE != BUNDLED_MONITOR_FILE and os.access(BASE_DIR, os.W_OK):
                save_json(BUNDLED_MONITOR_FILE, result_state)

        return result_state


def save_current_state(state_data):
    global MEMORY_LAST_SYNC_TS, MEMORY_LAST_SYNC_STR, MEMORY_DELETED_IDS, MEMORY_CUSTOM_TOKENS
    global MEMORY_GLOBAL_PEAK_MIN, MEMORY_GLOBAL_PEAK_HOUR

    with ACCOUNTS_LOCK:
        if isinstance(state_data, dict):
            for d_id in state_data.get("deleted_ids", []):
                MEMORY_DELETED_IDS.add(str(d_id).strip())

            if isinstance(state_data.get("custom_tokens"), dict):
                for t_uid, t_val in state_data["custom_tokens"].items():
                    uid_s = str(t_uid).strip()
                    if uid_s and t_val and uid_s not in MEMORY_DELETED_IDS:
                        MEMORY_CUSTOM_TOKENS[uid_s] = str(t_val).strip()

            for d_id in list(MEMORY_DELETED_IDS):
                MEMORY_CACHE_ACCOUNTS.pop(d_id, None)
                MEMORY_CUSTOM_TOKENS.pop(d_id, None)

            if float(state_data.get("last_global_sync_ts") or 0) > MEMORY_LAST_SYNC_TS:
                MEMORY_LAST_SYNC_TS = float(state_data["last_global_sync_ts"])
                MEMORY_LAST_SYNC_STR = state_data.get("last_global_sync_str", MEMORY_LAST_SYNC_STR)

            if isinstance(state_data.get("accounts"), dict):
                for uid, acc in state_data["accounts"].items():
                    uid_s = str(uid).strip()
                    if uid_s in MEMORY_DELETED_IDS:
                        continue
                    clean_acc = dict(acc)
                    tok_inline = clean_acc.pop("access_token", None)
                    if tok_inline:
                        MEMORY_CUSTOM_TOKENS[uid_s] = str(tok_inline).strip()
                    MEMORY_CACHE_ACCOUNTS[uid_s] = merge_best_account_data(
                        MEMORY_CACHE_ACCOUNTS.get(uid_s, {}), clean_acc
                    )
                state_data["accounts"] = sort_accounts_by_views_desc(MEMORY_CACHE_ACCOUNTS)
                g_peak_min, g_peak_hour = _compute_global_peaks_from_accounts(
                    state_data["accounts"],
                    prev_peak_min=_safe_float(state_data.get("global_peak_views_per_min")),
                    prev_peak_hour=_safe_float(state_data.get("global_peak_views_per_hour"))
                )
                MEMORY_GLOBAL_PEAK_MIN = g_peak_min
                MEMORY_GLOBAL_PEAK_HOUR = g_peak_hour
                state_data["global_peak_views_per_min"] = g_peak_min
                state_data["global_peak_views_per_hour"] = g_peak_hour
                state_data["deleted_ids"] = sorted(list(MEMORY_DELETED_IDS))
                state_data["custom_tokens"] = dict(MEMORY_CUSTOM_TOKENS)

        if is_upstash_configured():
            save_state_to_upstash(state_data)

        save_json(RUNTIME_ACCOUNTS_FILE, state_data)

        if RUNTIME_ACCOUNTS_FILE != BUNDLED_MONITOR_FILE and os.access(BASE_DIR, os.W_OK):
            save_json(BUNDLED_MONITOR_FILE, state_data)


def delete_account_permanently(acc_id):
    uid_s = str(acc_id or "").strip()
    if not uid_s:
        return False

    with ACCOUNTS_LOCK:
        state = get_saved_state(force_redis=not REDIS_BOOTSTRAPPED)
        MEMORY_DELETED_IDS.add(uid_s)
        MEMORY_CACHE_ACCOUNTS.pop(uid_s, None)
        MEMORY_CUSTOM_TOKENS.pop(uid_s, None)

        accounts = state.get("accounts", {}) if isinstance(state.get("accounts"), dict) else {}
        accounts.pop(uid_s, None)

        if os.path.exists(CODIGO1_ACCOUNTS_FILE) and os.access(BASE_DIR, os.W_OK):
            try:
                c1_data = load_json(CODIGO1_ACCOUNTS_FILE, {})
                if isinstance(c1_data, dict):
                    if "accounts" in c1_data and isinstance(c1_data["accounts"], dict):
                        c1_data["accounts"].pop(uid_s, None)
                    else:
                        c1_data.pop(uid_s, None)
                    save_json(CODIGO1_ACCOUNTS_FILE, c1_data)
            except Exception:
                pass

        new_state = {
            "last_global_sync_ts": state.get("last_global_sync_ts", MEMORY_LAST_SYNC_TS),
            "last_global_sync_str": state.get("last_global_sync_str", MEMORY_LAST_SYNC_STR),
            "global_peak_views_per_min": state.get("global_peak_views_per_min", MEMORY_GLOBAL_PEAK_MIN),
            "global_peak_views_per_hour": state.get("global_peak_views_per_hour", MEMORY_GLOBAL_PEAK_HOUR),
            "deleted_ids": sorted(list(MEMORY_DELETED_IDS)),
            "custom_tokens": dict(MEMORY_CUSTOM_TOKENS),
            "accounts": sort_accounts_by_views_desc(accounts)
        }
        save_current_state(new_state)
        return True


def add_or_update_account_minimal(ig_user_id_input, access_token_input):
    """
    Adiciona ou reconecta uma conta usando apenas 1 ou 2 dados:
    - Somente o Access Token (descobre o IG User ID e @username automaticamente via /me)
    - Ou Access Token + IG User ID
    - Ou somente o IG User ID (caso o token já exista no ambiente/histórico ou para cadastro inicial)
    """
    uid_clean = str(ig_user_id_input or "").strip()
    token_clean = str(access_token_input or "").strip()

    if not uid_clean and not token_clean:
        return False, "Informe pelo menos o Access Token ou o ID da conta.", None

    discovered_username = None

    # Se enviou Token, tenta descobrir/validar o ID e o @username automaticamente na API
    if token_clean:
        endpoints = []
        if uid_clean:
            endpoints.append(f"https://graph.instagram.com/{GRAPH_API_VERSION}/{uid_clean}")
        endpoints.append(f"https://graph.instagram.com/{GRAPH_API_VERSION}/me")

        last_err_msg = None
        for ep in endpoints:
            try:
                r = requests.get(
                    ep,
                    params={
                        "fields": "id,user_id,username,name,account_type,followers_count,media_count",
                        "access_token": token_clean
                    },
                    timeout=15
                )
                p_data = r.json()
                if r.status_code == 200 and isinstance(p_data, dict) and "error" not in p_data:
                    resolved_id = str(p_data.get("user_id") or p_data.get("id") or "").strip()
                    if not uid_clean and resolved_id:
                        uid_clean = resolved_id
                    if p_data.get("username"):
                        discovered_username = str(p_data["username"]).strip()
                    break
                elif isinstance(p_data, dict) and "error" in p_data:
                    last_err_msg = p_data["error"].get("message")
            except Exception as e:
                last_err_msg = str(e)

        if not uid_clean:
            return (
                False,
                f"Não foi possível descobrir o ID da conta apenas com este Token ({last_err_msg or 'Token inválido'}). Verifique o Token ou informe também o ID da conta.",
                None
            )

    with ACCOUNTS_LOCK:
        state = get_saved_state(force_redis=not REDIS_BOOTSTRAPPED)
        # Se a conta já tinha sido excluída antes, reativa automaticamente
        MEMORY_DELETED_IDS.discard(uid_clean)

        if token_clean:
            MEMORY_CUSTOM_TOKENS[uid_clean] = token_clean
        else:
            env_accs = get_env_accounts()
            token_clean = (
                MEMORY_CUSTOM_TOKENS.get(uid_clean, "")
                or (env_accs.get(uid_clean, {}) or {}).get("access_token", "")
            )

        existing_acc = state.get("accounts", {}).get(uid_clean, {})
        now_brt_str = datetime.now(BRT).strftime("%d/%m/%Y %H:%M:%S")

        acc_config = {
            "ig_user_id": uid_clean,
            "access_token": token_clean,
            "username": discovered_username or existing_acc.get("username") or f"user_{uid_clean}",
            "connected_at": existing_acc.get("connected_at") or now_brt_str,
            "token_type_label": "Longa Duração (60 dias)"
        }

    # Coleta imediatamente seguidores, status, cota 24h e todos os Reels/posts da nova conta
    fetched_acc = fetch_account_current_metrics(acc_config, existing_acc)

    with ACCOUNTS_LOCK:
        state = get_saved_state(force_redis=False)
        accounts = state.get("accounts", {}) if isinstance(state.get("accounts"), dict) else {}
        accounts[uid_clean] = merge_best_account_data(accounts.get(uid_clean, {}), fetched_acc)

        if os.path.exists(CODIGO1_ACCOUNTS_FILE) and os.access(BASE_DIR, os.W_OK):
            try:
                c1_data = load_json(CODIGO1_ACCOUNTS_FILE, {})
                if isinstance(c1_data, dict):
                    target_map = c1_data["accounts"] if ("accounts" in c1_data and isinstance(c1_data["accounts"], dict)) else c1_data
                    entry_with_tok = dict(accounts[uid_clean])
                    if token_clean:
                        entry_with_tok["access_token"] = token_clean
                    target_map[uid_clean] = entry_with_tok
                    save_json(CODIGO1_ACCOUNTS_FILE, c1_data)
            except Exception:
                pass

        now_ts = time.time()
        now_str = datetime.now(BRT).strftime("%d/%m/%Y %H:%M:%S")
        new_state = {
            "last_global_sync_ts": now_ts,
            "last_global_sync_str": now_str,
            "global_peak_views_per_min": state.get("global_peak_views_per_min", MEMORY_GLOBAL_PEAK_MIN),
            "global_peak_views_per_hour": state.get("global_peak_views_per_hour", MEMORY_GLOBAL_PEAK_HOUR),
            "deleted_ids": sorted(list(MEMORY_DELETED_IDS)),
            "custom_tokens": dict(MEMORY_CUSTOM_TOKENS),
            "accounts": sort_accounts_by_views_desc(accounts)
        }
        save_current_state(new_state)

    return True, "Conta adicionada e sincronizada com sucesso!", accounts[uid_clean]


# ==============================================================================
# SEGURANÇA: LOGIN OBRIGATÓRIO (DASHBOARD_USER e DASHBOARD_PASS)
# ==============================================================================

def check_basic_auth(username, password):
    expected_user = os.environ.get("DASHBOARD_USER", "").strip()
    expected_pass = os.environ.get("DASHBOARD_PASS", "").strip()
    if not expected_user or not expected_pass:
        return False
    return (
        hmac.compare_digest(username or "", expected_user)
        and hmac.compare_digest(password or "", expected_pass)
    )


def requires_auth(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        expected_user = os.environ.get("DASHBOARD_USER", "").strip()
        expected_pass = os.environ.get("DASHBOARD_PASS", "").strip()
        if not expected_user or not expected_pass:
            return Response(
                "Erro de Segurança: Configure as variáveis de ambiente DASHBOARD_USER e DASHBOARD_PASS no servidor.",
                503
            )
        auth = request.authorization
        if not auth or not check_basic_auth(auth.username, auth.password):
            return Response(
                "Acesso restrito. Digite seu usuário e senha.",
                401,
                {"WWW-Authenticate": 'Basic realm="Painel Monitor 24h"'}
            )
        return f(*args, **kwargs)
    return decorated


@app.after_request
def add_security_headers(response):
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["Referrer-Policy"] = "no-referrer"
    response.headers["Robots-Tag"] = "noindex, nofollow"
    response.headers["Content-Security-Policy"] = (
        "default-src 'self'; "
        "style-src 'self' 'unsafe-inline'; "
        "script-src 'self' 'unsafe-inline'; "
        "connect-src 'self'; "
        "img-src 'self' data:;"
    )
    return response


# ==============================================================================
# COLETOR DE MÉTRICAS E DURAÇÃO DOS VÍDEOS
# ==============================================================================

def _fetch_single_media_views(media_item, access_token):
    media_id = media_item.get("id")
    if not media_id:
        return 0

    insights_obj = media_item.get("insights", {})
    if isinstance(insights_obj, dict):
        for metric_entry in insights_obj.get("data", []):
            vals = metric_entry.get("values", [])
            if vals and isinstance(vals[0].get("value"), (int, float)):
                return int(vals[0]["value"])

    for direct_key in ("views", "play_count", "ig_play_count", "video_views"):
        if isinstance(media_item.get(direct_key), (int, float)):
            return int(media_item[direct_key])

    insights_url = f"https://graph.instagram.com/{GRAPH_API_VERSION}/{media_id}/insights"
    for metric_name in ("views", "plays", "ig_reels_aggregated_all_plays_count", "video_views", "impressions"):
        try:
            r = requests.get(
                insights_url,
                params={"metric": metric_name, "access_token": access_token},
                timeout=12
            )
            if r.status_code == 200:
                d = r.json().get("data", [])
                if d and d[0].get("values"):
                    val = d[0]["values"][0].get("value", 0)
                    if isinstance(val, (int, float)):
                        return int(val)
        except Exception:
            continue
    return 0


def _classify_instagram_account_status(profile_ok, profile_err_obj, pub_limit_res):
    if not profile_ok:
        err = profile_err_obj if isinstance(profile_err_obj, dict) else {}
        code = err.get("code")
        subcode = err.get("error_subcode")
        msg = (err.get("message") or "").lower()

        if code == 190:
            if subcode in (459, 464) or "checkpoint" in msg or "confirm your identity" in msg or "verify" in msg or "log in to www.instagram.com" in msg:
                return ("Requer Verificação (Checkpoint)", "error", err.get("message", "Conta solicitou confirmação/checkpoint no app."))
            if subcode == 458 or "not authorized" in msg or "revoked" in msg:
                return ("Desconectada (Acesso Revogado)", "error", err.get("message", "Permissão revogada no aplicativo."))
            if subcode in (463, 467):
                return ("Sessão Expirada", "error", err.get("message", "Token de acesso expirou."))
            return ("Caiu / Sessão Inválida", "error", err.get("message", "Token inválido ou conta inacessível na Meta."))

        if code in (368, 4, 17, 32, 613) or "restricted" in msg or "temporarily blocked" in msg or "spam" in msg:
            return ("Restrita / Bloqueio Temporário", "warning", err.get("message", "Ação restrita temporariamente pelo Instagram."))

        if "disabled" in msg or "deactivated" in msg or "suspended" in msg or "ban" in msg:
            return ("Bloqueada / Desativada", "error", err.get("message", "Conta desativada ou suspensa no Instagram."))

        if code in (10, 200) or "permission" in msg:
            return ("Restrita (Sem Permissão)", "warning", err.get("message", "Permissões insuficientes na conta."))

        if err:
            return ("Caiu / Alerta na Conta", "error", err.get("message", "Erro retornado pela API do Instagram."))
        return ("Sem Resposta da Rede", "warning", "Não foi possível contatar a API do Instagram no momento.")

    if isinstance(pub_limit_res, dict):
        if "error" in pub_limit_res:
            perr = pub_limit_res.get("error") or {}
            pcode = perr.get("code")
            pmsg = (perr.get("message") or "").lower()
            if pcode == 368 or "restricted" in pmsg or "spam" in pmsg or "blocked" in pmsg:
                return ("Restrita para Publicação", "warning", perr.get("message", "Conta com restrição temporária de publicação."))
        elif "data" in pub_limit_res and pub_limit_res["data"]:
            item = pub_limit_res["data"][0] if isinstance(pub_limit_res["data"], list) else {}
            quota_usage = item.get("quota_usage")
            cfg = item.get("config") or {}
            quota_total = cfg.get("quota_total")
            if isinstance(quota_usage, int) and isinstance(quota_total, int) and quota_total > 0:
                if quota_usage >= quota_total:
                    return ("Limite Diário Atingido", "warning", f"Cota 24h atingida ({quota_usage}/{quota_total}).")
                return ("Ativa", "success", f"Conta ativa (Cota 24h: {quota_usage}/{quota_total} usados).")

    return ("Ativa", "success", "Conta ativa, verificada e normal na API oficial do Instagram.")


def fetch_account_current_metrics(acc_config, last_json_entry):
    ig_user_id = str(acc_config.get("ig_user_id", "")).strip()
    access_token = acc_config.get("access_token", "")
    now_ts = time.time()
    now_str = datetime.now(BRT).strftime("%d/%m/%Y %H:%M:%S")

    previous_best = merge_best_account_data(acc_config, last_json_entry)
    prev_followers = _safe_int(previous_best.get("followers_count"))
    prev_views = _safe_int(previous_best.get("total_views"))
    prev_media_count = _safe_int(previous_best.get("media_count"))
    prev_posts_list = previous_best.get("posts_list") if isinstance(previous_best.get("posts_list"), list) else []
    prev_updated_at = previous_best.get("metrics_updated_at") or "Sem coleta antes da queda"

    current = dict(previous_best)
    current["ig_user_id"] = ig_user_id
    current["username"] = previous_best.get("username") or acc_config.get("username") or f"user_{ig_user_id}"
    current["label"] = acc_config.get("label") or previous_best.get("label") or "Conta"
    current["connected_at"] = acc_config.get("connected_at") or previous_best.get("connected_at") or "—"
    current["token_type_label"] = acc_config.get("token_type_label") or previous_best.get("token_type_label") or "Longa Duração (60 dias)"

    if not access_token:
        current["account_status"] = previous_best.get("account_status", "Sem Token / Histórico")
        current["account_status_badge"] = previous_best.get("account_status_badge", "warning")
        current["followers_count"] = prev_followers
        current["total_views"] = prev_views
        current["media_count"] = prev_media_count
        current["posts_list"] = prev_posts_list
        current["metrics_updated_at"] = prev_updated_at
        v_min, v_hour = _compute_account_velocity_rates(current)
        current["views_per_min"] = v_min
        current["views_per_hour"] = v_hour
        current["peak_views_per_min"] = round(max(_safe_float(previous_best.get("peak_views_per_min")), v_min), 2)
        current["peak_views_per_hour"] = round(max(_safe_float(previous_best.get("peak_views_per_hour")), v_hour), 2)
        current["intel"] = _analyze_account_intelligence(current)
        current.pop("access_token", None)
        return current

    profile_ok = False
    last_profile_error = {}
    fetched_followers = None
    fetched_media_count = None

    for endpoint in (
        f"https://graph.instagram.com/{GRAPH_API_VERSION}/{ig_user_id}",
        f"https://graph.instagram.com/{GRAPH_API_VERSION}/me"
    ):
        try:
            res_profile = requests.get(
                endpoint,
                params={
                    "fields": "id,user_id,username,name,account_type,followers_count,media_count",
                    "access_token": access_token
                },
                timeout=15
            )
            p_data = res_profile.json()
            if res_profile.status_code == 200 and "error" not in p_data:
                profile_ok = True
                if p_data.get("username"):
                    current["username"] = p_data["username"]
                if "followers_count" in p_data and p_data["followers_count"] is not None:
                    fetched_followers = _safe_int(p_data["followers_count"])
                if "media_count" in p_data and p_data["media_count"] is not None:
                    fetched_media_count = _safe_int(p_data["media_count"])
                if fetched_followers is not None:
                    break
            else:
                if isinstance(p_data, dict) and "error" in p_data:
                    last_profile_error = p_data["error"]
        except Exception as e:
            last_profile_error = {"message": str(e)}

    pub_limit_data = None
    if profile_ok:
        try:
            res_limit = requests.get(
                f"https://graph.instagram.com/{GRAPH_API_VERSION}/{ig_user_id}/content_publishing_limit",
                params={"fields": "config,quota_usage", "access_token": access_token},
                timeout=12
            )
            pub_limit_data = res_limit.json()
            if isinstance(pub_limit_data, dict) and pub_limit_data.get("data"):
                q_item = pub_limit_data["data"][0] if isinstance(pub_limit_data["data"], list) else {}
                if isinstance(q_item.get("quota_usage"), int):
                    current["quota_usage_24h"] = q_item["quota_usage"]
        except Exception:
            pub_limit_data = None

    status_label, status_badge, status_detail = _classify_instagram_account_status(
        profile_ok, last_profile_error, pub_limit_data
    )
    current["account_status"] = status_label
    current["account_status_badge"] = status_badge
    current["account_status_detail"] = status_detail

    if not profile_ok:
        current["followers_count"] = prev_followers
        current["total_views"] = prev_views
        current["media_count"] = prev_media_count
        current["posts_list"] = sorted(prev_posts_list, key=lambda x: _safe_int(x.get("views")), reverse=True)
        current["metrics_updated_at"] = prev_updated_at
        v_min, v_hour = _compute_account_velocity_rates(current)
        current["views_per_min"] = v_min
        current["views_per_hour"] = v_hour
        current["peak_views_per_min"] = round(max(_safe_float(previous_best.get("peak_views_per_min")), v_min), 2)
        current["peak_views_per_hour"] = round(max(_safe_float(previous_best.get("peak_views_per_hour")), v_hour), 2)
        current["intel"] = _analyze_account_intelligence(current)
        current.pop("access_token", None)
        return current

    all_media = []
    media_url = f"https://graph.instagram.com/{GRAPH_API_VERSION}/{ig_user_id}/media"
    inline_ok = False
    media_fetch_error = False

    try:
        next_url = media_url
        params = {
            "fields": "id,caption,media_type,media_product_type,media_url,permalink,shortcode,timestamp,like_count,comments_count,insights.metric(views)",
            "limit": 50,
            "access_token": access_token
        }
        pages = 0
        while next_url and pages < 20:
            pages += 1
            res_m = requests.get(next_url, params=params, timeout=20)
            data_m = res_m.json()
            if "data" in data_m:
                inline_ok = True
                all_media.extend(data_m["data"])
                next_url = data_m.get("paging", {}).get("next")
                params = None
            else:
                break
    except Exception:
        pass

    if not inline_ok:
        all_media = []
        try:
            next_url = media_url
            params = {
                "fields": "id,caption,media_type,media_product_type,media_url,permalink,shortcode,timestamp,like_count,comments_count",
                "limit": 50,
                "access_token": access_token
            }
            pages = 0
            while next_url and pages < 20:
                pages += 1
                res_m = requests.get(next_url, params=params, timeout=20)
                data_m = res_m.json()
                if "data" in data_m:
                    all_media.extend(data_m["data"])
                    next_url = data_m.get("paging", {}).get("next")
                    params = None
                else:
                    if "error" in data_m:
                        media_fetch_error = True
                    break
        except Exception:
            media_fetch_error = True

    prev_views_by_post_id = {
        str(p.get("id")): _safe_int(p.get("views"))
        for p in prev_posts_list if isinstance(p, dict) and p.get("id")
    }
    prev_gain_by_post_id = {
        str(p.get("id")): _safe_int(p.get("recent_views_gain"))
        for p in prev_posts_list if isinstance(p, dict) and p.get("id")
    }
    prev_dur_by_post_id = {
        str(p.get("id")): _safe_float(p.get("duration_sec"))
        for p in prev_posts_list if isinstance(p, dict) and p.get("id")
    }

    total_views = 0
    media_views_map = {}
    items_needing_individual_fetch = []

    for m_item in all_media:
        mid = m_item.get("id")
        insights_obj = m_item.get("insights", {})
        found_inline = False
        if isinstance(insights_obj, dict) and "data" in insights_obj:
            for metric_entry in insights_obj.get("data", []):
                vals = metric_entry.get("values", [])
                if vals and isinstance(vals[0].get("value"), (int, float)):
                    v_count = max(int(vals[0]["value"]), prev_views_by_post_id.get(str(mid), 0))
                    total_views += v_count
                    if mid:
                        media_views_map[mid] = v_count
                    found_inline = True
                    break
        if not found_inline:
            items_needing_individual_fetch.append(m_item)

    if items_needing_individual_fetch:
        with ThreadPoolExecutor(max_workers=6) as pool:
            future_by_id = {
                item.get("id"): pool.submit(_fetch_single_media_views, item, access_token)
                for item in items_needing_individual_fetch if item.get("id")
            }
            for mid, fut in future_by_id.items():
                try:
                    fetched_v = int(fut.result() or 0)
                    best_v = max(fetched_v, prev_views_by_post_id.get(str(mid), 0))
                    media_views_map[mid] = best_v
                    total_views += best_v
                except Exception:
                    fallback_v = prev_views_by_post_id.get(str(mid), 0)
                    media_views_map[mid] = fallback_v
                    total_views += fallback_v

    media_durations_map = {}
    items_needing_duration = []
    for m_item in all_media:
        mid = str(m_item.get("id", ""))
        cached_dur = max(prev_dur_by_post_id.get(mid, 0.0), MEDIA_DURATION_CACHE.get(mid, 0.0))
        if cached_dur > 0:
            media_durations_map[mid] = cached_dur
        elif m_item.get("media_url"):
            items_needing_duration.append(m_item)

    if items_needing_duration:
        with ThreadPoolExecutor(max_workers=8) as pool:
            dur_futures = {
                str(item.get("id")): pool.submit(_probe_video_duration_seconds, item)
                for item in items_needing_duration if item.get("id")
            }
            for mid, fut in dur_futures.items():
                try:
                    d_sec = _safe_float(fut.result())
                    if d_sec > 0:
                        media_durations_map[mid] = d_sec
                except Exception:
                    pass

    posts_ranked = []
    for m_item in all_media:
        mid = str(m_item.get("id", ""))
        old_v = prev_views_by_post_id.get(mid, 0)
        v_count = int(media_views_map.get(mid, old_v))
        recent_gain = (v_count - old_v) if (v_count > old_v and old_v > 0) else prev_gain_by_post_id.get(mid, 0)
        dur_sec = round(max(media_durations_map.get(mid, 0.0), prev_dur_by_post_id.get(mid, 0.0)), 1)

        shortcode = m_item.get("shortcode", "")
        permalink = (m_item.get("permalink") or "").strip()
        if not permalink and shortcode:
            permalink = f"https://www.instagram.com/reel/{shortcode}/"

        reels_link = permalink
        if shortcode:
            reels_link = f"https://www.instagram.com/reel/{shortcode}/"
        elif "/p/" in permalink:
            reels_link = permalink.replace("/p/", "/reel/")

        raw_caption = (m_item.get("caption") or "").strip().replace("\n", " ")
        short_caption = (raw_caption[:65] + "...") if len(raw_caption) > 65 else (raw_caption or "Sem legenda")
        ts_raw = m_item.get("timestamp", "")
        ts_fmt = ts_raw[:16].replace("T", " ") if ts_raw else ""

        posts_ranked.append({
            "id": mid,
            "views": v_count,
            "recent_views_gain": recent_gain,
            "duration_sec": dur_sec,
            "permalink": permalink or reels_link,
            "reels_url": reels_link or permalink,
            "shortcode": shortcode,
            "caption": short_caption,
            "media_type": m_item.get("media_product_type") or m_item.get("media_type") or "REELS",
            "timestamp": ts_fmt,
            "timestamp_raw": ts_raw,
            "like_count": _safe_int(m_item.get("like_count")),
            "comments_count": _safe_int(m_item.get("comments_count"))
        })

    posts_ranked.sort(key=lambda x: _safe_int(x.get("views")), reverse=True)

    best_total_views = max(total_views, prev_views)
    updated_history = _merge_views_history(
        previous_best.get("views_history"),
        [],
        current_views=best_total_views,
        current_ts=now_ts
    )

    current = merge_best_account_data(
        previous_best,
        {
            **current,
            "posts_list": posts_ranked if len(posts_ranked) > 0 else prev_posts_list,
            "followers_count": max(fetched_followers or 0, prev_followers),
            "total_views": best_total_views,
            "media_count": max(fetched_media_count or 0, len(posts_ranked), prev_media_count),
            "metrics_updated_at": now_str if not media_fetch_error else prev_updated_at,
            "views_history": updated_history
        }
    )

    current.pop("access_token", None)
    return current


def refresh_all_accounts_to_json():
    with SYNC_LOCK:
        saved_state = get_saved_state(force_redis=not REDIS_BOOTSTRAPPED)
        saved_accounts = saved_state.get("accounts", {}) if isinstance(saved_state, dict) else {}
        env_accounts = get_env_accounts()

        for d_id in list(MEMORY_DELETED_IDS):
            saved_accounts.pop(d_id, None)
            env_accounts.pop(d_id, None)

        if not env_accounts:
            if saved_accounts:
                saved_state["accounts"] = sort_accounts_by_views_desc(saved_accounts)
                save_current_state(saved_state)
            return saved_state

        acc_ids = [aid for aid in env_accounts.keys() if str(aid).strip() not in MEMORY_DELETED_IDS]
        new_accounts_map = {
            k: v for k, v in saved_accounts.items() if str(k).strip() not in MEMORY_DELETED_IDS
        }

        with ThreadPoolExecutor(max_workers=5) as pool:
            futures = {
                acc_id: pool.submit(
                    fetch_account_current_metrics,
                    env_accounts[acc_id],
                    saved_accounts.get(str(acc_id), {})
                )
                for acc_id in acc_ids
            }
            for acc_id, fut in futures.items():
                uid_s = str(acc_id).strip()
                if uid_s in MEMORY_DELETED_IDS:
                    continue
                try:
                    updated_acc = fut.result()
                    new_accounts_map[uid_s] = merge_best_account_data(
                        saved_accounts.get(uid_s, {}), updated_acc
                    )
                except Exception as e:
                    print(f"[AVISO MÉTRICAS] Falha ao atualizar conta {uid_s}: {e}", flush=True)
                    if uid_s in saved_accounts:
                        new_accounts_map[uid_s] = saved_accounts[uid_s]

        sorted_accounts_map = sort_accounts_by_views_desc(new_accounts_map)
        g_peak_min, g_peak_hour = _compute_global_peaks_from_accounts(
            sorted_accounts_map,
            prev_peak_min=_safe_float(saved_state.get("global_peak_views_per_min")),
            prev_peak_hour=_safe_float(saved_state.get("global_peak_views_per_hour"))
        )

        now_ts = time.time()
        now_str = datetime.now(BRT).strftime("%d/%m/%Y %H:%M:%S")

        updated_state = {
            "last_global_sync_ts": now_ts,
            "last_global_sync_str": now_str,
            "global_peak_views_per_min": g_peak_min,
            "global_peak_views_per_hour": g_peak_hour,
            "deleted_ids": sorted(list(MEMORY_DELETED_IDS)),
            "custom_tokens": dict(MEMORY_CUSTOM_TOKENS),
            "accounts": sorted_accounts_map
        }
        save_current_state(updated_state)
        return updated_state


# ==============================================================================
# THREAD LOCAL DE 5 EM 5 MINUTOS
# ==============================================================================

def background_5min_loop():
    time.sleep(5)
    while True:
        try:
            if not REDIS_BOOTSTRAPPED:
                state = get_saved_state(force_redis=True)
                last_ts = state.get("last_global_sync_ts", 0)
            else:
                last_ts = MEMORY_LAST_SYNC_TS

            if time.time() - last_ts >= 295 or not MEMORY_CACHE_ACCOUNTS:
                refresh_all_accounts_to_json()
        except Exception as e:
            print(f"[ERRO LOOP 5 MIN]: {e}", flush=True)
        time.sleep(60)


bg_thread = threading.Thread(target=background_5min_loop, daemon=True)
bg_thread.start()


# ==============================================================================
# TEMPLATE HTML (ORDENAÇÃO CLICÁVEL EM TODAS AS COLUNAS + RECORDES GLOBAIS SOMADOS)
# ==============================================================================

HTML_TEMPLATE = r"""
<!DOCTYPE html>
<html lang="pt-BR">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Monitor 24h & Inteligência Anti-Queda — Contas Conectadas</title>
    <style>
        :root {
            --bg: #0f172a;
            --card: #1e293b;
            --text: #f8fafc;
            --muted: #94a3b8;
            --border: #334155;
            --success: #22c55e;
            --warning: #f59e0b;
            --info: #38bdf8;
            --error: #ef4444;
        }
        * { box-sizing: border-box; font-family: 'Segoe UI', system-ui, sans-serif; }
        body { background: var(--bg); color: var(--text); margin: 0; padding: 20px; }
        .container { max-width: 1680px; margin: 0 auto; display: grid; gap: 18px; }
        .card { background: var(--card); border: 1px solid var(--border); border-radius: 12px; padding: 18px 20px; }
        h1, h2, h3 { margin: 0; }
        .hint { font-size: 0.82rem; color: var(--muted); margin-top: 6px; line-height: 1.4; }
        table { width: 100%; border-collapse: collapse; margin-top: 12px; font-size: 0.84rem; }
        th, td { border-bottom: 1px solid var(--border); padding: 10px 7px; text-align: left; vertical-align: middle; }
        th { color: var(--muted); font-weight: 600; }
        th.sortable-th {
            cursor: pointer;
            user-select: none;
            transition: background 0.15s, color 0.15s;
            position: relative;
            white-space: nowrap;
        }
        th.sortable-th:hover {
            background: rgba(56, 189, 248, 0.1);
            color: #f8fafc;
        }
        th.sortable-th.active-sort {
            color: #38bdf8;
            background: rgba(56, 189, 248, 0.14);
        }
        .sort-arrow {
            display: inline-block;
            margin-left: 4px;
            font-size: 0.76rem;
            color: #64748b;
        }
        th.sortable-th.active-sort .sort-arrow {
            color: #38bdf8;
            font-weight: 800;
        }
        .badge { padding: 4px 8px; border-radius: 6px; font-size: 0.76rem; font-weight: 600; display: inline-block; }
        .badge.success { background: rgba(34, 197, 94, 0.2); color: #4ade80; border: 1px solid rgba(34, 197, 94, 0.35); }
        .badge.warning { background: rgba(245, 158, 11, 0.2); color: #fbbf24; border: 1px solid rgba(245, 158, 11, 0.35); }
        .badge.info { background: rgba(56, 189, 248, 0.2); color: #38bdf8; border: 1px solid rgba(56, 189, 248, 0.35); }
        .badge.error { background: rgba(239, 68, 68, 0.2); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.35); }
        .metric-val { font-weight: 700; color: #f8fafc; font-size: 0.93rem; }
        button.small-btn {
            margin-top: 0; padding: 7px 13px; width: auto; font-size: 0.82rem; border-radius: 6px;
            background: #3b82f6; color: white; border: none; font-weight: 600; cursor: pointer; transition: 0.2s;
        }
        button.small-btn:hover { background: #2563eb; }
        button.small-btn.secondary { background: #0f766e; }
        button.small-btn.secondary:hover { background: #115e59; }
        .posts-toggle-btn {
            margin-top: 0;
            padding: 3px 7px;
            width: auto;
            font-size: 0.78rem;
            border-radius: 5px;
            background: #334155;
            color: #38bdf8;
            border: 1px solid #475569;
            cursor: pointer;
            line-height: 1;
            display: inline-flex;
            align-items: center;
            justify-content: center;
            transition: 0.15s;
        }
        .posts-toggle-btn:hover {
            background: #475569;
            color: #ffffff;
            border-color: #38bdf8;
        }
        .delete-acc-btn {
            padding: 6px 9px;
            border-radius: 6px;
            background: rgba(239, 68, 68, 0.16);
            color: #f87171;
            border: 1px solid rgba(239, 68, 68, 0.4);
            cursor: pointer;
            font-size: 0.85rem;
            line-height: 1;
            transition: 0.18s;
            display: inline-flex;
            align-items: center;
            justify-content: center;
        }
        .delete-acc-btn:hover {
            background: #ef4444;
            color: #ffffff;
            border-color: #ef4444;
            transform: scale(1.05);
        }
        .posts-dropdown-row { background: #0b1120; }
        .posts-dropdown-box {
            padding: 12px 14px;
            border-radius: 8px;
            background: #111a2e;
            border: 1px solid var(--border);
            max-height: 320px;
            overflow-y: auto;
        }
        .post-rank-item {
            display: flex;
            justify-content: space-between;
            align-items: center;
            gap: 12px;
            padding: 8px 10px;
            border-bottom: 1px solid #1e293b;
            font-size: 0.83rem;
        }
        .post-rank-item:last-child { border-bottom: none; }
        .post-rank-link {
            color: #38bdf8;
            text-decoration: none;
            font-weight: 600;
            word-break: break-all;
        }
        .post-rank-link:hover {
            text-decoration: underline;
            color: #7dd3fc;
        }
        .duration-pill {
            background: rgba(168, 85, 247, 0.18);
            color: #e9d5ff;
            border: 1px solid rgba(168, 85, 247, 0.4);
            padding: 3px 8px;
            border-radius: 6px;
            font-size: 0.76rem;
            font-weight: 700;
            white-space: nowrap;
        }
        .top-stats-bar {
            display: flex;
            gap: 14px;
            flex-wrap: wrap;
            font-size: 0.85rem;
            color: var(--muted);
            margin-top: 8px;
            align-items: center;
        }
        .record-pill {
            background: rgba(245, 158, 11, 0.12);
            border: 1px solid rgba(245, 158, 11, 0.35);
            padding: 4px 10px;
            border-radius: 8px;
            color: #fde68a;
        }
        .intel-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(310px, 1fr));
            gap: 14px;
            margin-top: 12px;
        }
        .intel-box {
            background: #0f172a;
            border: 1px solid var(--border);
            border-radius: 10px;
            padding: 13px 15px;
        }
        .intel-box h3 {
            font-size: 0.92rem;
            margin-bottom: 8px;
            display: flex;
            align-items: center;
            gap: 6px;
        }
        .intel-item {
            font-size: 0.82rem;
            padding: 6px 0;
            border-bottom: 1px dashed #1e293b;
            display: flex;
            justify-content: space-between;
            align-items: center;
            gap: 8px;
        }
        .intel-item:last-child { border-bottom: none; }
        .progress-bar-bg {
            width: 100%;
            height: 6px;
            background: #0f172a;
            border-radius: 4px;
            overflow: hidden;
            margin-top: 4px;
            border: 1px solid #334155;
        }
        .progress-bar-fill {
            height: 100%;
            border-radius: 4px;
        }
        .sub-meta {
            color: var(--muted);
            font-size: 0.75rem;
            display: block;
            margin-top: 2px;
        }
        .add-account-form {
            display: grid;
            grid-template-columns: 2fr 1fr auto;
            gap: 12px;
            align-items: end;
            margin-top: 14px;
        }
        @media (max-width: 860px) {
            .add-account-form {
                grid-template-columns: 1fr;
            }
        }
        .field-group label {
            display: block;
            font-size: 0.79rem;
            color: var(--muted);
            margin-bottom: 5px;
            font-weight: 600;
        }
        .input-dark {
            width: 100%;
            padding: 9px 12px;
            border-radius: 7px;
            border: 1px solid var(--border);
            background: #0f172a;
            color: #f8fafc;
            font-size: 0.85rem;
            outline: none;
            transition: border-color 0.15s;
        }
        .input-dark:focus {
            border-color: #38bdf8;
        }
        .btn-add-acc {
            padding: 9px 18px;
            border-radius: 7px;
            background: #22c55e;
            color: #052e16;
            border: none;
            font-weight: 700;
            font-size: 0.85rem;
            cursor: pointer;
            transition: 0.18s;
            white-space: nowrap;
            height: 38px;
        }
        .btn-add-acc:hover {
            background: #16a34a;
            color: #ffffff;
        }
        .btn-add-acc:disabled {
            opacity: 0.65;
            cursor: not-allowed;
        }
        .modal-overlay {
            position: fixed;
            inset: 0;
            background: rgba(2, 6, 23, 0.78);
            display: none;
            align-items: center;
            justify-content: center;
            z-index: 9999;
            padding: 16px;
            backdrop-filter: blur(3px);
        }
        .modal-card {
            background: #1e293b;
            border: 1px solid #ef4444;
            border-radius: 12px;
            max-width: 440px;
            width: 100%;
            padding: 22px 24px;
            box-shadow: 0 20px 50px rgba(0, 0, 0, 0.6);
        }
        .modal-title {
            font-size: 1.08rem;
            font-weight: 700;
            color: #f87171;
            display: flex;
            align-items: center;
            gap: 8px;
            margin-bottom: 10px;
        }
        .modal-body {
            font-size: 0.88rem;
            color: #cbd5e1;
            line-height: 1.5;
            margin-bottom: 18px;
        }
        .modal-actions {
            display: flex;
            justify-content: flex-end;
            gap: 10px;
        }
        .btn-cancel {
            padding: 8px 15px;
            border-radius: 7px;
            background: #334155;
            color: #e2e8f0;
            border: 1px solid #475569;
            font-weight: 600;
            font-size: 0.84rem;
            cursor: pointer;
        }
        .btn-cancel:hover { background: #475569; }
        .btn-confirm-delete {
            padding: 8px 16px;
            border-radius: 7px;
            background: #ef4444;
            color: #ffffff;
            border: none;
            font-weight: 700;
            font-size: 0.84rem;
            cursor: pointer;
        }
        .btn-confirm-delete:hover { background: #dc2626; }
    </style>
</head>
<body>
<div class="container">
    <div style="display:flex; justify-content:space-between; align-items:center; flex-wrap:wrap; gap:12px;">
        <div>
            <h1>Painel de Monitoramento 24h & Inteligência Anti-Queda (v2)</h1>
            <div class="hint">
                🛡️ <b>Cadência Blindada (Padrão Vencedor):</b> Máximo de <b>2 lotes/24h</b> com intervalo de <b>3h30–4h</b> entre o 1º e o 2º lote, seguido de <b>descanso obrigatório de 12h–24h</b> e freio automático se a média de views do último lote cair.
            </div>
        </div>
        <div style="display:flex; gap:8px; flex-wrap:wrap; align-items:center;">
            {% if upstash_active and redis_bootstrapped %}
            <div class="badge success" style="font-size:0.82rem; padding:8px 12px;">
                ☁️ Banco Persistente: <b>Upstash Redis Sincronizado</b>
            </div>
            {% elif upstash_active %}
            <div class="badge warning" style="font-size:0.82rem; padding:8px 12px;">
                ⚠️ Upstash Configurado (Aguardando Conexão...)
            </div>
            {% else %}
            <div class="badge warning" style="font-size:0.82rem; padding:8px 12px;">
                ⚠️ Upstash Redis Não Configurado (Usando /tmp)
            </div>
            {% endif %}
            <div class="badge info" style="font-size:0.86rem; padding:8px 12px;">
                🔄 Última Atualização: <b>{{ last_sync }}</b>
            </div>
            <div class="badge success" style="font-size:0.82rem; padding:8px 12px;">
                ⏱️ Recarregando tela em: <span id="reloadCountdown">60s</span>
            </div>
        </div>
    </div>

    <!-- CENTRAL DE COMANDO E ALOCAÇÃO DE LOTES (MOTOR INTELIGENTE V2) -->
    <div class="card" style="border-color:#3b82f6;">
        <div style="display:flex; justify-content:space-between; align-items:center; flex-wrap:wrap; gap:10px;">
            <div>
                <h2 style="color:#60a5fa;">🧠 Central Tática de Alocação de Lotes (3h30 entre Lotes + Descanso 12h–24h)</h2>
                <div class="hint">
                    Evita o erro de postar de 2h em 2h quando vídeos antigos estão viralizando: avalia a <b>média real do último lote</b>, <b>quantidade de lotes em 24h</b> e <b>tempo de descanso</b>.
                </div>
            </div>
            <span class="badge info">API Automação: <code>/api/smart_queue</code></span>
        </div>

        <div class="intel-grid">
            <!-- COLUNA 1: CONTAS PRONTAS PARA RECEBER LOTE AGORA -->
            <div class="intel-box" style="border-color:rgba(34,197,94,0.4);">
                <h3 style="color:#4ade80;">🔥 Prontas p/ Lote Agora (Janela 3h30+ ou 12h+ Cumprida)</h3>
                {% if ready_to_post_list %}
                    {% for item in ready_to_post_list %}
                    <div class="intel-item">
                        <div>
                            <b>@{{ item.username }}</b>
                            <span class="sub-meta">{{ item.intel.action_title }} • Último {{ item.intel.last_post_age_str }} ({{ item.intel.batches_24h_count }}/2 lotes 24h)</span>
                        </div>
                        <div style="text-align:right;">
                            <span class="badge success">{{ item.views_per_min | fmt_rate }}/min</span>
                            <span class="sub-meta">Sugerido: <b>{{ item.intel.recommended_batch_size }} vídeos</b></span>
                        </div>
                    </div>
                    {% endfor %}
                {% else %}
                    <div class="hint">Nenhuma conta livre para lote neste momento (todas cumprindo janela de 3h30 ou descanso de 12h–24h).</div>
                {% endif %}
            </div>

            <!-- COLUNA 2: CONTAS EM MATURAÇÃO (3H30) OU DESCANSO DE CICLO (12H-24H) -->
            <div class="intel-box" style="border-color:rgba(245,158,11,0.4);">
                <h3 style="color:#fbbf24;">⏳ Em Maturação (3h30) ou Descanso de Ciclo (12h–24h)</h3>
                {% if maturing_cooldown_list %}
                    {% for item in maturing_cooldown_list %}
                    <div class="intel-item">
                        <div>
                            <b>@{{ item.username }}</b>
                            <span class="sub-meta">
                                {{ item.intel.action_title }} • Lote {{ item.intel.last_post_age_str }} (média {{ item.intel.last_batch_avg_views | fmt_num }} views/post)
                            </span>
                        </div>
                        <div style="text-align:right;">
                            <span class="badge warning">{{ item.intel.batches_24h_count }}/2 lotes (24h)</span>
                            <span class="sub-meta" style="color:#fbbf24;">{{ item.intel.posts_last_24h_count }} vídeos em 24h</span>
                        </div>
                    </div>
                    {% endfor %}
                {% else %}
                    <div class="hint">Nenhuma conta em janela de espera ou descanso de ciclo.</div>
                {% endif %}
            </div>

            <!-- COLUNA 3: FREIO ANTI-QUEDA / ZUMBIS / RECONECTAR -->
            <div class="intel-box" style="border-color:rgba(239,68,68,0.4);">
                <h3 style="color:#f87171;">🛑 Freio Anti-Queda, Zumbis ou Reconectar</h3>
                {% if paused_or_down_list %}
                    {% for item in paused_or_down_list %}
                    <div class="intel-item">
                        <div>
                            <b>@{{ item.username }}</b>
                            <span class="sub-meta">{{ item.intel.action_title }}</span>
                        </div>
                        <div style="text-align:right;">
                            <span class="badge {{ item.intel.action_badge }}">{{ item.total_views | fmt_num }} views</span>
                            <span class="sub-meta">Último lote: {{ item.intel.last_batch_avg_views | fmt_num }}/post</span>
                        </div>
                    </div>
                    {% endfor %}
                {% else %}
                    <div class="hint">Todas as contas estão saudáveis e sem sinais de throttling.</div>
                {% endif %}
            </div>
        </div>
    </div>

    <!-- TABELA PRINCIPAL DE CONTAS CONECTADAS -->
    <div class="card">
        <div style="display:flex; justify-content:space-between; align-items:flex-start; flex-wrap:wrap; gap:12px;">
            <div>
                <h2 id="mainTableTitle">Contas Conectadas ({{ accounts|length }}) — Clique em qualquer coluna para ordenar ↕</h2>
                <div class="top-stats-bar">
                    <span>Seguidores Totais: <b style="color:#4ade80;">{{ total_followers | fmt_num }}</b></span>
                    <span>Visualizações Totais: <b style="color:#38bdf8;">{{ total_views | fmt_num }}</b></span>
                    <span>Views / Min Atuais: <b style="color:#fbbf24;">{{ total_views_per_min | fmt_rate }}/min</b></span>
                    <span>Views / Hora Atuais: <b style="color:#c084fc;">{{ total_views_per_hour | fmt_rate }}/h</b></span>
                    <span class="record-pill" title="Recorde de visualizações por minuto somando todas as contas simultaneamente">
                        🏆 Recorde Min (Todas as Contas): <b style="color:#fbbf24;">{{ global_peak_min_val | fmt_rate }}/min</b>
                    </span>
                    <span class="record-pill" title="Recorde de visualizações por hora somando todas as contas simultaneamente">
                        🏆 Recorde Hora (Todas as Contas): <b style="color:#f472b6;">{{ global_peak_hour_val | fmt_rate }}/h</b>
                    </span>
                </div>
            </div>
            <div style="display:flex; gap:8px; flex-wrap:wrap;">
                <button type="button" class="small-btn secondary" onclick="copiarSnapshotVercel(this)" title="Copia o JSON completo com tokens + seguidores + views atuais">
                    💾 Copiar Snapshot JSON
                </button>
                <button type="button" class="small-btn" onclick="atualizarMetricasContas(this)">
                    🔄 Atualizar Seguidores, Visualizações e Posts
                </button>
            </div>
        </div>

        {% if accounts %}
        <div style="overflow-x:auto;">
            <table id="accountsTable">
                <thead>
                    <tr>
                        <th class="sortable-th" data-col="0" data-type="number" onclick="ordenarTabelaPorColuna(0)" style="width:92px; text-align:center;" title="Clique para ordenar por quantidade de posts">
                            Rank / Posts <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="1" data-type="string" onclick="ordenarTabelaPorColuna(1)" title="Clique para ordenar por @Username">
                            @Username <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="2" data-type="number" onclick="ordenarTabelaPorColuna(2)" title="Clique para ordenar por Status API e Cota 24h">
                            Status API & Cota 24h <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="3" data-type="number" onclick="ordenarTabelaPorColuna(3)" title="Clique para ordenar por Seguidores">
                            Seguidores & Conv. <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th active-sort" data-col="4" data-type="number" onclick="ordenarTabelaPorColuna(4)" title="Clique para ordenar por Visualizações Totais">
                            Visualizações Totais <span class="sort-arrow">▼</span>
                        </th>
                        <th class="sortable-th" data-col="5" data-type="number" onclick="ordenarTabelaPorColuna(5)" title="Clique para ordenar por Views / Min">
                            Views / Min (Atual) <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="6" data-type="number" onclick="ordenarTabelaPorColuna(6)" title="Clique para ordenar por Views / Hora">
                            Views / Hora (Atual) <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="7" data-type="number" onclick="ordenarTabelaPorColuna(7)" title="Clique para ordenar pelos Recordes da conta">
                            🏆 Recordes (Min / Hora) <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="8" data-type="number" onclick="ordenarTabelaPorColuna(8)" style="min-width:135px;" title="Clique para ordenar pelo Índice de Atividade (%)">
                            Índice Atividade & Ritmo <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="9" data-type="number" onclick="ordenarTabelaPorColuna(9)" title="Clique para ordenar pelo tempo desde o último lote">
                            Último Lote & Fadiga 24h <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="10" data-type="number" onclick="ordenarTabelaPorColuna(10)" style="min-width:250px;" title="Clique para ordenar pela prioridade da Recomendação Anti-Queda">
                            🧠 Recomendação Anti-Queda <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="11" data-type="number" onclick="ordenarTabelaPorColuna(11)" title="Clique para ordenar pela data/hora da Última Coleta">
                            Última Coleta <span class="sort-arrow">↕</span>
                        </th>
                        <th class="sortable-th" data-col="12" data-type="string" onclick="ordenarTabelaPorColuna(12)" style="width:65px; text-align:center;" title="Clique para ordenar">
                            Excluir <span class="sort-arrow">↕</span>
                        </th>
                    </tr>
                </thead>
                <tbody id="accountsTableBody">
                    {% for acc_id, acc in accounts.items() %}
                    {% set posts_ordenados = acc.get('posts_list', []) %}
                    {% set intel = acc.get('intel', {}) %}
                    {% set badge_status = acc.get('account_status_badge', 'success') %}
                    {% set status_rank = 3 if badge_status == 'success' else (2 if badge_status == 'warning' else 1) %}
                    <tr id="acc_row_{{ acc_id }}" class="acc-main-row" data-acc-id="{{ acc_id }}">
                        <td style="text-align:center; white-space:nowrap;" data-sort="{{ acc.get('media_count', 0) }}">
                            <div style="display:inline-flex; align-items:center; gap:6px;">
                                <span class="badge info rank-badge-num" style="min-width:30px; text-align:center;">#{{ loop.index }}</span>
                                <button type="button" id="btn_toggle_{{ acc_id }}" class="posts-toggle-btn" onclick="togglePostsConta('{{ acc_id }}', this)" title="Abrir/fechar lista de posts e diagnóstico de retenção">
                                    ↓
                                </button>
                            </div>
                        </td>
                        <td data-sort="{{ acc.username | lower }}">
                            <b>@{{ acc.username }}</b>
                            <span class="sub-meta">ID: {{ acc.ig_user_id }}</span>
                        </td>
                        <td data-sort="{{ status_rank * 1000 + (100 - intel.get('posts_last_24h_count', 0)) }}">
                            <span class="badge {{ acc.get('account_status_badge', 'success') }}" title="{{ acc.get('account_status_detail', '') }}">
                                {{ acc.get('account_status', 'Ativa') }}
                            </span>
                            <span class="sub-meta">{{ acc.get('account_status_detail', '') }}</span>
                        </td>
                        <td data-sort="{{ acc.get('followers_count', 0) }}">
                            <span class="metric-val">{{ acc.get('followers_count') | fmt_num }}</span>
                            <span class="sub-meta" title="Seguidores ganhos a cada 1.000 visualizações">
                                🎯 {{ intel.get('followers_per_1k_views', 0) }} seg / 1k views
                            </span>
                        </td>
                        <td data-sort="{{ acc.get('total_views', 0) }}">
                            <span class="metric-val" style="color:#38bdf8;">{{ acc.get('total_views') | fmt_num }}</span>
                            <span class="sub-meta">
                                {{ acc.get('media_count', 0) }} posts • 🏆 {{ intel.get('hits_10k', 0) }} hits (+10k)
                            </span>
                        </td>
                        <td data-sort="{{ acc.get('views_per_min', 0) }}">
                            <span class="metric-val" style="color:#fbbf24;">{{ acc.get('views_per_min', 0) | fmt_rate }}/min</span>
                            <span class="sub-meta" style="color:{{ intel.get('trend_color', '#94a3b8') }}; font-weight:600;">
                                {{ intel.get('trend_label', '—') }}
                            </span>
                        </td>
                        <td data-sort="{{ acc.get('views_per_hour', 0) }}">
                            <span class="metric-val" style="color:#c084fc;">{{ acc.get('views_per_hour', 0) | fmt_rate }}/h</span>
                        </td>
                        <td data-sort="{{ acc.get('peak_views_per_min', 0) }}">
                            <span style="color:#fde047; font-weight:700;">{{ acc.get('peak_views_per_min', 0) | fmt_rate }}/m</span>
                            <span class="sub-meta" style="color:#f472b6; font-weight:600;">
                                {{ acc.get('peak_views_per_hour', 0) | fmt_rate }}/h
                            </span>
                        </td>
                        <td data-sort="{{ intel.get('activity_index_pct', 0) }}">
                            <div style="display:flex; justify-content:space-between; font-size:0.78rem;">
                                <span>Saúde vs Pico:</span>
                                <b style="color:#f8fafc;">{{ intel.get('activity_index_pct', 0) }}%</b>
                            </div>
                            <div class="progress-bar-bg">
                                <div class="progress-bar-fill" style="width:{{ intel.get('activity_index_pct', 0) }}%; background:{% if intel.get('activity_index_pct', 0) >= 60 %}#22c55e{% elif intel.get('activity_index_pct', 0) >= 20 %}#38bdf8{% else %}#ef4444{% endif %};"></div>
                            </div>
                            <span class="sub-meta">
                                Top 1 post = {{ intel.get('top_post_share_pct', 0) }}% das views
                            </span>
                        </td>
                        <td data-sort="{{ intel.get('mins_since_last_post') if intel.get('mins_since_last_post') is not none else 9999999 }}">
                            <b style="color:#e2e8f0; font-size:0.81rem;">Último: {{ intel.get('last_post_age_str', '—') }}</b>
                            <span class="sub-meta" style="color:{% if intel.get('batches_24h_count', 0) >= 2 %}#fbbf24{% else %}#4ade80{% endif %}; font-weight:600;">
                                📦 24h: {{ intel.get('batches_24h_count', 0) }}/2 lotes ({{ intel.get('posts_last_24h_count', 0) }} vídeos)
                            </span>
                            <span class="sub-meta" style="color:#cbd5e1;">
                                Média últ. lote: <b>{{ intel.get('last_batch_avg_views', 0) | fmt_num }}</b> views/post
                            </span>
                            <span class="sub-meta" style="color:#38bdf8;">
                                ⏰ {{ intel.get('best_window_str', '—') }}
                            </span>
                        </td>
                        <td data-sort="{{ intel.get('priority_score', 0) }}">
                            <span class="badge {{ intel.get('action_badge', 'info') }}">
                                {{ intel.get('action_title', '—') }}
                            </span>
                            <span class="sub-meta" style="max-width:275px; white-space:normal; line-height:1.3;">
                                {{ intel.get('action_detail', '') }}
                            </span>
                        </td>
                        <td data-sort="{{ acc.get('updated_at_ts', 0) }}">
                            <span style="font-size:0.8rem;">{{ acc.get('metrics_updated_at', '—') }}</span>
                        </td>
                        <td style="text-align:center;" data-sort="{{ acc.username | lower }}">
                            <button type="button" class="delete-acc-btn" onclick="abrirModalExclusao('{{ acc_id }}', '{{ acc.username }}')" title="Remover @{{ acc.username }} do painel">
                                🗑️
                            </button>
                        </td>
                    </tr>
                    <tr id="posts_row_{{ acc_id }}" class="posts-dropdown-row" style="display:none;">
                        <td colspan="13" style="padding:10px 16px;">
                            <div class="posts-dropdown-box">
                                <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:8px; flex-wrap:wrap; gap:8px;">
                                    <b style="color:#38bdf8; font-size:0.88rem;">
                                        📊 Posts / Reels de @{{ acc.username }} — Diagnóstico de Tração, Duração do Vídeo e Horário Real (BRT)
                                    </b>
                                    <span style="color:var(--muted); font-size:0.78rem;">
                                        Total: {{ posts_ordenados|length }} post(s) |
                                        🏆 Hits +10k: <b>{{ intel.get('hits_10k', 0) }} ({{ intel.get('hit_rate_10k_pct', 0) }}%)</b> |
                                        💀 Morte Súbita (&lt;400 views após 2h): <b>{{ intel.get('dead_posts_count', 0) }}</b>
                                    </span>
                                </div>
                                {% if posts_ordenados %}
                                    {% for p in posts_ordenados %}
                                    <div class="post-rank-item">
                                        <div style="display:flex; align-items:center; gap:10px; flex-wrap:wrap;">
                                            <span class="badge info" style="min-width:34px; text-align:center;">#{{ loop.index }}</span>
                                            <span style="font-weight:700; color:#4ade80; min-width:120px;">
                                                👁️ {{ p.get('views', 0) | fmt_num }} views
                                            </span>
                                            {% if p.get('recent_views_gain', 0) > 0 %}
                                            <span class="badge success" title="Visualizações ganhas desde a última sincronização">
                                                +{{ p.get('recent_views_gain') | fmt_num }} agora
                                            </span>
                                            {% endif %}
                                            <span class="badge {{ p.get('diag_badge', 'info') }}">
                                                {{ p.get('diag_label', '—') }}
                                            </span>
                                            <a href="{{ p.get('reels_url') or p.get('permalink') or '#' }}" target="_blank" rel="noopener noreferrer" class="post-rank-link">
                                                🔗 {{ p.get('reels_url') or p.get('permalink') or ('ID: ' ~ p.get('id')) }}
                                            </a>
                                            <span class="duration-pill" title="Duração exata do vídeo em segundos">
                                                ⏱️ {{ p.get('duration_sec', 0) | fmt_dur }}
                                            </span>
                                        </div>
                                        <div style="color:var(--muted); font-size:0.78rem; text-align:right; white-space:nowrap;">
                                            <span>⏳ Idade: <b style="color:#e2e8f0;">{{ p.get('age_human', '—') }}</b></span>
                                            {% if p.get('timestamp_brt') %}
                                            <span style="margin-left:8px; color:#94a3b8;">(📅 {{ p.get('timestamp_brt') }} BRT)</span>
                                            {% endif %}
                                        </div>
                                    </div>
                                    {% endfor %}
                                {% else %}
                                    <div class="hint" style="margin:0; color:#fbbf24;">
                                        Nenhum post carregado ainda ou esta conta caiu antes da primeira sincronização de posts.
                                    </div>
                                {% endif %}
                            </div>
                        </td>
                    </tr>
                    {% endfor %}
                </tbody>
            </table>
        </div>
        {% else %}
        <p class="hint" style="margin-top:16px;">Nenhuma conta configurada ainda. Adicione sua primeira conta no painel abaixo.</p>
        {% endif %}
    </div>

    <!-- SEÇÃO NO FINAL DA PÁGINA: ADICIONAR OU RECONECTAR CONTA COM 1 OU 2 DADOS -->
    <div class="card" style="border-color:rgba(34, 197, 94, 0.45);">
        <div style="display:flex; justify-content:space-between; align-items:center; flex-wrap:wrap; gap:10px;">
            <div>
                <h2 style="color:#4ade80; font-size:1.1rem;">➕ Adicionar ou Reconectar Conta Rápido</h2>
                <div class="hint">
                    Basta colar o <b>Access Token</b> (o sistema descobre o ID, @username, seguidores e vídeos sozinho). Se quiser, você também pode informar o <b>ID da Conta</b> opcionalmente.
                </div>
            </div>
            <span class="badge success">Persistência Automática Upstash + JSON</span>
        </div>

        <form class="add-account-form" onsubmit="adicionarNovaConta(event)">
            <div class="field-group">
                <label for="newAccToken">🔑 Access Token da Conta (IGAA... ou EAA...)</label>
                <input type="text" id="newAccToken" class="input-dark" placeholder="Cole aqui o Access Token da conta..." autocomplete="off">
            </div>
            <div class="field-group">
                <label for="newAccId">🆔 ID da Conta (Opcional — descoberto pelo Token)</label>
                <input type="text" id="newAccId" class="input-dark" placeholder="Ex: 17841400000000000 (opcional)" autocomplete="off">
            </div>
            <div>
                <button type="submit" id="btnAddAccount" class="btn-add-acc">
                    ➕ Conectar e Sincronizar
                </button>
            </div>
        </form>
        <div id="addAccountStatus" class="hint" style="margin-top:10px; display:none; font-weight:600;"></div>
    </div>
</div>

<!-- POP-UP MODAL DE CONFIRMAÇÃO DE EXCLUSÃO DE CONTA -->
<div id="deleteModalOverlay" class="modal-overlay" onclick="fecharModalSeClicarFora(event)">
    <div class="modal-card">
        <div class="modal-title">
            🗑️ Confirmar Exclusão da Conta
        </div>
        <div class="modal-body">
            Tem certeza que deseja remover a conta <b id="modalDeleteUsername" style="color:#f8fafc;">@conta</b> (ID: <code id="modalDeleteAccId">—</code>) deste painel?<br><br>
            <span style="color:#fbbf24; font-size:0.81rem;">⚠️ A conta será removida imediatamente da visualização e do banco persistente (Upstash Redis).</span>
        </div>
        <div class="modal-actions">
            <button type="button" class="btn-cancel" onclick="fecharModalExclusao()">Cancelar</button>
            <button type="button" id="btnConfirmDeleteAcc" class="btn-confirm-delete" onclick="confirmarExclusaoConta()">Sim, Excluir Conta</button>
        </div>
    </div>
</div>

<script>
    let contaPendenteExclusaoId = null;
    let contaPendenteExclusaoUser = null;
    let adicionandoContaEmAndamento = false;

    // Estado de ordenação atual (padrão: coluna 4 = Visualizações Totais, decrescente)
    let currentSortCol = 4;
    let currentSortDir = 'desc';

    function ordenarTabelaPorColuna(colIndex, forcedDir = null) {
        const table = document.getElementById('accountsTable');
        const tbody = document.getElementById('accountsTableBody');
        if (!table || !tbody) return;

        const headers = table.querySelectorAll('th.sortable-th');
        const targetHeader = table.querySelector(`th.sortable-th[data-col="${colIndex}"]`);
        if (!targetHeader) return;

        if (forcedDir) {
            currentSortCol = colIndex;
            currentSortDir = forcedDir;
        } else {
            if (currentSortCol === colIndex) {
                currentSortDir = (currentSortDir === 'desc') ? 'asc' : 'desc';
            } else {
                currentSortCol = colIndex;
                // Para texto (@Username), o 1º clique pode começar crescente (A->Z) ou decrescente;
                // para números, começa decrescente (maior -> menor), e alterna a cada clique.
                const sortType = targetHeader.getAttribute('data-type') || 'number';
                currentSortDir = (sortType === 'string') ? 'asc' : 'desc';
            }
        }

        const sortType = targetHeader.getAttribute('data-type') || 'number';
        const mainRows = Array.from(tbody.querySelectorAll('tr.acc-main-row'));

        const rowPairs = mainRows.map(mainRow => {
            const accId = mainRow.getAttribute('data-acc-id');
            const detailRow = document.getElementById('posts_row_' + accId);
            const cell = mainRow.children[colIndex];
            let rawVal = cell ? (cell.getAttribute('data-sort') ?? cell.innerText.trim()) : '';

            let parsedVal;
            if (sortType === 'number') {
                const num = parseFloat(String(rawVal).replace(',', '.'));
                parsedVal = isNaN(num) ? 0 : num;
            } else {
                parsedVal = String(rawVal).toLowerCase();
            }

            return { mainRow, detailRow, parsedVal };
        });

        rowPairs.sort((a, b) => {
            if (a.parsedVal < b.parsedVal) return currentSortDir === 'asc' ? -1 : 1;
            if (a.parsedVal > b.parsedVal) return currentSortDir === 'asc' ? 1 : -1;
            return 0;
        });

        rowPairs.forEach((pair, idx) => {
            tbody.appendChild(pair.mainRow);
            if (pair.detailRow) {
                tbody.appendChild(pair.detailRow);
            }
            const rankBadge = pair.mainRow.querySelector('.rank-badge-num');
            if (rankBadge) {
                rankBadge.innerText = '#' + (idx + 1);
            }
        });

        headers.forEach(th => {
            th.classList.remove('active-sort');
            const arrow = th.querySelector('.sort-arrow');
            if (arrow) arrow.innerText = '↕';
        });

        targetHeader.classList.add('active-sort');
        const activeArrow = targetHeader.querySelector('.sort-arrow');
        if (activeArrow) {
            activeArrow.innerText = currentSortDir === 'asc' ? '▲' : '▼';
        }

        try {
            sessionStorage.setItem('table_sort_state', JSON.stringify({
                col: currentSortCol,
                dir: currentSortDir
            }));
        } catch (e) {}
    }

    function abrirModalExclusao(accId, username) {
        contaPendenteExclusaoId = accId;
        contaPendenteExclusaoUser = username;
        document.getElementById('modalDeleteUsername').innerText = '@' + username;
        document.getElementById('modalDeleteAccId').innerText = accId;
        const btn = document.getElementById('btnConfirmDeleteAcc');
        btn.disabled = false;
        btn.innerText = 'Sim, Excluir Conta';
        document.getElementById('deleteModalOverlay').style.display = 'flex';
    }

    function fecharModalExclusao() {
        contaPendenteExclusaoId = null;
        contaPendenteExclusaoUser = null;
        document.getElementById('deleteModalOverlay').style.display = 'none';
    }

    function fecharModalSeClicarFora(ev) {
        if (ev.target && ev.target.id === 'deleteModalOverlay') {
            fecharModalExclusao();
        }
    }

    async function confirmarExclusaoConta() {
        if (!contaPendenteExclusaoId) return;
        const btn = document.getElementById('btnConfirmDeleteAcc');
        btn.disabled = true;
        btn.innerText = '⏳ Excluindo...';

        try {
            const res = await fetch('/api/delete_account/' + encodeURIComponent(contaPendenteExclusaoId), {
                method: 'POST'
            });
            const data = await res.json();
            if (res.ok && data.ok) {
                const rowMain = document.getElementById('acc_row_' + contaPendenteExclusaoId);
                const rowPosts = document.getElementById('posts_row_' + contaPendenteExclusaoId);
                if (rowMain) rowMain.remove();
                if (rowPosts) rowPosts.remove();
                fecharModalExclusao();
                window.location.reload();
            } else {
                alert('Erro ao excluir conta: ' + (data.error || 'Falha desconhecida'));
                btn.disabled = false;
                btn.innerText = 'Sim, Excluir Conta';
            }
        } catch (e) {
            alert('Erro de rede ao tentar excluir conta: ' + e);
            btn.disabled = false;
            btn.innerText = 'Sim, Excluir Conta';
        }
    }

    async function adicionarNovaConta(ev) {
        ev.preventDefault();
        const tokenEl = document.getElementById('newAccToken');
        const idEl = document.getElementById('newAccId');
        const btn = document.getElementById('btnAddAccount');
        const statusEl = document.getElementById('addAccountStatus');

        const accessToken = (tokenEl.value || '').trim();
        const igUserId = (idEl.value || '').trim();

        if (!accessToken && !igUserId) {
            statusEl.style.display = 'block';
            statusEl.style.color = '#f87171';
            statusEl.innerText = '⚠️ Informe pelo menos o Access Token ou o ID da conta.';
            return;
        }

        adicionandoContaEmAndamento = true;
        btn.disabled = true;
        btn.innerText = '⏳ Buscando dados na Meta e salvando...';
        statusEl.style.display = 'block';
        statusEl.style.color = '#38bdf8';
        statusEl.innerText = '🔄 Conectando à Graph API do Instagram, coletando seguidores, Reels e visualizações...';

        try {
            const res = await fetch('/api/add_account', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                    access_token: accessToken,
                    ig_user_id: igUserId
                })
            });
            const data = await res.json();
            if (res.ok && data.ok) {
                statusEl.style.color = '#4ade80';
                statusEl.innerText = '✅ Conta @' + (data.username || data.ig_user_id) + ' adicionada com sucesso! Recarregando painel...';
                tokenEl.value = '';
                idEl.value = '';
                setTimeout(() => window.location.reload(), 700);
            } else {
                statusEl.style.color = '#f87171';
                statusEl.innerText = '❌ Erro: ' + (data.error || 'Não foi possível adicionar a conta.');
                btn.disabled = false;
                btn.innerText = '➕ Conectar e Sincronizar';
                adicionandoContaEmAndamento = false;
            }
        } catch (e) {
            statusEl.style.color = '#f87171';
            statusEl.innerText = '❌ Erro de rede ao adicionar conta: ' + e;
            btn.disabled = false;
            btn.innerText = '➕ Conectar e Sincronizar';
            adicionandoContaEmAndamento = false;
        }
    }

    function togglePostsConta(accId, btnEl) {
        const row = document.getElementById('posts_row_' + accId);
        if (!row) return;
        const isHidden = (row.style.display === 'none' || row.style.display === '');
        row.style.display = isHidden ? 'table-row' : 'none';
        if (btnEl) {
            btnEl.innerText = isHidden ? '↑' : '↓';
        }
        try {
            const openState = JSON.parse(sessionStorage.getItem('open_posts_rows') || '{}');
            openState[accId] = isHidden;
            sessionStorage.setItem('open_posts_rows', JSON.stringify(openState));
        } catch (e) {}
    }

    function atualizarMetricasContas(btn) {
        btn.disabled = true;
        btn.innerText = '⏳ Atualizando métricas e salvando no Upstash...';
        window.location.href = '/atualizar_metricas';
    }

    async function copiarSnapshotVercel(btn) {
        const origText = btn.innerText;
        btn.disabled = true;
        btn.innerText = '⏳ Gerando JSON...';
        try {
            const res = await fetch('/api/export_snapshot');
            const data = await res.json();
            await navigator.clipboard.writeText(JSON.stringify(data));
            alert('✅ Snapshot JSON copiado para a área de transferência!');
        } catch (e) {
            alert('Erro ao copiar JSON: ' + e);
        } finally {
            btn.disabled = false;
            btn.innerText = origText;
        }
    }

    window.addEventListener('DOMContentLoaded', () => {
        try {
            const savedSort = JSON.parse(sessionStorage.getItem('table_sort_state') || 'null');
            if (savedSort && typeof savedSort.col === 'number' && (savedSort.dir === 'asc' || savedSort.dir === 'desc')) {
                ordenarTabelaPorColuna(savedSort.col, savedSort.dir);
            }
        } catch (e) {}

        try {
            const openState = JSON.parse(sessionStorage.getItem('open_posts_rows') || '{}');
            Object.keys(openState).forEach(accId => {
                if (openState[accId]) {
                    const row = document.getElementById('posts_row_' + accId);
                    const btn = document.getElementById('btn_toggle_' + accId);
                    if (row) row.style.display = 'table-row';
                    if (btn) btn.innerText = '↑';
                }
            });
        } catch (e) {}
    });

    let remaining = 60;
    setInterval(() => {
        const modal = document.getElementById('deleteModalOverlay');
        if (modal && modal.style.display === 'flex') return;
        if (adicionandoContaEmAndamento) return;

        // Pausa o reload automático se o usuário estiver digitando no formulário lá embaixo
        const activeEl = document.activeElement;
        if (activeEl && (activeEl.id === 'newAccToken' || activeEl.id === 'newAccId')) return;

        remaining--;
        const el = document.getElementById('reloadCountdown');
        if (el) el.innerText = remaining + 's';
        if (remaining <= 0) {
            window.location.reload();
        }
    }, 1000);
</script>
</body>
</html>
"""


# ==============================================================================
# ROTAS FLASK E API DE FILA INTELIGENTE + ADIÇÃO E EXCLUSÃO DE CONTAS
# ==============================================================================

@app.route("/", methods=["GET"])
@requires_auth
def index():
    global MEMORY_GLOBAL_PEAK_MIN, MEMORY_GLOBAL_PEAK_HOUR

    state = get_saved_state(force_redis=not REDIS_BOOTSTRAPPED)
    last_ts = state.get("last_global_sync_ts", 0)
    accounts = state.get("accounts", {})

    if time.time() - last_ts >= 300 or not accounts:
        state = refresh_all_accounts_to_json()

    accounts = sort_accounts_by_views_desc(state.get("accounts", {}))
    last_sync_str = state.get("last_global_sync_str", "—")

    ready_to_post_list = []
    maturing_cooldown_list = []
    paused_or_down_list = []

    for acc in accounts.values():
        if isinstance(acc, dict):
            v_min, v_hour = _compute_account_velocity_rates(acc)
            acc["views_per_min"] = v_min
            acc["views_per_hour"] = v_hour

            peak_min = round(max(_safe_float(acc.get("peak_views_per_min")), v_min), 2)
            peak_hour = round(max(_safe_float(acc.get("peak_views_per_hour")), v_hour), 2)
            acc["peak_views_per_min"] = peak_min
            acc["peak_views_per_hour"] = peak_hour
            acc["updated_at_ts"] = _parse_br_datetime_to_ts(acc.get("metrics_updated_at")) or 0

            intel = _analyze_account_intelligence(acc)
            acc["intel"] = intel

            acode = intel.get("action_code", "")
            if acode in ("SURF_TRACTION", "FEED_WARM", "REACTIVATE_CHAMPION"):
                ready_to_post_list.append(acc)
            elif acode in ("COOLDOWN_HOT", "COOLDOWN_MATURING", "DAILY_CYCLE_REST"):
                maturing_cooldown_list.append(acc)
            elif acode in ("PAUSE_ZOMBIE", "THROTTLE_REST", "RECONNECT", "QUOTA_FULL"):
                paused_or_down_list.append(acc)

    ready_to_post_list.sort(key=lambda x: x.get("intel", {}).get("priority_score", 0), reverse=True)

    total_followers = sum(_safe_int(acc.get("followers_count")) for acc in accounts.values())
    total_views = sum(_safe_int(acc.get("total_views")) for acc in accounts.values())
    total_views_per_min = round(sum(_safe_float(acc.get("views_per_min")) for acc in accounts.values()), 2)
    total_views_per_hour = round(sum(_safe_float(acc.get("views_per_hour")) for acc in accounts.values()), 2)

    prev_g_min = _safe_float(state.get("global_peak_views_per_min"))
    prev_g_hour = _safe_float(state.get("global_peak_views_per_hour"))
    global_peak_min_val, global_peak_hour_val = _compute_global_peaks_from_accounts(
        accounts,
        prev_peak_min=prev_g_min,
        prev_peak_hour=prev_g_hour
    )

    if global_peak_min_val > prev_g_min or global_peak_hour_val > prev_g_hour:
        MEMORY_GLOBAL_PEAK_MIN = global_peak_min_val
        MEMORY_GLOBAL_PEAK_HOUR = global_peak_hour_val
        state["global_peak_views_per_min"] = global_peak_min_val
        state["global_peak_views_per_hour"] = global_peak_hour_val
        save_current_state(state)

    return render_template_string(
        HTML_TEMPLATE,
        accounts=accounts,
        last_sync=last_sync_str,
        total_followers=total_followers,
        total_views=total_views,
        total_views_per_min=total_views_per_min,
        total_views_per_hour=total_views_per_hour,
        global_peak_min_val=global_peak_min_val,
        global_peak_hour_val=global_peak_hour_val,
        ready_to_post_list=ready_to_post_list,
        maturing_cooldown_list=maturing_cooldown_list,
        paused_or_down_list=paused_or_down_list,
        upstash_active=is_upstash_configured(),
        redis_bootstrapped=REDIS_BOOTSTRAPPED
    )


@app.route("/api/add_account", methods=["POST"])
@requires_auth
def api_add_account():
    payload = request.get_json(silent=True) or {}
    ig_user_id = (payload.get("ig_user_id") or request.form.get("ig_user_id") or "").strip()
    access_token = (payload.get("access_token") or request.form.get("access_token") or "").strip()

    ok, msg, acc_data = add_or_update_account_minimal(ig_user_id, access_token)
    if not ok:
        return jsonify({"ok": False, "error": msg}), 400

    return jsonify({
        "ok": True,
        "message": msg,
        "ig_user_id": acc_data.get("ig_user_id"),
        "username": acc_data.get("username"),
        "followers_count": acc_data.get("followers_count", 0),
        "total_views": acc_data.get("total_views", 0)
    })


@app.route("/api/delete_account/<acc_id>", methods=["POST", "DELETE"])
@requires_auth
def api_delete_account(acc_id):
    ok = delete_account_permanently(acc_id)
    if not ok:
        return jsonify({"ok": False, "error": "ID de conta inválido."}), 400
    return jsonify({"ok": True, "deleted_id": str(acc_id).strip()})


@app.route("/api/smart_queue", methods=["GET"])
@requires_auth
def api_smart_queue():
    state = get_saved_state(force_redis=not REDIS_BOOTSTRAPPED)
    accounts = sort_accounts_by_views_desc(state.get("accounts", {}))
    queue = []

    for uid, acc in accounts.items():
        if not isinstance(acc, dict):
            continue
        v_min, v_hour = _compute_account_velocity_rates(acc)
        acc["views_per_min"] = v_min
        acc["views_per_hour"] = v_hour
        intel = _analyze_account_intelligence(acc)
        queue.append({
            "ig_user_id": uid,
            "username": acc.get("username"),
            "can_post_now": intel.get("can_post_now", False),
            "recommended_batch_size": intel.get("recommended_batch_size", 0),
            "priority_score": intel.get("priority_score", 0),
            "action_code": intel.get("action_code"),
            "action_title": intel.get("action_title"),
            "action_detail": intel.get("action_detail"),
            "views_per_min": v_min,
            "views_per_hour": v_hour,
            "activity_index_pct": intel.get("activity_index_pct"),
            "mins_since_last_post": intel.get("mins_since_last_post"),
            "batches_24h_count": intel.get("batches_24h_count", 0),
            "posts_last_24h_count": intel.get("posts_last_24h_count", 0),
            "last_batch_avg_views": intel.get("last_batch_avg_views", 0),
            "best_window_brt": intel.get("best_window_str")
        })

    queue.sort(key=lambda x: x["priority_score"], reverse=True)
    return jsonify({
        "generated_at_brt": datetime.now(BRT).strftime("%d/%m/%Y %H:%M:%S"),
        "accounts_ready_count": sum(1 for x in queue if x["can_post_now"]),
        "smart_queue": queue
    })


@app.route("/atualizar_metricas", methods=["GET", "POST"])
@requires_auth
def atualizar_metricas():
    refresh_all_accounts_to_json()
    return redirect(url_for("index"))


@app.route("/api/export_snapshot", methods=["GET"])
@requires_auth
def export_snapshot():
    env_accs = get_env_accounts()
    state = get_saved_state(force_redis=not REDIS_BOOTSTRAPPED)
    saved_accs = state.get("accounts", {})

    export_dict = {}
    all_uids = (set(env_accs.keys()) | set(saved_accs.keys())) - MEMORY_DELETED_IDS
    for uid in all_uids:
        uid_s = str(uid).strip()
        env_item = env_accs.get(uid_s, {})
        saved_item = saved_accs.get(uid_s, {})
        merged = merge_best_account_data(env_item, saved_item)
        tok = MEMORY_CUSTOM_TOKENS.get(uid_s) or env_item.get("access_token")
        if tok:
            merged["access_token"] = tok
        export_dict[uid_s] = merged

    return jsonify(export_dict)


@app.route("/api/cron/sync", methods=["GET", "POST"])
def cron_sync():
    cron_secret = os.environ.get("CRON_SECRET", "").strip()
    if not cron_secret:
        return jsonify({"ok": False, "error": "CRON_SECRET não definido."}), 403

    provided = request.args.get("key", "").strip()
    auth_header = request.headers.get("Authorization", "")
    if auth_header.startswith("Bearer "):
        provided = auth_header.replace("Bearer ", "", 1).strip()

    if not hmac.compare_digest(provided, cron_secret):
        return jsonify({"ok": False, "error": "Chave inválida."}), 401

    state = refresh_all_accounts_to_json()
    return jsonify({
        "ok": True,
        "upstash_persisted": is_upstash_configured() and REDIS_BOOTSTRAPPED,
        "updated_at": state.get("last_global_sync_str"),
        "accounts_count": len(state.get("accounts", {}))
    })


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000, debug=False, use_reloader=False)