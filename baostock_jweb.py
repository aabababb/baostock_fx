import json
import os
import re
import smtplib
import time
import http.server
import threading
from urllib.parse import urlparse, parse_qs
from email.mime.text import MIMEText
from email.header import Header
from datetime import datetime, timedelta, date
from zoneinfo import ZoneInfo  # Python 3.9+，若低版本需安装 backports.zoneinfo
import pandas as pd
from pandas.tseries.offsets import BDay

import requests
from bs4 import BeautifulSoup

import signal
from contextlib import contextmanager

import akshare as ak
import baostock as bs
from openai import OpenAI

CONFIG_FILE = "aks_config_jweb.json"

# ---------- 全局日志缓冲区 ----------
log_buffer = []          # 存储日志字符串
log_lock = threading.Lock()
analysis_running = False  # 标志：是否正在执行AI分析

# ---------- 日志函数（同时输出到控制台和缓冲区，使用北京时间） ----------
def log(msg: str):
    timestamp = datetime.now(ZoneInfo("Asia/Shanghai")).strftime("%Y-%m-%d %H:%M:%S")
    line = f"[{timestamp}] {msg}"
    print(line)
    with log_lock:
        log_buffer.append(line)
        if len(log_buffer) > 500:  # 限制最多保留500条
            log_buffer.pop(0)

# ---------- 配置加载 ----------
def load_config(config_file: str) -> dict:
    if not os.path.exists(config_file):
        raise FileNotFoundError(f"配置文件 {config_file} 不存在，请先创建并填写配置。")
    with open(config_file, "r", encoding="utf-8") as f:
        return json.load(f)

config = load_config(CONFIG_FILE)

ADJUST = config["stock"].get("adjust", "qfq")
NEWS_CONFIG = config.get("news", {"enable": True, "max_news": 5})
EMAIL_CONFIG = config.get("email", {})
SHUTDOWN_AFTER_RUN = config.get("shutdown", False)
web_passwd = config.get("web", {}).get("passwd")  # 若配置，则启动HTTP状态服务
AI_CONFIG = config.get("ai", {})
schedule_time_str = config.get("schedule_time", "09:00")  # 定时执行时间，默认09:00
NEWS_REFRESH_CONFIG = config.get("news_refresh", {})
NEWS_REFRESH_ENABLED = NEWS_REFRESH_CONFIG.get("enabled", True)
NEWS_REFRESH_INTERVAL = NEWS_REFRESH_CONFIG.get("interval_minutes", 30)


class TimeoutException(Exception):
    pass

@contextmanager
def time_limit(seconds):
    """在 Unix/Linux 下可用，Windows 需使用其他方式"""
    def signal_handler(signum, frame):
        raise TimeoutException("Timed out")
    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)

def get_lowest_price_stocks(n: int = 10, max_retries: int = 3, retry_delay: int = 5, timeout: int = 30) -> list:
    """
    获取股价最低的 n 只非停牌、非ST股票，自动尝试多个数据源，每个源支持重试和超时
    :param n: 返回股票数量
    :param max_retries: 每个数据源最大重试次数
    :param retry_delay: 重试间隔秒数
    :param timeout: 单次请求超时秒数
    """
    data_sources = [
        ("新浪", lambda: ak.stock_zh_a_spot()),
        ("东方财富", lambda: ak.stock_zh_a_spot_em()),
    ]
    
    df_spot = None
    source_name = ""
    
    for name, func in data_sources:
        for attempt in range(max_retries):
            try:
                log(f"尝试 {name} 实时行情，第 {attempt+1}/{max_retries} 次...")
                # 使用信号设置超时（仅限 Unix/Linux，Windows 需使用其他方法）
                with time_limit(timeout):
                    df = func()
                if df is not None and not df.empty:
                    df_spot = df
                    source_name = name
                    log(f"{name} 获取成功，共 {len(df_spot)} 条数据")
                    break
                else:
                    log(f"{name} 返回空数据")
            except TimeoutException:
                log(f"{name} 请求超时（{timeout}秒）")
            except Exception as e:
                log(f"{name} 获取失败: {e}")
            
            if df_spot is not None:
                break
            if attempt < max_retries - 1:
                log(f"等待 {retry_delay} 秒后重试...")
                time.sleep(retry_delay)
        
        if df_spot is not None:
            break
    
    if df_spot is None:
        log("所有实时行情数据源均不可用")
        return []

    log(f"成功使用 {source_name} 获取 {len(df_spot)} 条行情数据")

    # 识别代码列、价格列、成交量列、状态列、名称列
    code_col = None
    price_col = None
    volume_col = None
    status_col = None
    name_col = None

    for col in df_spot.columns:
        if "代码" in col or col == "code":
            code_col = col
        if "最新价" in col or "现价" in col or col == "最新" or col == "price":
            price_col = col
        if "成交量" in col or col == "volume":
            volume_col = col
        if "状态" in col or col == "status":
            status_col = col
        if "名称" in col or "简称" in col or col == "name":
            name_col = col

    if code_col is None or price_col is None:
        log(f"无法识别代码列或价格列，实际列名: {df_spot.columns.tolist()}")
        return []

    # 1. 过滤价格 <= 0 的股票（停牌股可能价格为零）
    df_spot[price_col] = pd.to_numeric(df_spot[price_col], errors='coerce')
    df_spot = df_spot.dropna(subset=[price_col])
    df_spot = df_spot[df_spot[price_col] > 0]
    log(f"过滤价格 <=0 后剩余 {len(df_spot)} 只股票")

    # 2. 过滤成交量 <= 0 的股票（停牌股成交量通常为零）
    if volume_col:
        df_spot[volume_col] = pd.to_numeric(df_spot[volume_col], errors='coerce')
        df_spot = df_spot.dropna(subset=[volume_col])
        df_spot = df_spot[df_spot[volume_col] > 0]
        log(f"过滤成交量 <=0 后剩余 {len(df_spot)} 只股票")

    # 3. 过滤状态包含“停牌”的股票
    if status_col:
        df_spot = df_spot[~df_spot[status_col].astype(str).str.contains("停牌", na=False)]
        log(f"过滤停牌状态后剩余 {len(df_spot)} 只股票")

    # 4. 过滤 ST 股票（名称中包含 "ST"，不区分大小写）
    if name_col:
        df_spot = df_spot[~df_spot[name_col].astype(str).str.contains("ST", case=False, na=False)]
        log(f"过滤 ST 股票后剩余 {len(df_spot)} 只股票")
    else:
        log("未找到名称列，无法过滤 ST 股票")

    # 按价格排序
    df_sorted = df_spot.sort_values(by=price_col)
    lowest = df_sorted.head(n)
    result = list(zip(lowest[code_col].astype(str).str.replace(r'\D', '', regex=True), lowest[price_col]))

    log(f"股价最低的 {n} 只非停牌、非ST股票：")
    for code, price in result:
        log(f"  {code}: {price:.2f}")
    return result

# ---------- 新闻搜索（东方财富 + 百度备选） ----------
def get_stock_news(stock_code: str, max_news: int = 5) -> str:
    """获取股票新闻，自动尝试多个数据源"""
    log(f"开始获取股票 {stock_code} 的新闻...")

    # 1. 尝试东方财富新闻
    try:
        df = ak.stock_news_em(symbol=stock_code)
        if df is not None and not df.empty:
            titles = df['新闻标题'].head(max_news).tolist()
            if titles:
                news_str = "；".join(titles)
                log(f"股票 {stock_code} 从东方财富获取到 {len(titles)} 条新闻")
                return news_str
    except Exception as e:
        log(f"东方财富新闻获取失败: {e}")

    # 2. 尝试百度新闻（可能返回安全验证页）
    try:
        url = f"https://www.baidu.com/s?tn=news&word={stock_code}"
        headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
            "Referer": "https://www.baidu.com/",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
        }
        resp = requests.get(url, headers=headers, timeout=10)
        resp.encoding = 'utf-8'
        soup = BeautifulSoup(resp.text, 'html.parser')
        news_items = []
        for item in soup.select('h3.news-title a, h3.c-title a, div.result-op a'):
            title = item.get_text(strip=True)
            if title:
                news_items.append(title)
            if len(news_items) >= max_news:
                break
        if not news_items:
            for h3 in soup.find_all('h3'):
                a = h3.find('a')
                if a and a.get_text(strip=True):
                    news_items.append(a.get_text(strip=True))
                    if len(news_items) >= max_news:
                        break
        if news_items:
            news_str = "；".join(news_items[:max_news])
            log(f"股票 {stock_code} 从百度获取到 {len(news_items)} 条新闻")
            return news_str
        else:
            log(f"股票 {stock_code} 百度新闻未获取到有效内容")
    except Exception as e:
        log(f"百度新闻获取失败: {e}")

    # 3. 都失败返回空
    log(f"股票 {stock_code} 未获取到新闻")
    return "无相关新闻"

# ---------- Baostock 历史数据 ----------
def baostock_login():
    lg = bs.login()
    if lg.error_code != '0':
        log(f"Baostock 登录失败: {lg.error_msg}")
        return False
    log("Baostock 登录成功")
    return True

def baostock_logout():
    bs.logout()
    log("Baostock 登出")

def get_stock_data_baostock(symbol: str, start: str, end: str, adjust: str = "qfq") -> pd.DataFrame:
    """获取指定股票的历史日线数据"""
    if len(start) == 8 and start.isdigit():
        start = f"{start[:4]}-{start[4:6]}-{start[6:]}"
    if len(end) == 8 and end.isdigit():
        end = f"{end[:4]}-{end[4:6]}-{end[6:]}"

    if symbol.startswith('6'):
        bs_symbol = f"sh.{symbol}"
    else:
        bs_symbol = f"sz.{symbol}"

    adjust_flag = "2" if adjust == "qfq" else ("1" if adjust == "hfq" else "3")

    rs = bs.query_history_k_data_plus(
        bs_symbol,
        "date,open,high,low,close,volume,amount,pctChg",
        start_date=start,
        end_date=end,
        frequency="d",
        adjustflag=adjust_flag
    )
    if rs.error_code != '0':
        return pd.DataFrame()

    data_list = []
    while (rs.error_code == '0') & rs.next():
        data_list.append(rs.get_row_data())

    if not data_list:
        return pd.DataFrame()

    df = pd.DataFrame(data_list, columns=rs.fields)
    for col in ["open", "high", "low", "close", "volume", "amount", "pctChg"]:
        df[col] = pd.to_numeric(df[col], errors='coerce')
    df["date"] = pd.to_datetime(df["date"])
    df.rename(columns={"pctChg": "pct_change"}, inplace=True)
    return df

# ---------- AI 调用 ----------
def analyze_with_openai(prompt: str, api_key: str, base_url: str, model: str,
                        temperature: float, max_tokens: int) -> str:
    """调用 OpenAI 兼容接口"""
    client = OpenAI(api_key=api_key, base_url=base_url)
    response = client.chat.completions.create(
        model=model,
        messages=[
            {"role": "system", "content": "你是一位严谨的金融分析师，回答需客观、专业。"},
            {"role": "user", "content": prompt},
        ],
        temperature=temperature,
        max_tokens=max_tokens,
    )
    return response.choices[0].message.content

def analyze_with_cloudflare(prompt: str, cfapi_url: str, account_id: str, api_token: str, model: str,
                            temperature: float = 0.3, max_tokens: int = 800, max_retries: int = 3) -> str:
    """调用 Cloudflare Workers AI，兼容不同返回格式，支持超时重试"""
    url = f"https://{cfapi_url}/client/v4/accounts/{account_id}/ai/run/{model}"
    headers = {
        "Authorization": f"Bearer {api_token}",
        "Content-Type": "application/json"
    }
    payload = {
        "messages": [
            {"role": "system", "content": "你是一位严谨的金融分析师，回答需客观、专业。"},
            {"role": "user", "content": prompt}
        ],
        "temperature": temperature,
        "max_tokens": max_tokens
    }

    for attempt in range(max_retries + 1):
        try:
            resp = requests.post(url, json=payload, headers=headers, timeout=120)
            resp.raise_for_status()
            data = resp.json()

            # 尝试多种可能的响应格式
            if "result" in data:
                result = data["result"]
                if isinstance(result, dict) and "response" in result:
                    return result["response"]
                if isinstance(result, dict) and "choices" in result:
                    choices = result["choices"]
                    if choices and "message" in choices[0] and "content" in choices[0]["message"]:
                        return choices[0]["message"]["content"]
                if isinstance(result, str):
                    return result

            if "choices" in data:
                choices = data["choices"]
                if choices and "message" in choices[0] and "content" in choices[0]["message"]:
                    return choices[0]["message"]["content"]

            log(f"Cloudflare 返回格式无法解析: {data}")
            return "AI 返回格式错误"

        except requests.exceptions.Timeout:
            log(f"Cloudflare 超时，重试 {attempt+1}/{max_retries}")
            time.sleep(10)
        except Exception as e:
            log(f"Cloudflare 调用失败: {e}")
            break

    return "AI 调用异常（多次超时）"

def analyze_with_ai(prompt: str, ai_config: dict) -> str:
    """统一 AI 分析入口，根据配置文件 type 选择调用方式"""
    ai_type = ai_config.get("type", "openai").lower()
    temperature = ai_config.get("temperature", 0.3)
    max_tokens = ai_config.get("max_tokens", 800)

    if ai_type == "openai":
        api_key = ai_config["api_key"]
        base_url = ai_config["base_url"]
        model = ai_config["model"]
        return analyze_with_openai(prompt, api_key, base_url, model, temperature, max_tokens)
    elif ai_type == "cloudflare":
        account_id = ai_config["account_id"]
        api_token = ai_config["api_token"]
        model = ai_config["model"]
        cfapi_url = ai_config.get("cfapi_url", "api.cloudflare.com")
        return analyze_with_cloudflare(prompt, cfapi_url, account_id, api_token, model, temperature, max_tokens)
    else:
        log(f"未知 AI 类型: {ai_type}")
        return "AI 配置错误"

def prepare_prompt(stock_code: str, df: pd.DataFrame, news_text: str = "") -> str:
    """构建单个股票的预测提示词，结合新闻信息"""
    recent_df = df.tail(10).copy()
    if recent_df.empty:
        return ""
    start_price = recent_df.iloc[0]["close"]
    end_price = recent_df.iloc[-1]["close"]
    period_return = (end_price / start_price - 1) * 100
    max_price = recent_df["high"].max()
    min_price = recent_df["low"].min()
    avg_volume = recent_df["volume"].mean()

    last_date = recent_df.iloc[-1]["date"]
    next_approx = last_date + BDay(1)
    next_approx_str = next_approx.strftime("%Y-%m-%d")

    data_str = recent_df[["date", "open", "close", "high", "low", "volume", "pct_change"]].to_string(index=False)

    news_section = ""
    if news_text and news_text != "无相关新闻" and news_text != "新闻获取失败":
        news_section = f"\n【最新新闻事件】\n{news_text}\n"

    prompt = f"""
你是一位专业的股票分析师。请根据以下 {stock_code} 的历史行情数据和最新新闻事件，预测该股票在下一个交易日（约 {next_approx_str}，若遇节假日顺延）的涨跌方向。

【股票代码】{stock_code}
【数据截止日期】{last_date.strftime('%Y-%m-%d')}
【数据区间】{recent_df.iloc[0]['date'].strftime('%Y-%m-%d')} 至 {last_date.strftime('%Y-%m-%d')}
【区间涨跌幅】{period_return:.2f}%
【最高价】{max_price}
【最低价】{min_price}
【平均成交量】{avg_volume:.0f}
{news_section}
【最近10个交易日数据】
{data_str}

请综合技术面与新闻事件，直接给出预测结果，格式如下：
预测：涨 / 跌
理由：（简要说明，不超过150字）

注意：预测基于历史数据与公开新闻，不构成投资建议。
"""
    return prompt

# ---------- 邮件发送 ----------

def send_email(subject: str, body: str, email_config: dict):
    if not email_config.get("sendmail", False):
        log("未启用邮件发送")
        return

    mail_type = email_config.get("mail_type", "smtp").lower()

    if mail_type == "smtp":
        # 原有 SMTP 发送逻辑
        smtp_server = email_config["smtp_server"]
        smtp_port = email_config["smtp_port"]
        sender_email = email_config["sender_email"]
        sender_password = email_config["sender_password"]
        receivers = email_config["receiver_emails"]

        message = MIMEText(body, "plain", "utf-8")
        message["From"] = Header(sender_email)
        message["To"] = Header(",".join(receivers))
        message["Subject"] = Header(subject, "utf-8")

        try:
            if smtp_port == 465:
                server = smtplib.SMTP_SSL(smtp_server, smtp_port)
            else:
                server = smtplib.SMTP(smtp_server, smtp_port)
                server.starttls()
            server.login(sender_email, sender_password)
            server.sendmail(sender_email, receivers, message.as_string())
            server.quit()
            log(f"邮件已通过 SMTP 发送至: {', '.join(receivers)}")
        except Exception as e:
            log(f"SMTP 邮件发送失败: {e}")

    elif mail_type == "curl":
        # 使用 HTTP API 发送邮件
        api_url = email_config.get("api_url")
        api_key = email_config.get("api_key")
        receivers = email_config.get("receiver_emails", [])

        if not api_url or not api_key:
            log("curl 邮件配置缺失：api_url 或 api_key 未设置")
            return

        headers = {
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json"
        }
        payload = {
            "receivers": receivers,
            "Subject": subject,
            "content": body
        }
        try:
            resp = requests.post(api_url, json=payload, headers=headers, timeout=30)
            resp.raise_for_status()
            log(f"邮件已通过 HTTP API 发送，状态码: {resp.status_code}")
        except Exception as e:
            log(f"HTTP API 邮件发送失败: {e}")

    else:
        log(f"未知的邮件发送方式: {mail_type}")


# ---------- HTTP 状态服务 ----------
class StatusHandler(http.server.BaseHTTPRequestHandler):
    web_passwd = None

    def do_GET(self):
        parsed_path = urlparse(self.path)
        if parsed_path.path == '/status':
            qs = parse_qs(parsed_path.query)
            pass_input = qs.get('pass', [None])[0]
            if self.web_passwd and pass_input != self.web_passwd:
                self.send_response(200)
                self.send_header('Content-type', 'text/plain; charset=utf-8')
                self.end_headers()
                self.wfile.write("密码错误，拒绝访问\n".encode('utf-8'))
                return
            self.send_response(200)
            self.send_header('Content-type', 'text/plain; charset=utf-8')
            self.end_headers()
            with log_lock:
                logs = list(log_buffer[-100:])  # 只输出最近100条日志
            if not logs:
                self.wfile.write("暂无日志\n".encode('utf-8'))
            else:
                self.wfile.write('\n'.join(logs).encode('utf-8'))
                self.wfile.write('\n'.encode('utf-8'))
        else:
            self.send_response(404)
            self.end_headers()
            self.wfile.write(b'Not Found')

    def log_message(self, format, *args):
        pass

def start_http_server(web_passwd):
    StatusHandler.web_passwd = web_passwd
    port = int(os.environ.get('PORT', 10000))
    server = http.server.HTTPServer(('0.0.0.0', port), StatusHandler)
    log(f"HTTP 状态服务已启动，监听 0.0.0.0:{port}，访问 /status?pass=你的密码")
    server.serve_forever()

# ---------- 新闻刷新任务（每30分钟执行，AI分析期间跳过） ----------
def refresh_news():
    """每半小时执行一次：获取当前低价股列表，并更新每只股票的新闻（仅记录日志，不调用AI）"""
    global analysis_running
    if analysis_running:
        log("正在执行AI分析，跳过本次新闻刷新")
        return

    log("========== 开始新闻刷新任务 ==========")
    try:
        lowest_stocks = get_lowest_price_stocks(10)
        if not lowest_stocks:
            log("新闻刷新：无法获取低价股列表，跳过本次新闻更新")
            return

        log(f"新闻刷新：获取到 {len(lowest_stocks)} 只低价股，开始获取新闻...")
        for code, price in lowest_stocks:
            news_text = get_stock_news(code, NEWS_CONFIG.get("max_news", 5))
            # 这里仅获取新闻，不进行AI分析，日志已在函数内部输出
        log("新闻刷新任务完成")
    except Exception as e:
        log(f"新闻刷新任务发生异常: {e}")

# ---------- 核心分析任务 ----------
def run_analysis():
    """执行一次完整的股票分析流程"""
    global analysis_running
    analysis_running = True
    try:
        log("========== 开始执行股票分析任务 ==========")

        # 初始化重试参数
        max_retries = 3
        retry_delays = [120, 600, 1800]  # 2分钟、10分钟、30分钟（秒）

        lowest_stocks = None
        baostock_ok = False

        for attempt in range(max_retries + 1):
            log(f"初始化尝试 {attempt + 1}/{max_retries + 1}")

            lowest_stocks = get_lowest_price_stocks(10)
            if not lowest_stocks:
                log("无法获取低价股列表")
            else:
                if baostock_login():
                    baostock_ok = True
                    break
                else:
                    log("Baostock 登录失败")

            if baostock_ok:
                break

            if attempt < max_retries:
                wait_seconds = retry_delays[attempt]
                log(f"等待 {wait_seconds // 60} 分钟后重试...")
                time.sleep(wait_seconds)

        if not (lowest_stocks and baostock_ok):
            log("多次重试后仍无法完成初始化，跳过本次任务。")
            if SHUTDOWN_AFTER_RUN:
                log("配置要求自动关机，正在执行关机命令...")
                os.system("shutdown -h now")
            return

        log(f"成功获取低价股列表，共 {len(lowest_stocks)} 只股票")

        today = datetime.now().date()
        start_date = today - timedelta(days=365)
        end_date = today
        start_str = start_date.strftime("%Y-%m-%d")
        end_str = end_date.strftime("%Y-%m-%d")

        results_up = []

        for code, price in lowest_stocks:
            log(f"正在处理股票 {code}，价格 {price:.2f}")

            news_text = get_stock_news(code, NEWS_CONFIG.get("max_news", 5))
            df = get_stock_data_baostock(code, start_str, end_str, ADJUST)
            if df.empty:
                log(f"股票 {code} 无历史数据，跳过")
                continue

            prompt = prepare_prompt(code, df, news_text)
            if not prompt:
                log(f"股票 {code} 提示词构建失败，跳过")
                continue

            log(f"调用 AI 分析 {code} ...")
            try:
                analysis = analyze_with_ai(prompt, AI_CONFIG)
            except Exception as e:
                log(f"AI 分析股票 {code} 失败: {e}")
                continue

            print(f"\n--- 股票 {code} AI 预测结果 ---")
            print(analysis)

            if re.search(r"预测\s*[:：]\s*涨", analysis):
                log(f"AI 分析股票涨结果 {analysis} ")
                results_up.append({
                    "code": code,
                    "price": price,
                    "news": news_text,
                    "analysis": analysis,
                    "last_date": df.iloc[-1]["date"].strftime("%Y-%m-%d")
                })

        baostock_logout()

        if results_up:
            log(f"共有 {len(results_up)} 只股票预测为涨，准备发送邮件...")
            subject = f"A股低价股 AI 预测上涨通知 ({datetime.now(ZoneInfo('Asia/Shanghai')).strftime('%Y-%m-%d')})"
            body = "以下股票 AI 预测下一交易日为上涨：\n\n"
            for item in results_up:
                body += f"股票代码: {item['code']}\n"
                body += f"最新收盘价: {item['price']:.2f}\n"
                body += f"数据截止日期: {item['last_date']}\n"
                body += f"相关新闻: {item['news']}\n"
                body += "AI 分析:\n"
                body += item['analysis'] + "\n"
                body += "-" * 40 + "\n"
            send_email(subject, body, EMAIL_CONFIG)
        else:
            log("没有股票被预测为涨，不发送邮件。")

        log("========== 本次股票分析任务结束 ==========")

        if SHUTDOWN_AFTER_RUN:
            log("配置要求自动关机，正在执行关机命令...")
            os.system("shutdown -h now")
    finally:
        analysis_running = False


def wait_until_schedule(schedule_hour: int, schedule_minute: int):
    """精确等待到下一个设定时间（北京时间）"""
    tz = ZoneInfo("Asia/Shanghai")
    now = datetime.now(tz)
    next_run = now.replace(hour=schedule_hour, minute=schedule_minute, second=0, microsecond=0)
    if now >= next_run:
        next_run += timedelta(days=1)
    wait_seconds = (next_run - now).total_seconds()
    log(f"下次分析时间：{next_run.strftime('%Y-%m-%d %H:%M:%S')}，等待 {wait_seconds/60:.2f} 分钟")
    time.sleep(wait_seconds)

def main():
    # 启动 HTTP 服务（如果配置了密码）
    if web_passwd:
        http_thread = threading.Thread(target=start_http_server, args=(web_passwd,), daemon=True)
        http_thread.start()
    else:
        log("未配置 web.passwd，HTTP 状态服务不启动")

    log(f"程序启动，定时调度模式：每天 {schedule_time_str} 执行AI分析，其他时间每 {NEWS_REFRESH_INTERVAL} 分钟刷新新闻（启用：{NEWS_REFRESH_ENABLED}）")

    try:
        schedule_hour, schedule_minute = map(int, schedule_time_str.split(":"))
    except Exception:
        log(f"配置的调度时间格式错误: {schedule_time_str}，使用默认09:00")
        schedule_hour, schedule_minute = 9, 0

    tz = ZoneInfo("Asia/Shanghai")
    now = datetime.now(tz)

    # 启动时判断
    if (now.hour > schedule_hour or (now.hour == schedule_hour and now.minute >= schedule_minute)):
        log(f"启动时已过设定时间 {schedule_time_str}，立即执行AI分析")
        run_analysis()
    else:
        log(f"未到设定时间，等待到 {schedule_time_str} 执行AI分析")
        wait_until_schedule(schedule_hour, schedule_minute)
        run_analysis()

    # 后续循环
    while True:
        if NEWS_REFRESH_ENABLED:
            # 新闻刷新循环，直到下一次分析时间
            while True:
                time.sleep(NEWS_REFRESH_INTERVAL * 60)
                now = datetime.now(tz)
                log(f"新闻刷新唤醒，当前北京时间：{now.strftime('%Y-%m-%d %H:%M:%S')}")
                next_run = now.replace(hour=schedule_hour, minute=schedule_minute, second=0, microsecond=0)
                if now >= next_run:
                    log("到达下一次分析时间，退出新闻刷新循环")
                    break
                else:
                    refresh_news()
                    next_refresh = now + timedelta(minutes=NEWS_REFRESH_INTERVAL)
                    log(f"下一次新闻刷新预计时间：{next_refresh.strftime('%Y-%m-%d %H:%M:%S')}")
            # 执行分析
            run_analysis()
        else:
            # 直接等待到第二天设定时间
            now = datetime.now(tz)
            next_run = now.replace(hour=schedule_hour, minute=schedule_minute, second=0, microsecond=0)
            if now >= next_run:
                next_run += timedelta(days=1)
            wait_seconds = (next_run - now).total_seconds()
            log(f"新闻刷新已禁用，下次分析时间：{next_run.strftime('%Y-%m-%d %H:%M:%S')}，等待 {wait_seconds/3600:.2f} 小时")
            time.sleep(wait_seconds)
            run_analysis()


if __name__ == "__main__":
    main()

