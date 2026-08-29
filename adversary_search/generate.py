#!/usr/bin/env python3
"""LLM 模板生成器（Qwen / DashScope，OpenAI 兼容接口）。

生成对抗实例模板 JSON → template_schema 校验 → 写入池目录，交给
pool_screen.py 粗筛。API key 读环境变量 DASHSCOPE_API_KEY。

用法：
  python generate.py --dry-run                 # 只看 prompt，不调 API
  python generate.py --n 10                    # 生成 10 个模板到 llm_pool/
  python generate.py --n 10 --model qwen-max   # 换模型（默认 qwen3.8-max，Token Plan 网关）
  python generate.py --n 10 --temperature 1.1  # 加多样性
"""

import argparse
import datetime
import json
import os
import re
import sys
import time

import requests

if hasattr(sys.stdout, 'buffer'):
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import template_schema

API_URL = os.environ.get("QWEN_BASE_URL", "https://token-plan.cn-beijing.maas.aliyuncs.com/compatible-mode/v1").rstrip("/") + "/chat/completions"
DEFAULT_MODEL = "qwen3.8-max"

SYSTEM_PROMPT = """你是调度理论研究员，任务是为"在线 makespan 调度（P|online,list|Cmax）竞争比下界"设计对抗实例模板。
只输出 JSON 数组（不要 markdown 代码块、不要解释文字）。

【语义】模板展开为固定作业序列 σ，值 = min_调度器响应 max_前缀 makespan(前缀)/OPT(前缀)，
即"任意确定性在线算法竞争比 >= 值"。m=4 台机器。目标：值越高越好
（>1.732 即达到 √3 级别；>=1.707 超过 FKT 就算合格）。

【JSON 格式】每个模板：
{"schema_version":1, "name":"...", "description":"必须写明：以哪个已知构造为种子、变异点是什么",
 "m":4,
 "params":[{"name":"a","value":0.2}],
 "defs":[{"name":"S0","expr":"(c-1)/(2-c)"}],
 "solve":[{"name":"c","equation":"6*c**3-28*c**2+38*c-13","guess":1.7}],   // 可选：代数约束，牛顿法解方程
 "recurrence":{"init":{"S":"1","A":"1/(2*V)"}, "step":{"S":"M*A","A":"(A-2*B)/4"},
               "until":"A/S >= V", "max_iter":60},                          // 可选：层递推
 "layers":[{"emit":[{"repeat":4,"size":"a"}]},
           {"loop":{"var":"i","from":0,"to":"n"},"emit":[{"repeat":4,"size":"B"}]}],
 "final":[{"repeat":1,"size":"1"}],
 "order":"fwd" 或 "rev"}
表达式：数字、变量、+ - * /、**（幂；严禁用 ^，那是位异或）、where(cond,a,b)（惰性求值）、
sqrt(x)、abs(x)；比较符只能出现在 where 条件里。
loop 内可用：i、n、递推状态名（=第 i 层状态）、<名>_next（第 i+1 层状态）。
final 内可用：<名>_first / <名>_last（递推首/末状态）。

【已知构造机制（参照系）】
1. FKT 1.707：层 4xa、层 4xb、终作业 1；最优 a≈0.2071、b=0.5。机制：同尺寸作业要么全分散
   （每台一个），要么碰撞立即给出高比值。
2. Rudin √3：V=√3−1−ε、M=(3V−2)/2；状态 (S,A,B) 递推 S'=M*A、A'=(A−2*B)/4、
   继续层 B'=S'−A'−M*A'，终止层（A'/S'>=V）夹逼 B'=S'−A'；每层 4xB+3xA+(A+2*A_next)，
   顶层 4xB+4xA；**层序 rev（层 n 在前）**；终作业 2*A_first。
3. Braun c1≈1.7310：c 是 6c**3−28c**2+38c−13=0 在 [5/3,2] 的根；序列 L0x4,S0x4,L1x4,S1x3,Sp1,F，
   尺寸全是 c 的有理函数（如 S0=(c−1)/(2−c)）。
共同骨架：魔法常数由极小多项式唯一锁定，使某条强制路径的比值精确坍缩到目标值。
**好模板必须在 solve/defs 里声明代数约束；只有裸自由尺寸的模板几乎必然 <1.707。**

【陷阱清单】
- 层序错误值暴跌（Rudin fwd 只有 5/3）；拿不准就 rev
- 每层作业数通常是 m=4 或 m−1=3（层分离论证的前提）
- 作业尺寸必须全为正；终作业常取 2×最小层参数或 1
- where 惰性求值：未选中分支可以含非法引用（例如 i==n 分支外的 A_next）
"""


def user_prompt(n):
    return f"""生成 {n} 个互不相同的 m=4 对抗模板。多样性要求：
- 至少覆盖三类种子：FKT 变体、Rudin 变体（改递推/层构成/终止条件）、Braun 变体（改层数/几何比）；
  允许 1-2 个混合/全新结构
- 每个模板 description 第一句写"种子=X；变异点=Y"
- 尺寸参数可以只给合理初值（后续有数值优化器精修），但代数约束（solve/defs）必须精确声明
只输出 JSON 数组。"""


def call_qwen(api_key, model, messages, temperature, max_tokens, no_think=False):
    """流式调用（reasoning 模型生成慢，流式可避免读超时）。"""
    headers = {"Authorization": f"Bearer {api_key}",
               "Content-Type": "application/json"}
    body = {"model": model, "messages": messages,
            "temperature": temperature, "max_tokens": max_tokens,
            "stream": True}
    if no_think:
        body["enable_thinking"] = False
    r = requests.post(API_URL, headers=headers, json=body,
                      timeout=(30, 1800), stream=True)
    if r.status_code != 200:
        raise RuntimeError(f"API {r.status_code}: {r.text[:300]}")
    parts, usage = [], {}
    for line in r.iter_lines(decode_unicode=True):
        if not line or not line.startswith("data:"):
            continue
        payload = line[5:].strip()
        if payload == "[DONE]":
            break
        try:
            chunk = json.loads(payload)
        except json.JSONDecodeError:
            continue
        if chunk.get("usage"):
            usage = chunk["usage"]
        ch = chunk.get("choices") or [{}]
        delta = ch[0].get("delta") or {}
        if delta.get("content"):
            parts.append(delta["content"])
            print(".", end="", flush=True)
    print()
    return "".join(parts), usage


def extract_json_array(text):
    t = text.strip()
    t = re.sub(r"^```(?:json)?\s*", "", t)
    t = re.sub(r"\s*```$", "", t)
    i, j = t.find("["), t.rfind("]")
    if i < 0 or j < 0:
        raise ValueError("回复中没有 JSON 数组")
    return json.loads(t[i:j + 1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=10)
    ap.add_argument("--model", type=str, default=DEFAULT_MODEL)
    ap.add_argument("--temperature", type=float, default=1.0)
    ap.add_argument("--max-tokens", type=int, default=16000)
    ap.add_argument("--per-call", type=int, default=8, help="单次 API 调用生成的模板数（防截断）")
    ap.add_argument("--no-think", action="store_true", help="关闭思考模式（更快）")
    ap.add_argument("--out", type=str,
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "llm_pool"))
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()

    system, user = SYSTEM_PROMPT, user_prompt(a.n)
    if a.dry_run:
        print("=== SYSTEM ===")
        print(system)
        print("=== USER ===")
        print(user)
        print(f"prompt 字符数: system={len(system)}, user={len(user)}")
        return

    api_key = os.environ.get("DASHSCOPE_API_KEY")
    if not api_key:
        print("错误：环境变量 DASHSCOPE_API_KEY 未设置")
        sys.exit(1)

    os.makedirs(a.out, exist_ok=True)
    ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    tpls = []
    batches = [a.per_call] * (a.n // a.per_call)
    if a.n % a.per_call:
        batches.append(a.n % a.per_call)
    for bi, bn in enumerate(batches):
        t0 = time.time()
        try:
            text, usage = call_qwen(api_key, a.model,
                                    [{"role": "system", "content": system},
                                     {"role": "user", "content": user_prompt(bn)}],
                                    a.temperature, a.max_tokens, a.no_think)
        except Exception as e:
            print(f"批次 {bi + 1} API 失败: {e}")
            continue
        dt = time.time() - t0
        print(f"批次 {bi + 1}/{len(batches)}: {dt:.1f}s, usage={usage}")
        try:
            tpls.extend(extract_json_array(text))
        except Exception as e:
            bad = os.path.join(a.out, f"raw_{ts}_b{bi}.txt")
            open(bad, "w", encoding="utf-8").write(text)
            print(f"  JSON 解析失败: {e}；原始回复存 {bad}（可手工抢救）")
    if not tpls:
        print("没有可用模板")
        sys.exit(1)

    n_ok, n_bad = 0, 0
    for k, tpl in enumerate(tpls):
        if not isinstance(tpl, dict):
            n_bad += 1
            continue
        errs = template_schema.validate(tpl)
        tag = f"qwen_{ts}_{k:02d}"
        if errs:
            tpl["_validation_errors"] = errs
            n_bad += 1
        else:
            n_ok += 1
        open(os.path.join(a.out, tag + ".json"), "w", encoding="utf-8").write(
            json.dumps(tpl, ensure_ascii=False, indent=2))
        status = "VALID" if not errs else "INVALID"
        print(f"  [{status}] {tag}: {tpl.get('name', '?')} {errs[:1] if errs else ''}")
    print(f"\n共 {len(tpls)} 个：合法 {n_ok}，非法 {n_bad}（均存 {a.out}，非法的带 _validation_errors 字段）")
    print(f"下一步：python pool_screen.py --dir {os.path.basename(a.out)}")


if __name__ == "__main__":
    main()
