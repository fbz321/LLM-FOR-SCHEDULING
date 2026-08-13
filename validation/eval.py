#!/usr/bin/env python3
"""
验证集评估脚本
=============
对固定验证集运行模型推理，计算 pass@k、平均生成长度、非法输出率等指标。

用法:
  # 基本评估（不运行 Lean 检查）
  python3 eval.py --adapter /root/backups/round1 --num-samples 5

  # 含 Lean 编译检查
  python3 eval.py --adapter /root/backups/r6 --num-samples 5 --lean-check

  # 指定输出目录
  python3 eval.py --adapter /root/backups/r7 --num-samples 5 --output results_r7

依赖:
  torch, transformers, peft, accelerate, bitsandbytes
"""

import json
import os
import re
import sys
import time
import argparse
import subprocess

from pathlib import Path
from typing import List, Dict, Optional, Tuple
from collections import defaultdict

# ── 默认路径 ──────────────────────────────────────────────────────

DEFAULT_BASE_MODEL = "/root/autodl-tmp/models/deepseek-math-7b-base"
DEFAULT_VALIDATION_SET = os.path.join(os.path.dirname(__file__), "validation_gaps.json")
DEFAULT_LEAN_PROJECT = "/root/autodl-tmp/ai4math"
DEFAULT_OUTPUT_DIR = os.path.join(os.path.dirname(__file__), "results")

# ── 非法输出检测 ──────────────────────────────────────────────────

# 这些模式表示模型输出了非 Lean 代码
ILLEGAL_PATTERNS = [
    (r"^(Here|Sure|Let me|I (will|need|can|think)|The (proof|key|idea|strategy|lemma))",
     "natural_language_start"),
    (r"(import\s+\S+){3,}", "repeated_imports"),  # more than 2 imports
    (r"```", "markdown_code_block"),
    (r"^\s*(#|//|--)\s*(Here|This|We|The|Note)", "comment_explanation"),
    (r"open\s+OnlineScheduling\s*\n\s*open\s+OnlineScheduling", "repeated_open"),
]


def check_illegal_output(text: str) -> List[str]:
    """检查输出是否包含非法模式。返回匹配的类别列表。"""
    issues = []
    for pattern, category in ILLEGAL_PATTERNS:
        if re.search(pattern, text, re.MULTILINE | re.IGNORECASE):
            issues.append(category)
    return issues


def is_empty_or_trivial(text: str) -> bool:
    """检查输出是否为空或仅包含空白/注释。"""
    cleaned = re.sub(r'(--[^\n]*|/\-[^*]*-\/)', '', text)  # 去除注释
    cleaned = cleaned.strip()
    return len(cleaned) < 5


def extract_generated_only(prompt: str, full_output: str) -> str:
    """
    从完整输出中只提取模型生成的部分。
    DeepSeek 格式: prompt 以 "Assistant:" 结尾，模型从该位置接续生成。
    """
    # 方案 1: 查找 Assistant 标记后的内容（支持 deepseek 和 deepseek3 两种模板）
    for marker in ["<｜Assistant｜>", "Assistant:"]:
        pos = full_output.rfind(marker)
        if pos >= 0:
            generated = full_output[pos + len(marker):]
            return generated.strip()

    # 方案 2: 去掉 prompt 前缀
    if full_output.startswith(prompt):
        generated = full_output[len(prompt):]
        return generated.strip()

    # 方案 3: 找最长公共前缀
    generated = full_output
    min_len = min(len(prompt), len(full_output))
    for i in range(min_len - 1, 10, -1):
        if prompt[:i] == full_output[:i]:
            generated = full_output[i:]
            break
    return generated.strip()


# ── 证明体提取 ────────────────────────────────────────────────────

def _extract_proof_only(text: str) -> Optional[str]:
    """
    从模型生成内容中提取 proof body（:= by 之后的部分）。
    模型倾向于从 import 开始重新生成整个定理，但我们只需要 proof body
    来替换 gap 中的 sorry。
    返回 proof body 字符串，如果无法提取则返回 None。
    """
    # 找最后一个 := by（因为模型可能重复了 theorem 声明）
    by_match = list(re.finditer(r':=\s*by\s*\n', text))
    if not by_match:
        # 尝试单行 := by ...
        by_match_single = re.search(r':=\s*by\s+(.+)', text, re.DOTALL)
        if by_match_single:
            return by_match_single.group(1).strip()
        return None

    # 取最后一个 := by 之后的内容
    last_by = by_match[-1]
    proof_start = last_by.end()
    proof_body = text[proof_start:].strip()

    # 去掉末尾可能重复的内容（namespace end, imports 等）
    # 找第一行不以空格/空白开头的（说明回到了顶层）
    lines = proof_body.split('\n')
    clean_lines = []
    for l in lines:
        if l.strip() == '':
            clean_lines.append(l)
        elif l[0] in (' ', '\t', '·'):
            clean_lines.append(l)
        else:
            # 非缩进行 = 回到顶层命令，截断
            break
    return '\n'.join(clean_lines).strip() if clean_lines else proof_body


# ── Lean 编译检查 ─────────────────────────────────────────────────

def check_lean_compiles(code: str, lean_project: str, timeout: int = 30) -> Tuple[bool, str]:
    """
    检查生成的 Lean 代码是否能编译。
    将代码写入 Lean 项目目录中的临时文件，运行 lake env lean 检查。
    返回 (success, error_message)。
    """
    import uuid
    unique_name = f"_eval_{uuid.uuid4().hex[:8]}.lean"
    dest_path = os.path.join(lean_project, unique_name)

    try:
        with open(dest_path, 'w', encoding='utf-8') as f:
            f.write(code)

        # 运行 lake env lean
        result = subprocess.run(
            ["lake", "env", "lean", unique_name],
            cwd=lean_project,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        # Filter out non-fatal lake warnings
        stderr_filtered = '\n'.join(
            l for l in result.stderr.split('\n')
            if 'manifest out of date' not in l
            and 'use `lake update' not in l
            and 'warning: mathlib:' not in l
            and 'has local changes' not in l
        ).strip()
        success = result.returncode == 0 or (
            stderr_filtered == ""
            and "error:" not in result.stdout
            and "error:" not in result.stderr
        )
        error_msg = stderr_filtered if not success else ""
        return success, error_msg
    except subprocess.TimeoutExpired:
        return False, "Lean check timed out"
    except FileNotFoundError:
        return False, "lake command not found"
    finally:
        # 清理临时文件
        try:
            os.unlink(dest_path)
        except (OSError, FileNotFoundError):
            pass


# ── 模型推理 ──────────────────────────────────────────────────────

def load_model_and_tokenizer(base_model: str, adapter_path: Optional[str] = None):
    """加载 base model 和可选的 LoRA adapter。"""
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer
    from peft import PeftModel

    print(f"Loading base model: {base_model}")
    model = AutoModelForCausalLM.from_pretrained(
        base_model,
        torch_dtype=torch.bfloat16,
        device_map="auto",
        trust_remote_code=True,
    )
    tokenizer = AutoTokenizer.from_pretrained(
        base_model, trust_remote_code=True
    )

    if adapter_path:
        print(f"Loading LoRA adapter: {adapter_path}")
        model = PeftModel.from_pretrained(model, adapter_path)

    model.eval()
    return model, tokenizer


def generate_completion(
    model, tokenizer, prompt: str,
    max_new_tokens: int = 512,
    temperature: float = 0.3,
    do_sample: bool = True,
    top_p: float = 0.95,
) -> str:
    """生成一个补全。"""
    import torch

    inputs = tokenizer(prompt, return_tensors="pt").to(model.device)
    with torch.no_grad():
        outputs = model.generate(
            **inputs,
            max_new_tokens=max_new_tokens,
            temperature=temperature,
            do_sample=do_sample,
            top_p=top_p,
            pad_token_id=tokenizer.eos_token_id,
        )
    full = tokenizer.decode(outputs[0], skip_special_tokens=True)
    return full


def format_prompt(sample: Dict) -> str:
    """使用 DeepSeek chat template: User: ...\n\nAssistant:"""
    return format_prompt_deepseek(sample)


def format_prompt_deepseek(sample: Dict) -> str:
    """DeepSeek 训练模板格式 (LLaMA-Factory template: deepseek):
    User: {instruction}\n\n{input}\n\nAssistant:
    """
    instruction = sample.get("instruction", "")
    code_with_gap = sample.get("input", "")
    return f"User: {instruction}\n\n{code_with_gap}\n\nAssistant:"


def format_prompt_deepseek3(sample: Dict) -> str:
    """DeepSeek3/Prover 模板 (LLaMA-Factory template: deepseek3):
    <｜User｜>{instruction}\n\n{input}<｜Assistant｜>
    """
    instruction = sample.get("instruction", "")
    code_with_gap = sample.get("input", "")
    return f"<｜User｜>{instruction}\n\n{code_with_gap}<｜Assistant｜>"


def format_prompt_simple(sample: Dict) -> str:
    """简单的代码补全格式（仅 Lean 代码，不用 chat template）。"""
    code_with_gap = sample.get("input", "")
    return code_with_gap


def format_prompt_nl2lean(sample: Dict, template: str = "deepseek") -> str:
    """NL→Lean 任务的 prompt 格式。"""
    instruction = sample.get("instruction", "")
    nl_input = sample.get("input", "")
    if template == "deepseek3":
        return f"<｜User｜>{instruction}\n\n{nl_input}<｜Assistant｜>"
    return f"User: {instruction}\n\n{nl_input}\n\nAssistant:"


# ── 增强非法输出检测 ──────────────────────────────────────────────

ENHANCED_ILLEGAL_PATTERNS = [
    # Lean 结构问题
    (r'(lemma|theorem)\s+\S+.*(lemma|theorem)\s+\S+', "duplicate_theorem"),
    (r'(lemma|theorem)\s+\S+\s*:\s*$', "theorem_without_by"),  # no := by
    (r'\b(averageLoad|known_sum_average|onlineAlgorithm|list_scheduling)\b', "fake_identifier"),
    # 缩进断裂
    (r'^\S.*\n  \S.*\n\S', "indentation_break"),
]


def check_enhanced_illegal(text: str) -> List[str]:
    """检查更细微的非法输出模式。"""
    issues = []
    for pattern, category in ENHANCED_ILLEGAL_PATTERNS:
        if re.search(pattern, text, re.MULTILINE):
            issues.append(category)
    return issues


# ── NL→Lean 任务评估 ──────────────────────────────────────────────

def evaluate_single_nl2lean(
    model, tokenizer, sample: Dict,
    num_samples: int = 5,
    lean_check: bool = False,
    lean_project: str = DEFAULT_LEAN_PROJECT,
) -> Dict:
    """对单个 NL→Lean 任务评估。模型从 NL 描述生成完整 Lean 代码。"""
    sample_id = sample["id"]
    source = sample.get("source", "unknown")
    prompt = format_prompt_nl2lean(sample)

    completions = []
    for k in range(num_samples):
        t0 = time.time()
        full_output = generate_completion(model, tokenizer, prompt)
        elapsed = time.time() - t0

        generated = extract_generated_only(prompt, full_output)
        generated_len = len(generated)
        illegal = check_illegal_output(generated)
        enhanced_illegal = check_enhanced_illegal(generated)
        illegal.extend(enhanced_illegal)
        is_empty = is_empty_or_trivial(generated)
        lean_ok = None
        lean_error = None

        if lean_check and generated and not is_empty:
            lean_ok, lean_error = check_lean_compiles(generated, lean_project)

        completions.append({
            "sample_index": k,
            "generated": generated,
            "generated_length": generated_len,
            "elapsed_seconds": round(elapsed, 2),
            "is_empty": is_empty,
            "illegal_patterns": illegal,
            "lean_passes": lean_ok,
            "lean_error": lean_error[:500] if lean_error else None,
        })

    any_pass = any(c["lean_passes"] for c in completions) if lean_check else None
    any_nonempty = any(not c["is_empty"] for c in completions)
    any_clean = any(not c["is_empty"] and len(c["illegal_patterns"]) == 0 for c in completions)
    avg_len = sum(c["generated_length"] for c in completions) / len(completions)
    illegal_rate = sum(1 for c in completions if len(c["illegal_patterns"]) > 0) / len(completions)

    return {
        "sample_id": sample_id,
        "type": "nl2lean",
        "source": source,
        "expected_name": sample.get("expected_name", ""),
        "num_samples": num_samples,
        "pass@1": any_pass if lean_check else (any_clean if not lean_check else None),
        "pass@k": any_pass if lean_check else (any_clean if not lean_check else None),
        "any_nonempty": any_nonempty,
        "any_clean": any_clean,
        "avg_generated_length": round(avg_len, 1),
        "illegal_output_rate": round(illegal_rate, 3),
        "lean_checked": lean_check,
        "completions": completions,
    }


# ── 评估主流程 ────────────────────────────────────────────────────

def evaluate_single_gap(
    model, tokenizer, sample: Dict,
    num_samples: int = 5,
    lean_check: bool = False,
    lean_project: str = DEFAULT_LEAN_PROJECT,
    prompt_style: str = "simple",
) -> Dict:
    """
    对单个 gap 生成 num_samples 个补全并评估。
    返回该 gap 的详细评估结果。
    """
    gap_id = sample["id"]
    difficulty = sample.get("difficulty", "unknown")
    source = sample.get("source", "unknown")

    if prompt_style == "deepseek3":
        prompt = format_prompt_deepseek3(sample)
    elif prompt_style == "deepseek":
        prompt = format_prompt_deepseek(sample)
    else:
        prompt = format_prompt_simple(sample)

    completions = []
    for k in range(num_samples):
        t0 = time.time()
        full_output = generate_completion(model, tokenizer, prompt)
        elapsed = time.time() - t0

        generated = extract_generated_only(prompt, full_output)
        generated_len = len(generated)
        illegal = check_illegal_output(generated)
        is_empty = is_empty_or_trivial(generated)
        lean_ok = None
        lean_error = None

        # 可选 Lean 编译检查
        if lean_check and generated and not is_empty:
            # 关键: 只取生成内容中的 proof body（去掉重复的 header）
            # 模型倾向于重新生成整个定理，需要提取 := by 之后的部分
            proof_body = _extract_proof_only(generated)
            if proof_body:
                # 用 proof body 替换 input 中的 sorry
                full_code = sample["input"].replace("sorry", proof_body, 1)
            else:
                full_code = sample["input"].replace("sorry", generated, 1)
            lean_ok, lean_error = check_lean_compiles(full_code, lean_project)

        completions.append({
            "sample_index": k,
            "generated": generated,
            "generated_length": generated_len,
            "elapsed_seconds": round(elapsed, 2),
            "is_empty": is_empty,
            "illegal_patterns": illegal,
            "lean_passes": lean_ok,
            "lean_error": lean_error[:500] if lean_error else None,
        })

    # 汇总该 gap 的指标
    any_pass = any(
        c["lean_passes"] for c in completions
    ) if lean_check else None

    any_nonempty = any(not c["is_empty"] for c in completions)
    any_clean = any(
        not c["is_empty"] and len(c["illegal_patterns"]) == 0
        for c in completions
    )

    avg_len = sum(c["generated_length"] for c in completions) / len(completions)
    illegal_rate = sum(
        1 for c in completions if len(c["illegal_patterns"]) > 0
    ) / len(completions)

    return {
        "gap_id": gap_id,
        "difficulty": difficulty,
        "source": source,
        "num_samples": num_samples,
        "pass@1": any_pass if lean_check else (any_clean if not lean_check else None),
        "pass@k": any_pass if lean_check else (any_clean if not lean_check else None),
        "any_nonempty": any_nonempty,
        "any_clean": any_clean,
        "avg_generated_length": round(avg_len, 1),
        "illegal_output_rate": round(illegal_rate, 3),
        "lean_checked": lean_check,
        "completions": completions,
    }


def evaluate_all(
    model, tokenizer,
    validation_set: List[Dict],
    num_samples: int = 5,
    lean_check: bool = False,
    lean_project: str = DEFAULT_LEAN_PROJECT,
    prompt_style: str = "simple",
) -> Dict:
    """对所有验证 gap 进行评估。"""
    results = []
    n = len(validation_set)

    print(f"\n{'='*60}")
    print(f"Evaluating {n} validation gaps (num_samples={num_samples})")
    if lean_check:
        print(f"Lean check: ENABLED (project: {lean_project})")
    else:
        print(f"Lean check: DISABLED")
    print(f"{'='*60}\n")

    for i, sample in enumerate(validation_set):
        task_type = sample.get("type", "lean_gap")
        sample_id = sample.get("id", sample.get("gap_id", "?"))
        print(f"[{i+1}/{n}] {sample_id} ({task_type}) ... ", end="", flush=True)

        t_start = time.time()
        if task_type == "nl2lean":
            result = evaluate_single_nl2lean(
                model, tokenizer, sample,
                num_samples=num_samples,
                lean_check=lean_check,
                lean_project=lean_project,
            )
        else:
            result = evaluate_single_gap(
                model, tokenizer, sample,
                num_samples=num_samples,
                lean_check=lean_check,
                lean_project=lean_project,
                prompt_style=prompt_style,
            )
        elapsed = time.time() - t_start

        # 简要输出
        if lean_check:
            status = "✅ PASS" if result["pass@k"] else "❌ FAIL"
        else:
            status = "✅" if result["any_clean"] else ("⚠️  nonempty" if result["any_nonempty"] else "❌ empty")
        print(f"{status}  avg_len={result['avg_generated_length']}  "
              f"illegal={result['illegal_output_rate']:.0%}  "
              f"({elapsed:.1f}s)")

        results.append(result)

    return aggregate_results(results, num_samples)


def aggregate_results(results: List[Dict], num_samples: int) -> Dict:
    """汇总所有 gap 的评估结果。"""
    n = len(results)
    if n == 0:
        return {"error": "No results"}

    # pass@k 统计（如果用 lean check，以 lean_passes 为准；否则以 any_clean 为准）
    pass_count = sum(
        1 for r in results
        if r["pass@k"] is True
    )

    # 按难度分组
    by_difficulty = defaultdict(lambda: {"count": 0, "pass": 0, "avg_len": 0, "illegal_rate": 0})
    for r in results:
        d = r["difficulty"]
        by_difficulty[d]["count"] += 1
        if r["pass@k"]:
            by_difficulty[d]["pass"] += 1
        by_difficulty[d]["avg_len"] += r["avg_generated_length"]
        by_difficulty[d]["illegal_rate"] += r["illegal_output_rate"]

    for d in by_difficulty:
        by_difficulty[d]["avg_len"] /= by_difficulty[d]["count"]
        by_difficulty[d]["illegal_rate"] /= by_difficulty[d]["count"]
        by_difficulty[d]["pass_rate"] = (
            by_difficulty[d]["pass"] / by_difficulty[d]["count"]
            if by_difficulty[d]["count"] > 0 else 0
        )

    # 按来源分组
    by_source = defaultdict(lambda: {"count": 0, "pass": 0})
    for r in results:
        s = r["source"]
        by_source[s]["count"] += 1
        if r["pass@k"]:
            by_source[s]["pass"] += 1

    for s in by_source:
        by_source[s]["pass_rate"] = (
            by_source[s]["pass"] / by_source[s]["count"]
            if by_source[s]["count"] > 0 else 0
        )

    avg_len = sum(r["avg_generated_length"] for r in results) / n
    avg_illegal = sum(r["illegal_output_rate"] for r in results) / n

    return {
        "total_gaps": n,
        "num_samples_per_gap": num_samples,
        "pass@k": pass_count,
        "pass_rate": round(pass_count / n, 4),
        "avg_generated_length": round(avg_len, 1),
        "avg_illegal_output_rate": round(avg_illegal, 4),
        "by_difficulty": dict(by_difficulty),
        "by_source": dict(by_source),
        "detailed_results": results,
    }


# ── 命令行入口 ────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Evaluate a trained model on the Lean proof validation set"
    )
    parser.add_argument(
        "--adapter", type=str, required=True,
        help="Path to LoRA adapter (e.g., /root/backups/round1)"
    )
    parser.add_argument(
        "--base-model", type=str, default=DEFAULT_BASE_MODEL,
        help="Path to base model"
    )
    parser.add_argument(
        "--validation-set", type=str, default=DEFAULT_VALIDATION_SET,
        help="Path to validation set JSON (gap-filling or nl2lean)"
    )
    parser.add_argument(
        "--num-samples", type=int, default=5,
        help="Number of completions per gap (default: 5)"
    )
    parser.add_argument(
        "--lean-check", action="store_true",
        help="Run lake env lean to verify compilability"
    )
    parser.add_argument(
        "--lean-project", type=str, default=DEFAULT_LEAN_PROJECT,
        help="Path to Lean project for compilation check"
    )
    parser.add_argument(
        "--output", type=str, default=None,
        help="Output directory for results"
    )
    parser.add_argument(
        "--prompt-style", type=str, default="deepseek",
        choices=["deepseek", "deepseek3", "simple"],
        help="Prompt format: 'deepseek' (User:/Assistant:), 'deepseek3' (<｜User｜>/<｜Assistant｜>), or 'simple'"
    )
    parser.add_argument(
        "--gpu", type=str, default="0",
        help="CUDA_VISIBLE_DEVICES (default: 0)"
    )
    args = parser.parse_args()

    # 设置 GPU
    os.environ["CUDA_VISIBLE_DEVICES"] = args.gpu

    # 加载验证集
    print(f"Loading validation set: {args.validation_set}")
    with open(args.validation_set, "r", encoding="utf-8") as f:
        validation_set = json.load(f)
    print(f"  {len(validation_set)} gaps loaded")

    # 输出目录
    if args.output:
        output_dir = args.output
    else:
        adapter_name = os.path.basename(args.adapter.rstrip('/'))
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        output_dir = os.path.join(DEFAULT_OUTPUT_DIR, f"{adapter_name}_{timestamp}")

    os.makedirs(output_dir, exist_ok=True)

    # 加载模型
    model, tokenizer = load_model_and_tokenizer(args.base_model, args.adapter)

    # 运行评估
    t_start = time.time()
    results = evaluate_all(
        model, tokenizer,
        validation_set,
        num_samples=args.num_samples,
        lean_check=args.lean_check,
        lean_project=args.lean_project,
        prompt_style=args.prompt_style,
    )
    total_time = time.time() - t_start

    # 打印总结
    print(f"\n{'='*60}")
    print(f"EVALUATION SUMMARY")
    print(f"{'='*60}")
    print(f"  Total gaps:              {results['total_gaps']}")
    print(f"  Samples per gap:         {results['num_samples_per_gap']}")
    if args.lean_check:
        print(f"  pass@{args.num_samples}:           {results['pass@k']}/{results['total_gaps']} ({results['pass_rate']:.1%})")
    else:
        print(f"  Clean outputs:           {results['pass@k']}/{results['total_gaps']} ({results['pass_rate']:.1%})")
    print(f"  Avg generated length:    {results['avg_generated_length']:.0f} chars")
    print(f"  Avg illegal output rate: {results['avg_illegal_output_rate']:.1%}")
    print(f"  Total time:              {total_time:.0f}s")

    if not args.lean_check:
        print(f"\n  ⚠️  Lean check disabled. Run with --lean-check for compilability verification.")

    print(f"\n  By difficulty:")
    for diff, stats in sorted(results.get("by_difficulty", {}).items()):
        bar = "█" * int(stats["pass_rate"] * 20)
        print(f"    {diff:<8} {stats['pass']}/{stats['count']} pass  {stats['pass_rate']:.0%}  {bar}")

    print(f"\n  By source:")
    for src, stats in sorted(results.get("by_source", {}).items()):
        print(f"    {src:<30} {stats['pass']}/{stats['count']} ({stats['pass_rate']:.0%})")

    # 保存结果
    # 详细结果（含所有 completion）
    full_path = os.path.join(output_dir, "full_results.json")
    with open(full_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    print(f"\n  Full results saved to: {full_path}")

    # 摘要（不含 completion 详情，方便快速对比）
    summary = {k: v for k, v in results.items() if k != "detailed_results"}
    summary["adapter"] = args.adapter
    summary["base_model"] = args.base_model
    summary["lean_checked"] = args.lean_check
    summary["evaluation_time"] = round(total_time, 0)

    summary_path = os.path.join(output_dir, "summary.json")
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)
    print(f"  Summary saved to: {summary_path}")

    # 失败详情（仅当 lean check 时）
    if args.lean_check:
        failures = [
            r for r in results["detailed_results"]
            if not r["pass@k"]
        ]
        if failures:
            fail_path = os.path.join(output_dir, "failures.json")
            fail_report = []
            for r in failures:
                for c in r["completions"]:
                    if not c["lean_passes"] and not c["is_empty"]:
                        fail_report.append({
                            "gap_id": r["gap_id"],
                            "sample": c["sample_index"],
                            "lean_error": c["lean_error"],
                            "generated": c["generated"][:300],
                        })
            with open(fail_path, "w", encoding="utf-8") as f:
                json.dump(fail_report, f, indent=2, ensure_ascii=False)
            print(f"  Failure details saved to: {fail_path}")

    print(f"\nDone. Output directory: {output_dir}")


if __name__ == "__main__":
    main()
