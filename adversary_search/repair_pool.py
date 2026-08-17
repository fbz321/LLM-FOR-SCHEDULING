#!/usr/bin/env python3
"""修复循环：把漏斗 L1/L2 失败的模板连同精确错误回给 Qwen 修复一轮。

用法：
  python repair_pool.py --dir llm_pool                # 修复 dir 里所有失败模板
  python repair_pool.py --dir llm_pool --dry-run      # 只看收集到的失败清单
"""

import argparse
import datetime
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import template_schema
from generate import SYSTEM_PROMPT, call_qwen, extract_json_array

REPAIR_USER_TMPL = """以下是 {k} 个未通过验证的对抗模板及精确错误。请逐个修复，只输出 JSON 数组，
每个元素是修复后的完整模板，name 保持原名加后缀 _r1。

修复原则：
- 负/零尺寸：调整 params 数值或增加约束，确保所有展开尺寸为正
  （逐层检查递推的每个状态、where 的两个分支、final 作业）
- 未定义名字：补 params/defs 声明，或改用已定义的名字
- 递推不终止：修改 until 或 step，使其在 max_iter 内可达（参考 Rudin：until 用 A/S >= V）
- 保持原模板的结构意图（description 里的变异点），不要退化成平凡结构
- 幂运算必须用 **，严禁 ^

{blocks}
只输出 JSON 数组。"""


def collect_failures(dirpath):
    fails = []
    for fn in sorted(os.listdir(dirpath)):
        if not fn.endswith(".json") or fn.startswith("raw_") or "_r1" in fn:
            continue
        path = os.path.join(dirpath, fn)
        try:
            tpl = json.load(open(path, encoding="utf-8"))
        except Exception as e:
            fails.append((fn, None, f"JSON 解析错误: {e}"))
            continue
        tpl.pop("_validation_errors", None)
        errs = template_schema.validate(tpl)
        if errs:
            fails.append((fn, tpl, "；".join(errs)))
            continue
        try:
            template_schema.materialize(tpl)
        except template_schema.TplError as e:
            fails.append((fn, tpl, str(e)))
        except Exception as e:
            fails.append((fn, tpl, f"展开异常: {e}"))
    return fails


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--per-call", type=int, default=6)
    ap.add_argument("--model", type=str, default=None)
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()

    fails = collect_failures(a.dir)
    print(f"收集到 {len(fails)} 个失败模板：")
    for fn, tpl, err in fails:
        nm = tpl.get("name", "?") if tpl else "?"
        print(f"  - {fn} [{nm}]: {err[:100]}")
    if a.dry_run or not fails:
        return

    import generate as gen
    model = a.model or gen.DEFAULT_MODEL
    api_key = os.environ.get("DASHSCOPE_API_KEY")
    if not api_key:
        print("错误：DASHSCOPE_API_KEY 未设置")
        sys.exit(1)

    ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    n_ok = n_bad = 0
    for bi in range(0, len(fails), a.per_call):
        chunk = fails[bi:bi + a.per_call]
        blocks = []
        for fn, tpl, err in chunk:
            blocks.append(f"### 模板（文件 {fn}）\n错误：{err}\n原模板 JSON：\n"
                          + json.dumps(tpl, ensure_ascii=False))
        user = REPAIR_USER_TMPL.format(k=len(chunk), blocks="\n\n".join(blocks))
        print(f"\n修复批次 {bi // a.per_call + 1}（{len(chunk)} 个）...")
        try:
            text, usage = call_qwen(api_key, model,
                                    [{"role": "system", "content": SYSTEM_PROMPT},
                                     {"role": "user", "content": user}],
                                    0.5, 16000, no_think=True)
            print(f"  usage={usage}")
            fixed = extract_json_array(text)
        except Exception as e:
            print(f"  批次失败: {e}")
            continue
        for tpl in fixed:
            if not isinstance(tpl, dict):
                continue
            errs = template_schema.validate(tpl)
            tag = "repair_" + ts + f"_{n_ok + n_bad:02d}"
            if errs:
                tpl["_validation_errors"] = errs
                n_bad += 1
            else:
                n_ok += 1
            open(os.path.join(a.dir, tag + ".json"), "w", encoding="utf-8").write(
                json.dumps(tpl, ensure_ascii=False, indent=2))
            print(f"  [{'VALID' if not errs else 'INVALID'}] {tag}: {tpl.get('name', '?')}")
    print(f"\n修复产出：合法 {n_ok}，非法 {n_bad}")
    print("下一步：python pool_screen.py --dir " + os.path.basename(a.dir) + " --exact")


if __name__ == "__main__":
    main()
