#!/usr/bin/env python3
"""
生成 validation_nl2lean.json — NL→Lean 固定验证集
从 17 个未训练的完整定理中创建 NL 描述 → Lean 代码的验证对。
"""

import json, re, os

LEAN_DIR = "/root/autodl-tmp/ai4math/OnlineScheduling"
OUTPUT = os.path.join(os.path.dirname(__file__), "validation_nl2lean.json")

# ── NL 描述（手工编写）────────────────────────────────────────────
# 每个定理配 1-3 句中文自然语言描述

NL_DESCRIPTIONS = {
    # Basic.lean
    "makespan_ge_each": (
        "证明在线调度中 makespan（最大机器负载）的基本性质："
        "任意一台机器的负载不超过 makespan。"
    ),
    "zero_loads_nonneg": (
        "证明：当所有机器负载为零时，makespan 非负。"
    ),
    "sum_step": (
        "证明在线算法执行一步后的负载守恒："
        "所有机器负载之和等于执行前的负载和加上新任务的大小。"
    ),
    "runAlgorithm_total_load": (
        "证明负载守恒定理：运行任意在线算法处理完整任务序列后，"
        "所有机器的负载之和等于任务序列的总处理时间。"
    ),
    "runAlgorithm_append_singleton": (
        "证明：在任务序列末尾追加一个新任务后运行算法，"
        "等价于先运行原序列、再对新任务执行一步 step。"
    ),
    "runAlgorithm_loads_nonneg": (
        "证明：如果任务序列中所有处理时间都非负，"
        "运行算法后每台机器的负载也非负。"
    ),
    "mem_competitive_set_iff": (
        "证明：c 属于算法 alg 的竞争比集合"
        "当且仅当 alg 是 c-competitive 的。"
    ),

    # Algorithms/ListScheduling.lean
    "graham_tightness": (
        "陈述 Graham 定理的紧性：当机器数 m ≥ 2 时，存在任务序列使得 "
        "List Scheduling 算法的 makespan 恰好等于 (2 - 1/m) * OPT，"
        "即上界是紧的。该结果在 Graham 1966 年论文中证明。"
    ),

    # LowerBounds layers
    "layer_forces_separation": (
        "在在线调度的层次构造方法中，证明一个 layer 可以强制分离："
        "给定 layer 和当前负载，算法要么违反竞争比，要么将负载均匀分配。"
        "这是 Faigle-Kern-Turan 层次下界方法的核心引理。"
    ),
    "loads_are_multiples_from_zero": (
        "证明：从零负载开始，处理 t 个大小为 x 的相同任务后，"
        "每台机器的负载是 x 的整数倍。"
    ),

    # LowerBounds/GoSLowerBound.lean
    "gos_online_lower_bound_five_thirds": (
        "陈述 Grade of Service 在线调度中的经典下界：对 m=2，"
        "任何确定性在线算法的竞争比至少为 5/3。"
        "这是 Park & Chang (2005) 的结果。"
    ),

    # LowerBounds/KnownSumLowerBound.lean
    "known_sum_m2_upper_bound_four_thirds": (
        "在已知总处理时间的半在线模型（Known Sum）中，"
        "对 m=2 证明上界 4/3：存在算法达到竞争比 4/3。"
    ),

    # LowerBounds/BinStretchingLowerBound.lean
    "bin_stretching_lower_bound_four_thirds": (
        "在 Bin Stretching 模型（已知 OPT 的半在线调度）中，"
        "对 m=2 证明下界 4/3：任何确定性算法的竞争比至少为 4/3。"
        "该结果由 Azar & Regev (2001) 给出。"
    ),

    # Models/KnownSum.lean
    "known_sum_m2_optimal_ratio": (
        "陈述已知总处理时间半在线模型中的经典结论："
        "对 m=2，上下界紧合，最优竞争比为 4/3。"
    ),
    "known_sum_m3_optimal_ratio": (
        "陈述已知总处理时间半在线模型中 m=3 的改进上界结果。"
    ),

    # Models/BinStretching.lean
    "bin_stretching_model_lower_bound_four_thirds": (
        "在 Bin Stretching 半在线模型中陈述下界结果："
        "对 m=2，确定性算法的竞争比下界为 4/3。"
    ),
    "bin_stretching_upper_bound": (
        "陈述 Bin Stretching 的渐进上界：对足够大的 m（m ≥ 60000），"
        "存在算法达到竞争比 139/93 < 1.495。"
    ),
}

def extract_theorem(fpath, name):
    """从 Lean 文件中提取指定定理的完整代码块"""
    with open(fpath) as f:
        content = f.read()

    # Find imports, opens, namespace
    imports = [l for l in content.split('\n') if l.startswith('import ')]
    opens = [l for l in content.split('\n') if l.startswith('open ')]
    namespaces = []
    in_ns = False
    for l in content.split('\n'):
        if l.strip().startswith('namespace '):
            in_ns = True
            namespaces.append(l)
        elif l.strip().startswith('end ') and in_ns:
            namespaces.append(l)

    # Find the theorem block
    blocks = re.split(r'\n(?=(?:lemma|theorem)\s+)', content)
    for block in blocks:
        name_match = re.match(r'(lemma|theorem)\s+(\S+)', block)
        if not name_match:
            continue
        if name_match.group(2).strip(" :(") == name:
            # Build full output
            header = '\n'.join(imports + opens)
            if namespaces:
                header += '\n' + '\n'.join(namespaces[:2])  # namespace + variable

            # Add noncomputable section if present
            section_match = re.search(r'(noncomputable section)', content)

            full = header + '\n\n'
            if section_match:
                full += 'noncomputable section\n\n'
            full += block.strip()

            if namespaces:
                full += '\n\nend ' + namespaces[0].strip().split()[1]

            return full.strip()
    return None

def main():
    samples = []
    count = 0

    for name, desc in sorted(NL_DESCRIPTIONS.items()):
        # Find which file contains this theorem
        found = None
        for root, dirs, files in os.walk(LEAN_DIR):
            for f in files:
                if f.endswith('.lean'):
                    fpath = os.path.join(root, f)
                    output = extract_theorem(fpath, name)
                    if output:
                        found = (fpath, output)
                        break
            if found:
                break

        if not found:
            print(f"  SKIP {name}: not found")
            continue

        fpath, output = found
        rel = fpath.replace(LEAN_DIR + "/", "")

        sample = {
            "id": f"nl2lean_val_{name}",
            "type": "nl2lean",
            "instruction": (
                "你是一个精通在线调度理论的 Lean 4 定理证明专家。"
                "将以下自然语言描述的数学问题转化为完整的 Lean 4 证明。"
                "只输出 Lean 代码，不要包含任何解释或注释。"
            ),
            "input": desc,
            "expected_name": name,
            "source": rel,
            "output": output,
        }
        samples.append(sample)
        count += 1
        print(f"  {name:<45} {rel:<40} OK")

    print(f"\nTotal: {count} NL→Lean validation samples")

    # Verify all outputs are sorry/axiom-free
    issues = []
    for s in samples:
        if "sorry" in s["output"]:
            issues.append(f"{s['id']}: sorry")
        if re.search(r'\baxiom\s+\w', s["output"]):
            issues.append(f"{s['id']}: axiom")

    if issues:
        print(f"\n⚠️  ISSUES: {len(issues)}")
        for i in issues:
            print(f"  {i}")
    else:
        print("✅ All outputs clean (no sorry/axiom)")

    # Save
    with open(OUTPUT, "w", encoding="utf-8") as f:
        json.dump(samples, f, indent=2, ensure_ascii=False)
    print(f"\nSaved: {OUTPUT}")
    print(f"Size: {len(json.dumps(samples, ensure_ascii=False))} bytes")

    # Summary
    by_source = {}
    for s in samples:
        src = s["source"]
        by_source[src] = by_source.get(src, 0) + 1
    print(f"\nBy source:")
    for src, n in sorted(by_source.items()):
        print(f"  {src}: {n}")

if __name__ == "__main__":
    main()
