#!/usr/bin/env python3
"""
生成固定验证集: 从未进入训练的定理中抽取 Lean→Lean gap。
每个定理生成多个 gap 变体（删除不同 tactic/block），总计 30-40 个样本。

使用的定理（均未在 R1-R7 训练数据中出现）:
  Basic.lean:         makespan_ge_average, opt_ge_both, runAlgorithm_mono,
                       sum_foldl_step, load_mono_on_prefix
  CompetitiveRatio:   competitive_implies_bounded, competitive_ratio_ge_one
  Models/KnownSum:    known_sum_opt_bound
"""

import json
import os
import re
from copy import deepcopy

# ── 验证集候选定理（完整的 Lean 代码，含 proof body） ──────────────────────

CANDIDATES = []

# --- Candidate 1: makespan_ge_average (Basic.lean L175-187) ---
CANDIDATES.append({
    "id": "val_makespan_ge_average",
    "source": "Basic.lean",
    "difficulty": "medium",
    "tactic_count": 8,
    "header": """import Mathlib
import OnlineScheduling.Basic

open Finset
open BigOperators

namespace OnlineScheduling

variable (m : ℕ) [NeZero m]

lemma makespan_ge_average (loads : Loads m) :
    (Finset.sum Finset.univ loads) / (m : ℝ) ≤ makespan m loads := by""",
    "proof_body": """  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have h_each_le : ∀ i, loads i ≤ makespan m loads := makespan_ge_each (m := m) loads
  have h_sum_le : (Finset.sum Finset.univ loads) ≤ (m : ℝ) * makespan m loads := by
    calc
      (Finset.sum Finset.univ loads) ≤ (Finset.sum Finset.univ (fun _ => makespan m loads)) :=
        Finset.sum_le_sum (fun i _ => h_each_le i)
      _ = (m : ℝ) * makespan m loads := by simp
  refine calc
    (Finset.sum Finset.univ loads) / (m : ℝ) ≤ ((m : ℝ) * makespan m loads) / (m : ℝ) :=
      div_le_div_of_nonneg_right h_sum_le (by linarith)
    _ = makespan m loads := by field_simp [hm_pos.ne']""",
    "footer": "\nend OnlineScheduling",
    # Define deletable blocks (each is 1-3 consecutive lines, independently removable)
    "deletable_blocks": [
        # Block 0: the hm_pos have
        {"lines": "  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m", "desc": "have hm_pos"},
        # Block 1: the h_each_le have
        {"lines": "  have h_each_le : ∀ i, loads i ≤ makespan m loads := makespan_ge_each (m := m) loads", "desc": "have h_each_le"},
        # Block 2: the h_sum_le calc block
        {"lines": """  have h_sum_le : (Finset.sum Finset.univ loads) ≤ (m : ℝ) * makespan m loads := by
    calc
      (Finset.sum Finset.univ loads) ≤ (Finset.sum Finset.univ (fun _ => makespan m loads)) :=
        Finset.sum_le_sum (fun i _ => h_each_le i)
      _ = (m : ℝ) * makespan m loads := by simp""", "desc": "h_sum_le calc block"},
        # Block 3: the refine calc (whole thing)
        {"lines": """  refine calc
    (Finset.sum Finset.univ loads) / (m : ℝ) ≤ ((m : ℝ) * makespan m loads) / (m : ℝ) :=
      div_le_div_of_nonneg_right h_sum_le (by linarith)
    _ = makespan m loads := by field_simp [hm_pos.ne']""", "desc": "final calc chain"},
        # Block 4: just the calc first step
        {"lines": "      div_le_div_of_nonneg_right h_sum_le (by linarith)", "desc": "div_le_div_of_nonneg_right"},
        # Block 5: just the calc last step
        {"lines": "    _ = makespan m loads := by field_simp [hm_pos.ne']", "desc": "field_simp cancel"},
    ],
})

# --- Candidate 2: opt_ge_both (Basic.lean L172-173) ---
CANDIDATES.append({
    "id": "val_opt_ge_both",
    "source": "Basic.lean",
    "difficulty": "easy",
    "tactic_count": 1,
    "header": """import Mathlib
import OnlineScheduling.Basic

open Finset

namespace OnlineScheduling

variable (m : ℕ) [NeZero m]

lemma opt_ge_both (σ : JobSequence) : max (maxJobSize σ) (totalLoad σ / (m : ℝ)) ≤ OPT σ :=""",
    "proof_body": """  max_le (opt_ge_max_job σ) (opt_ge_avg_load (m := m) σ)""",
    "footer": "\nend OnlineScheduling",
    "deletable_blocks": [
        {"lines": """  max_le (opt_ge_max_job σ) (opt_ge_avg_load (m := m) σ)""", "desc": "full proof (max_le)"},
    ],
})

# --- Candidate 3: runAlgorithm_mono (Basic.lean L152-163) ---
CANDIDATES.append({
    "id": "val_runAlgorithm_mono",
    "source": "Basic.lean",
    "difficulty": "hard",
    "tactic_count": 7,
    "header": """import Mathlib
import OnlineScheduling.Basic

open List

namespace OnlineScheduling

variable (m : ℕ) [NeZero m]

lemma runAlgorithm_mono (alg : OnlineAlgorithm m) (σ₁ σ₃ : JobSequence) (h_nonneg : ∀ p ∈ σ₃, 0 ≤ p) :
    ∀ i, runAlgorithm m alg σ₁ i ≤ runAlgorithm m alg (σ₁ ++ σ₃) i :=""",
    "proof_body": """  induction' σ₃ with p σ₃ ih generalizing σ₁
  · simp
  · intro i
    have hp_nonneg : 0 ≤ p := h_nonneg p (by simp)
    have h_rest : ∀ q ∈ σ₃, 0 ≤ q := λ q hq => h_nonneg q (by simp [hq])
    rw [show σ₁ ++ (p :: σ₃) = (σ₁ ++ [p]) ++ σ₃ by simp]
    have h_step : runAlgorithm m alg σ₁ i ≤ runAlgorithm m alg (σ₁ ++ [p]) i :=
      runAlgorithm_snoc (m := m) alg σ₁ p hp_nonneg i
    have h_ih := ih (σ₁ := σ₁ ++ [p]) h_rest i
    exact le_trans h_step h_ih""",
    "footer": "\nend OnlineScheduling",
    "deletable_blocks": [
        {"lines": "  induction' σ₃ with p σ₃ ih generalizing σ₁", "desc": "induction start"},
        {"lines": "  · simp", "desc": "nil case"},
        {"lines": """    have hp_nonneg : 0 ≤ p := h_nonneg p (by simp)
    have h_rest : ∀ q ∈ σ₃, 0 ≤ q := λ q hq => h_nonneg q (by simp [hq])""", "desc": "nonneg hypotheses"},
        {"lines": "    rw [show σ₁ ++ (p :: σ₃) = (σ₁ ++ [p]) ++ σ₃ by simp]", "desc": "rewrite append"},
        {"lines": """    have h_step : runAlgorithm m alg σ₁ i ≤ runAlgorithm m alg (σ₁ ++ [p]) i :=
      runAlgorithm_snoc (m := m) alg σ₁ p hp_nonneg i""", "desc": "h_step via runAlgorithm_snoc"},
        {"lines": "    have h_ih := ih (σ₁ := σ₁ ++ [p]) h_rest i", "desc": "induction hypothesis"},
        {"lines": "    exact le_trans h_step h_ih", "desc": "final le_trans"},
    ],
})

# --- Candidate 4: sum_foldl_step (Basic.lean L124-133) ---
CANDIDATES.append({
    "id": "val_sum_foldl_step",
    "source": "Basic.lean",
    "difficulty": "hard",
    "tactic_count": 6,
    "header": """import Mathlib
import OnlineScheduling.Basic

open Finset
open BigOperators
open List

namespace OnlineScheduling

variable (m : ℕ) [NeZero m]

lemma sum_foldl_step (alg : OnlineAlgorithm m) (loads_before : Loads m) (tau : JobSequence) :
    (∑ i : Fin m, (tau.foldl (step (m := m) alg) loads_before i)) =
    (∑ i, loads_before i) + totalLoad tau :=""",
    "proof_body": """  induction' tau with p tau ih generalizing loads_before
  · simp [totalLoad]
  · rw [List.foldl_cons]
    have h_step := sum_step (m := m) alg loads_before p
    have h := ih (step (m := m) alg loads_before p)
    rw [h, h_step]
    simp [totalLoad, add_comm, add_left_comm, add_assoc]""",
    "footer": "\nend OnlineScheduling",
    "deletable_blocks": [
        {"lines": "  induction' tau with p tau ih generalizing loads_before", "desc": "induction start"},
        {"lines": "  · simp [totalLoad]", "desc": "nil case"},
        {"lines": "  · rw [List.foldl_cons]", "desc": "rw foldl_cons"},
        {"lines": """    have h_step := sum_step (m := m) alg loads_before p
    have h := ih (step (m := m) alg loads_before p)""", "desc": "apply sum_step and ih"},
        {"lines": "    rw [h, h_step]", "desc": "rw h and h_step"},
        {"lines": "    simp [totalLoad, add_comm, add_left_comm, add_assoc]", "desc": "simp arithmetic"},
    ],
})

# --- Candidate 5: load_mono_on_prefix (Basic.lean L258-261) ---
CANDIDATES.append({
    "id": "val_load_mono_on_prefix",
    "source": "Basic.lean",
    "difficulty": "easy",
    "tactic_count": 1,
    "header": """import Mathlib
import OnlineScheduling.Basic

namespace OnlineScheduling

variable (m : ℕ) [NeZero m]

lemma load_mono_on_prefix (alg : OnlineAlgorithm m) (sigma tau : JobSequence)
    (h_nonneg : ∀ p ∈ tau, 0 ≤ p) (i : Fin m) :
    runAlgorithm m alg sigma i ≤ runAlgorithm m alg (sigma ++ tau) i :=""",
    "proof_body": """  runAlgorithm_mono (m := m) alg sigma tau h_nonneg i""",
    "footer": "\nend OnlineScheduling",
    "deletable_blocks": [
        {"lines": """  runAlgorithm_mono (m := m) alg sigma tau h_nonneg i""", "desc": "delegate to runAlgorithm_mono"},
    ],
})

# --- Candidate 6: competitive_implies_bounded (CompetitiveRatio.lean L59-61) ---
CANDIDATES.append({
    "id": "val_competitive_implies_bounded",
    "source": "CompetitiveRatio.lean",
    "difficulty": "easy",
    "tactic_count": 1,
    "header": """import Mathlib
import OnlineScheduling.Basic
import OnlineScheduling.CompetitiveRatio

open OnlineScheduling

lemma competitive_implies_bounded {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (c : ℝ)
    (hc : IsCCompetitive m alg c) (σ : JobSequence) :
    algorithmMakespan m alg σ ≤ c * OPT σ :=""",
    "proof_body": """  hc σ""",
    "footer": "",
    "deletable_blocks": [
        {"lines": """  hc σ""", "desc": "apply hc (definitional)"},
    ],
})

# --- Candidate 7: competitive_ratio_ge_one (CompetitiveRatio.lean L65-102) ---
CANDIDATES.append({
    "id": "val_competitive_ratio_ge_one",
    "source": "CompetitiveRatio.lean",
    "difficulty": "hard",
    "tactic_count": 12,
    "header": """import Mathlib
import OnlineScheduling.Basic
import OnlineScheduling.CompetitiveRatio

open OnlineScheduling

lemma competitive_ratio_ge_one {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (c : ℝ)
    (hc : IsCCompetitive m alg c) : 1 ≤ c := by""",
    "proof_body": """  let sigma : JobSequence := [1]
  let loadsBefore : Loads m := fun _ => 0
  let j : Fin m := alg loadsBefore 1
  have h_run : runAlgorithm m alg sigma = step (m := m) alg loadsBefore 1 := by
    simp [sigma, runAlgorithm, loadsBefore]
  have h_load_j : runAlgorithm m alg sigma j = 1 := by
    rw [h_run]
    simp [step, loadsBefore, j]
  have h_makespan_ge : 1 ≤ algorithmMakespan m alg sigma := by
    dsimp [algorithmMakespan]
    have h := makespan_ge_each (m := m) (runAlgorithm m alg sigma) j
    simpa [h_load_j] using h
  have h_opt_le : OPT sigma ≤ 1 := by
    let optLoads : Loads m := fun i => if i = j then (1 : ℝ) else 0
    have h_total : totalLoad sigma = ∑ i : Fin m, optLoads i := by
      have h_sum : (∑ i : Fin m, optLoads i) = (1 : ℝ) := by
        simp [optLoads]
      simp [sigma, totalLoad, h_sum]
    have h_makespan : makespan m optLoads = (1 : ℝ) := by
      apply le_antisymm
      · dsimp [makespan]
        apply Finset.sup'_le
        intro i _
        by_cases hij : i = j <;> simp [optLoads, hij]
      · have h := makespan_ge_each (m := m) optLoads j
        simpa [optLoads] using h
    have h := opt_le_of_schedule (m := m) sigma optLoads h_total
    simpa [h_makespan] using h
  have h_opt_ge : 1 ≤ OPT sigma := by
    have h_max : maxJobSize sigma = (1 : ℝ) := by
      simp [sigma, maxJobSize]
    have h := opt_ge_max_job sigma
    simpa [h_max] using h
  have h_bound := hc sigma
  have h_opt_eq : OPT sigma = 1 := le_antisymm h_opt_le h_opt_ge
  nlinarith""",
    "footer": "",
    "deletable_blocks": [
        # Block 0: setup
        {"lines": """  let sigma : JobSequence := [1]
  let loadsBefore : Loads m := fun _ => 0
  let j : Fin m := alg loadsBefore 1""", "desc": "setup sigma, loadsBefore, j"},
        # Block 1: h_run
        {"lines": """  have h_run : runAlgorithm m alg sigma = step (m := m) alg loadsBefore 1 := by
    simp [sigma, runAlgorithm, loadsBefore]""", "desc": "h_run via simp"},
        # Block 2: h_load_j
        {"lines": """  have h_load_j : runAlgorithm m alg sigma j = 1 := by
    rw [h_run]
    simp [step, loadsBefore, j]""", "desc": "h_load_j via rw+simp"},
        # Block 3: h_makespan_ge
        {"lines": """  have h_makespan_ge : 1 ≤ algorithmMakespan m alg sigma := by
    dsimp [algorithmMakespan]
    have h := makespan_ge_each (m := m) (runAlgorithm m alg sigma) j
    simpa [h_load_j] using h""", "desc": "h_makespan_ge proof"},
        # Block 4: h_opt_le (complex block)
        {"lines": """  have h_opt_le : OPT sigma ≤ 1 := by
    let optLoads : Loads m := fun i => if i = j then (1 : ℝ) else 0
    have h_total : totalLoad sigma = ∑ i : Fin m, optLoads i := by
      have h_sum : (∑ i : Fin m, optLoads i) = (1 : ℝ) := by
        simp [optLoads]
      simp [sigma, totalLoad, h_sum]
    have h_makespan : makespan m optLoads = (1 : ℝ) := by
      apply le_antisymm
      · dsimp [makespan]
        apply Finset.sup'_le
        intro i _
        by_cases hij : i = j <;> simp [optLoads, hij]
      · have h := makespan_ge_each (m := m) optLoads j
        simpa [optLoads] using h
    have h := opt_le_of_schedule (m := m) sigma optLoads h_total
    simpa [h_makespan] using h""", "desc": "h_opt_le proof (OPT upper bound)"},
        # Block 5: h_opt_ge
        {"lines": """  have h_opt_ge : 1 ≤ OPT sigma := by
    have h_max : maxJobSize sigma = (1 : ℝ) := by
      simp [sigma, maxJobSize]
    have h := opt_ge_max_job sigma
    simpa [h_max] using h""", "desc": "h_opt_ge proof (OPT lower bound)"},
        # Block 6: final deduction
        {"lines": """  have h_bound := hc sigma
  have h_opt_eq : OPT sigma = 1 := le_antisymm h_opt_le h_opt_ge
  nlinarith""", "desc": "final h_bound + h_opt_eq + nlinarith"},
        # Block 7: inner h_makespan sub-proof
        {"lines": """    have h_makespan : makespan m optLoads = (1 : ℝ) := by
      apply le_antisymm
      · dsimp [makespan]
        apply Finset.sup'_le
        intro i _
        by_cases hij : i = j <;> simp [optLoads, hij]
      · have h := makespan_ge_each (m := m) optLoads j
        simpa [optLoads] using h""", "desc": "h_makespan subproof (1 upper bound)"},
    ],
})

# --- Candidate 8: known_sum_opt_bound (Models/KnownSum.lean L29-32) ---
CANDIDATES.append({
    "id": "val_known_sum_opt_bound",
    "source": "Models/KnownSum.lean",
    "difficulty": "easy",
    "tactic_count": 2,
    "header": """import Mathlib
import OnlineScheduling.Basic
import OnlineScheduling.Models.KnownSum

open OnlineScheduling

variable {m : Nat} [NeZero m]

lemma known_sum_opt_bound (inst : KnownSumInstance m) :
    inst.totalSum / (m : ℝ) ≤ OPT inst.jobs :=""",
    "proof_body": """  rw [← inst.h_consistent]
  exact opt_ge_avg_load (m := m) inst.jobs""",
    "footer": "",
    "deletable_blocks": [
        {"lines": "  rw [← inst.h_consistent]", "desc": "rw h_consistent"},
        {"lines": "  exact opt_ge_avg_load (m := m) inst.jobs", "desc": "apply opt_ge_avg_load"},
    ],
})

# ── Gap 生成逻辑 ──────────────────────────────────────────────────

def generate_gaps(candidate, max_gaps_per_theorem=8):
    """
    从一个候选定理生成多个 gap 变体:
    - 单块删除: 每个 deletable block 单独删除
    - 双块删除: 删除两个非重叠 block（随机组合）
    - 保留至少 max_gaps_per_theorem 个变体
    """
    blocks = candidate["deletable_blocks"]
    header = candidate["header"]
    proof_body = candidate["proof_body"]
    footer = candidate["footer"]
    gaps = []

    def remove_block(body, block_lines):
        """从 proof body 中删除指定的行"""
        if block_lines in body:
            # Remove the block and any trailing blank line
            result = body.replace(block_lines, "  sorry")
            return result
        return None

    def build_sample(gap_body, removed_desc, gap_id_suffix):
        """构建一个验证集样本"""
        full_input = header + "\n" + gap_body + "\n" + footer if footer else header + "\n" + gap_body
        full_output = header + "\n" + proof_body + "\n" + footer if footer else header + "\n" + proof_body
        return {
            "id": f"{candidate['id']}_{gap_id_suffix}",
            "source": candidate["source"],
            "difficulty": candidate["difficulty"],
            "removed": removed_desc,
            "instruction": "You are an expert Lean 4 theorem prover specializing in online scheduling theory. Complete the given proof by replacing `sorry` with a correct proof.",
            "input": full_input.strip(),
            "output": full_output.strip(),
            "check_imports": [
                line for line in header.split("\n")
                if line.startswith("import ")
            ],
        }

    # 1. Single block deletions
    for i, block in enumerate(blocks):
        gap_body = remove_block(proof_body, block["lines"])
        if gap_body:
            gaps.append(build_sample(gap_body, block["desc"], f"gap_{i:02d}"))

    # 2. Double block deletions (non-overlapping)
    if len(blocks) >= 2:
        for i in range(len(blocks)):
            for j in range(i + 1, len(blocks)):
                if len(gaps) >= max_gaps_per_theorem:
                    break
                # Check that blocks don't overlap in the source
                if blocks[i]["lines"] in proof_body and blocks[j]["lines"] in proof_body:
                    # Apply both deletions
                    temp = proof_body.replace(blocks[i]["lines"], "  sorry")
                    temp = temp.replace(blocks[j]["lines"], "  sorry")
                    # Only add if we actually replaced two blocks (no overlap)
                    if temp.count("sorry") >= 2:
                        desc = f"{blocks[i]['desc']} + {blocks[j]['desc']}"
                        gaps.append(build_sample(temp, desc, f"gap_{i:02d}_{j:02d}"))
            if len(gaps) >= max_gaps_per_theorem:
                break

    # 3. If not enough, create more by removing non-overlapping sections
    #    of the larger blocks
    if len(gaps) < 3 and candidate["tactic_count"] > 3:
        # For complex proofs, create additional gaps by removing half the proof
        lines = proof_body.strip().split("\n")
        mid = len(lines) // 2
        for split_point in [mid // 2, mid, mid + mid // 2]:
            if split_point >= len(lines):
                continue
            gap_body = "\n".join(lines[:split_point]) + "\n  sorry"
            if gap_body not in [g["input"].split(candidate["id"])[-1] for g in gaps]:
                desc = f"truncate after line {split_point}"
                gaps.append(build_sample(gap_body, desc, f"gap_trunc_{split_point:02d}"))

    return gaps[:max_gaps_per_theorem]


# ── 主流程 ────────────────────────────────────────────────────────

def main():
    all_gaps = []
    stats = []

    for cand in CANDIDATES:
        gaps = generate_gaps(cand, max_gaps_per_theorem=6)
        all_gaps.extend(gaps)
        stats.append({
            "theorem": cand["id"],
            "source": cand["source"],
            "difficulty": cand["difficulty"],
            "num_gaps": len(gaps),
        })

    # Print stats
    print("=" * 60)
    print("Validation Set Generation Report")
    print("=" * 60)
    total = 0
    for s in stats:
        print(f"  {s['theorem']:<40} {s['source']:<25} {s['difficulty']:<8} {s['num_gaps']:>2} gaps")
        total += s["num_gaps"]
    print(f"\n  TOTAL: {total} validation gaps from {len(CANDIDATES)} theorems")
    print()

    # Difficulty distribution
    by_diff = {"easy": 0, "medium": 0, "hard": 0}
    for g in all_gaps:
        by_diff[g["difficulty"]] += 1
    print(f"  Difficulty: easy={by_diff['easy']}, medium={by_diff['medium']}, hard={by_diff['hard']}")

    # Save
    output_path = os.path.join(os.path.dirname(__file__), "validation_gaps.json")
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(all_gaps, f, indent=2, ensure_ascii=False)
    print(f"\n  Saved to: {output_path}")

    # Also save a summary
    summary_path = os.path.join(os.path.dirname(__file__), "validation_summary.json")
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump({
            "total_gaps": len(all_gaps),
            "num_theorems": len(CANDIDATES),
            "by_difficulty": by_diff,
            "theorems": stats,
            "theorem_names": [c["id"] for c in CANDIDATES],
        }, f, indent=2, ensure_ascii=False)
    print(f"  Summary saved to: {summary_path}")


if __name__ == "__main__":
    main()
