/-
Braun–Chung–Graham 2025 (J. Scheduling 28:529–544) m = 4 构造的"机制探针"。

目的：不重证全部定理，只复现"为什么这个自适应实例正确"的代数心脏——
比值分解：τ_A(F)/τ_o(F) = 1 + α(1+α)/(q−1) − 指数衰减余项，
其中 1 + α(1+α)/(q−1) = √3 由 α 的极小多项式 α²−2α−2=0 保证。

这给出构造正确的完整机制：
  1. 若算法在任何层不"整齐"（把 S⁺_k 放错机器），makespan 立即超过 √3·OPT − (2−√3)；
  2. 唯一逃生路径（每层分散，Table 3）的比值 = √3 − 余项(r)，余项随 r 指数衰减；
  3. 故绝对比 = √3 − ε_r（Theorem 2），加性界 d = 2−√3 吸收余项后渐近比 = √3（Theorem 1）。

只 import Mathlib（不依赖项目库），单文件编译，秒级验证。
-/

import Mathlib

namespace BraunKey

noncomputable section

/-- α = 1 + √3：本构造唯一的"魔法常数"。 -/
def α : ℝ := 1 + Real.sqrt 3

/-- 层间几何比 q = 2α²（严格递增，> 1）。 -/
def q : ℝ := 2 * α ^ 2

lemma α_pos : 0 < α := by
  dsimp [α]; linarith [Real.sqrt_nonneg 3]

lemma α_ne_zero : α ≠ 0 := ne_of_gt α_pos

/-- α 的极小多项式：α² − 2α − 2 = 0（α = 1+√3 ⟺ 该方程，正根唯一）。 -/
lemma α_poly : α ^ 2 - 2 * α - 2 = 0 := by
  dsimp [α]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- 由极小多项式导出的替换式 α² = 2α + 2。 -/
lemma α_sq : α ^ 2 = 2 * α + 2 := by
  nlinarith [α_poly]

lemma q_ne_one : q ≠ 1 := by
  dsimp [q]
  have : 2 < α := by
    dsimp [α]
    have : 1 < Real.sqrt 3 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
    linarith
  have : 2 < α ^ 2 := by
    calc 2 < α * 2 := by linarith
    _ = 2 * α := by ring
    _ ≤ α ^ 2 := by nlinarith [α_sq]
  nlinarith

/-- q−1 ≠ 0（ratio 引理的分母非零条件）。 -/
lemma q_sub_one_ne_zero : q - 1 ≠ 0 := by
  intro h
  exact q_ne_one (by linarith)

/-- 唯一性：满足 x²−2x−2=0 且 x>0 的实根恰为 α=1+√3（另一个根 1−√3<0 被排除）。
    这就是"为什么尺寸比只能是 α"——代数方程唯一确定它。 -/
lemma α_unique (x : ℝ) (hx : x ^ 2 - 2 * x - 2 = 0) (hpos : 0 < x) : x = α := by
  have hfac : (x - (1 + Real.sqrt 3)) * (x - (1 - Real.sqrt 3)) = 0 := by
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hneg : 1 - Real.sqrt 3 ≤ 0 := by
    have : 1 ≤ Real.sqrt 3 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 3)
    linarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · dsimp [α]; linarith
  · exfalso
    have : x = 1 - Real.sqrt 3 := by linarith
    linarith

/-! ### 比值分解（机制核心）

强制 makespan（Table 3，P1 收集所有 L_k、S_k 与 F）：
    τ_A(F) = Σ_{k≤r} (L_k + S_k) + F = (1+α)·Σ_{k≤r} q^k + 2α·q^r
最优 makespan：τ_o(F) = F = 2α·q^r（最大作业界，打包 Table 7）
比值 = 1 + (1+α)·Σq^k / (2α·q^r)
      = 1 + α(1+α)/(q−1) − (1+α)/(2α(q−1)·q^r)     ← 分解
      = √3 − 余项(r)，余项 → 0（q > 1 指数衰减）
-/

/-- 几何部分和 Σ_{k≤r} q^k = (q^{r+1}−1)/(q−1)。 -/
lemma geom_sum (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), q ^ k = (q ^ (r + 1) - 1) / (q - 1) := by
  induction r with
  | zero =>
      simp
      field_simp [q_sub_one_ne_zero]
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [q_sub_one_ne_zero]
      ring

/-- 比值分解：1 + (1+α)·Σq^k / (2α·q^r) = 1 + α(1+α)/(q−1) − 余项(r)。
    余项 = (1+α)/(2α(q−1)·q^r)，随 r 指数衰减。 -/
lemma ratio_decomp (r : ℕ) :
    1 + (1 + α) * (∑ k ∈ Finset.range (r + 1), q ^ k) / (2 * α * q ^ r)
      = 1 + α * (1 + α) / (q - 1) - (1 + α) / (2 * α * (q - 1) * q ^ r) := by
  rw [geom_sum]
  have hq : q - 1 ≠ 0 := q_sub_one_ne_zero
  have hα : α ≠ 0 := α_ne_zero
  have hqpos : 0 < q := by dsimp [q]; nlinarith [α_pos]
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ (ne_of_gt hqpos)
  -- q^{r+1} = q·q^r
  have hsucc : q ^ (r + 1) = q * q ^ r := by
    rw [pow_succ']
  calc
    1 + (1 + α) * ((q ^ (r + 1) - 1) / (q - 1)) / (2 * α * q ^ r)
        = 1 + (1 + α) * (q * q ^ r - 1) / ((q - 1) * (2 * α * q ^ r)) := by
            rw [hsucc]
            field_simp [hq, hα, hqr]
    _ = 1 + ((1 + α) * q / (2 * α * (q - 1))) - (1 + α) / (2 * α * (q - 1) * q ^ r) := by
            field_simp [hq, hα, hqr]
            ring_nf
    _ = 1 + α * (1 + α) / (q - 1) - (1 + α) / (2 * α * (q - 1) * q ^ r) := by
            dsimp [q]
            field_simp [hq, hα]

/-- 极限恒等式：1 + α(1+α)/(q−1) = √3。这是"为什么恰是 √3"——
    α 的极小多项式让系数坍缩。 -/
lemma ratio_limit : 1 + α * (1 + α) / (q - 1) = Real.sqrt 3 := by
  have hq : q - 1 ≠ 0 := q_sub_one_ne_zero
  have hs : Real.sqrt 3 = α - 1 := by dsimp [α]; ring
  rw [hs]
  -- 目标: 1 + α(1+α)/(q−1) = α−1，即 α(1+α)/(q−1) = α−2
  have hmain : α * (1 + α) = (α - 2) * (q - 1) := by
    dsimp [q]
    calc
      α * (1 + α) = α + α ^ 2 := by ring
      _ = 3 * α + 2 := by rw [α_sq]; ring
      _ = (α - 2) * (2 * α ^ 2 - 1) := by
          have hα3 : α ^ 3 = 6 * α + 4 := by
            calc
              α ^ 3 = α * α ^ 2 := by ring
              _ = α * (2 * α + 2) := by rw [α_sq]
              _ = 6 * α + 4 := by
                  rw [show α * (2 * α + 2) = 2 * α ^ 2 + 2 * α by ring]
                  rw [α_sq]
                  ring
          ring_nf
          rw [hα3, α_sq]
          ring
  have hdiv : α * (1 + α) / (q - 1) = α - 2 := by
    rw [div_eq_iff hq]
    linarith
  linarith

/-- 余项非负（单调衰减到 0 的前提）。 -/
lemma remainder_pos (r : ℕ) : 0 ≤ (1 + α) / (2 * α * (q - 1) * q ^ r) := by
  have h1 : 0 ≤ 1 + α := by linarith [α_pos]
  have hq1 : 0 < q - 1 := by
    have hq : 1 < q := by
      dsimp [q]
      have : 2 < α := by
        dsimp [α]
        have : 1 < Real.sqrt 3 := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
        linarith
      have : 4 < α ^ 2 := by
        calc 4 < α * 2 := by linarith
        _ = 2 * α := by ring
        _ ≤ α ^ 2 := by nlinarith [α_sq]
      nlinarith
    linarith
  have hqpos : 0 < q := by
    dsimp [q]
    have : 0 < α ^ 2 := sq_pos_of_ne_zero (ne_of_gt α_pos)
    nlinarith
  have hqpow : 0 < q ^ r := pow_pos hqpos r
  have hden : 0 < 2 * α * (q - 1) * q ^ r := by
    have h2 : 0 < (2 : ℝ) := by norm_num
    have h2a : 0 < 2 * α := mul_pos h2 α_pos
    have h2aq : 0 < 2 * α * (q - 1) := mul_pos h2a hq1
    exact mul_pos h2aq hqpow
  exact div_nonneg h1 (le_of_lt hden)

/-! ### 加性常数 d = 2 − √3（加性界的 slack 来源） -/

/-- 2α(√3−1)/q = 2 − √3：几何级数系数坍缩后留下的精确常数。
    它正是 Theorem 1 的 d。 -/
lemma additive_coeff : 2 * α * (Real.sqrt 3 - 1) / q = 2 - Real.sqrt 3 := by
  have hα : α ≠ 0 := α_ne_zero
  have hs1 : Real.sqrt 3 - 1 = α - 2 := by dsimp [α]; ring
  have hs2 : 2 - Real.sqrt 3 = 3 - α := by dsimp [α]; ring
  rw [hs1, hs2]
  dsimp [q]
  field_simp [hα]
  nlinarith [α_poly]

/-- 加性界核心：对任意 r，强制 makespan = √3·F − (2−√3)（BraunGraham2025.lean
    中 braun_additive_identity 的同一事实，这里用比值分解形式重述）。 -/
lemma forced_makespan_additive (r : ℕ) :
    (1 + α) * (∑ k ∈ Finset.range (r + 1), q ^ k) + 2 * α * q ^ r
      = Real.sqrt 3 * (2 * α * q ^ r) - (2 - Real.sqrt 3) := by
  have hα : α ≠ 0 := α_ne_zero
  have hq : q - 1 ≠ 0 := q_sub_one_ne_zero
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ (by dsimp [q]; nlinarith [α_pos])
  -- 关键一步：比值分解 (ratio_decomp，含 Σ 形式) + 极限恒等式 (ratio_limit)
  have hdecomp := ratio_decomp r
  have hmain : 1 + α * (1 + α) / (q - 1) = Real.sqrt 3 := ratio_limit
  -- 比值 = √3 − 余项(r)
  have hstep : 1 + (1 + α) * (∑ k ∈ Finset.range (r + 1), q ^ k) / (2 * α * q ^ r)
      = Real.sqrt 3 - (1 + α) / (2 * α * (q - 1) * q ^ r) := by
    linarith [hdecomp, hmain]
  -- (1+α)/(q−1) = 2−√3：纯代数，(3−α)(q−1) = 1+α 由 α 极小多项式保证
  have hcoef : (1 + α) / (q - 1) = 2 - Real.sqrt 3 := by
    have hs2 : 2 - Real.sqrt 3 = 3 - α := by dsimp [α]; ring
    rw [hs2]
    have hden : q - 1 ≠ 0 := q_sub_one_ne_zero
    rw [div_eq_iff hden]
    dsimp [q]
    have hp : (3 - α) * (2 * α ^ 2 - 1) - (1 + α) = -2 * (α - 1) * (α ^ 2 - 2 * α - 2) := by
      ring
    rw [α_poly] at hp
    nlinarith
  -- 比值式乘以 2αq^r 即得加性恒等式
  calc
    (1 + α) * (∑ k ∈ Finset.range (r + 1), q ^ k) + 2 * α * q ^ r
        = (2 * α * q ^ r) * (1 + (1 + α) * (∑ k ∈ Finset.range (r + 1), q ^ k) / (2 * α * q ^ r)) := by
            field_simp [hα, hqr]
            ring
    _ = (2 * α * q ^ r) * (Real.sqrt 3 - (1 + α) / (2 * α * (q - 1) * q ^ r)) := by
            rw [hstep]
    _ = Real.sqrt 3 * (2 * α * q ^ r) - (1 + α) / (q - 1) := by
            field_simp [hα, hqr, hq]
    _ = Real.sqrt 3 * (2 * α * q ^ r) - (2 - Real.sqrt 3) := by
            rw [hcoef]

end

end BraunKey
