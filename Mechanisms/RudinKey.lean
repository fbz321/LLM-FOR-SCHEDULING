/-
Rudin (2003, SIAM J. Comput. 32:717-735) m=4 √3 下界的"机制探针"。

目的：不重证全部调度定理，只复现"为什么比值恰是 √3"的代数心脏。
与 Braun 探针（BraunKey.lean / BraunAbsKey.lean）同构——所有经典构造
都是"魔法常数（由极小多项式唯一锁定）+ 比值坍缩"：

  Braun  Theorem 1: α = 1+√3（α²−2α−2=0），比值 = √3 − 余项(r) → 渐近 √3
  Braun  Theorem 2: c₁（6c³−28c²+38c−13=0 唯一根），绝对比 = c₁
  Rudin  m=4:      V = √3−1（V²+2V−2=0），配 M = (3V−2)/2，比值 = 1+V = √3−ε

Rudin 正确性 = 精确代数机制，全部可 Lean 验证：
  1. V = √3−1 是 V²+2V−2=0 的唯一正根（另一根 −√3−1 < 0）→ 1+V = √3；
  2. M = (3V−2)/2 使 A4 碰撞比**恰** = 1+V（`M_add_five_halves`，即
     rudin_A4_eq 的代数心脏）——这就是"为什么 M 这么选"；
  3. 比值递推 f(R) = 3/(4M)+1/2−1/(2MR)，其增量 δ₁ = (2−2V−V²)/(4MV) 在
     V=√3−1 处**恰为 0**（分子 2−2V−V² = −(V²+2V−2) 即极小多项式）——
     极限比 √3 是"精确坍缩"而非近似。

只 import Mathlib，单文件编译，秒级验证。
-/

import Mathlib

namespace RudinKey

noncomputable section

/-! ### 魔法常数 V = √3 − 1 -/

/-- V = √3 − 1（ε=0 的极限；1+V = √3 是目标比）。 -/
def V : ℝ := Real.sqrt 3 - 1

/-- V 的极小多项式：V² + 2V − 2 = 0。 -/
lemma V_poly : V ^ 2 + 2 * V - 2 = 0 := by
  dsimp [V]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- V > 0。 -/
lemma V_pos : 0 < V := by
  dsimp [V]
  have h1 : 1 < Real.sqrt 3 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
  linarith

/-- 比值坍缩：1 + V = √3（这是"为什么恰是 √3"）。 -/
lemma one_add_V : 1 + V = Real.sqrt 3 := by
  dsimp [V]
  ring

/-- 唯一性：满足 x²+2x−2=0 且 x>0 的实根恰为 V=√3−1
    （另一根 −√3−1 < 0 被排除）。"为什么 V 只能是 √3−1"。 -/
lemma V_unique (x : ℝ) (hx : x ^ 2 + 2 * x - 2 = 0) (hpos : 0 < x) : x = V := by
  have hfac : (x - (Real.sqrt 3 - 1)) * (x + (Real.sqrt 3 + 1)) = 0 := by
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hpos2 : 0 < x + (Real.sqrt 3 + 1) := by
    have h1 : 0 < Real.sqrt 3 + 1 := by nlinarith [Real.sqrt_nonneg 3]
    nlinarith [hpos, h1]
  have hx_eq : x - (Real.sqrt 3 - 1) = 0 :=
    (mul_eq_zero.mp hfac).resolve_right (ne_of_gt hpos2)
  dsimp [V]
  linarith

/-! ### 第二常数 M = (3V−2)/2 与 A4 坍缩 -/

/-- M = (3V−2)/2。 -/
def M (V : ℝ) : ℝ := (3 * V - 2) / 2

/-- "为什么 M 这么选"：M + 5/2 = (3/2)(1+V)。
    即 A4（type-2 层第 4 个作业）碰撞 makespan A(M+5/2) 与 OPT (3/2)A 之比
    **恰** = 1+V。这是 rudin_A4_eq 的代数心脏。 -/
lemma M_add_five_halves (V : ℝ) : M V + 5 / 2 = (3 / 2) * (1 + V) := by
  dsimp [M]
  ring

/-- 在 V=√3−1 处，A4 碰撞比恰 = 1+V = √3。 -/
lemma A4_ratio_collapse (A : ℝ) (hA : A ≠ 0) :
    (A * (M V + 5 / 2)) / ((3 / 2) * A) = 1 + V := by
  rw [M_add_five_halves]
  field_simp [hA]

/-! ### 比值递推与收缩 -/

/-- 比值递推：R_{i+1} = f(R_i)，M = (3V−2)/2（type-2 层比例演化）。 -/
def ratioStep (V R : ℝ) : ℝ :=
  let M := (3 * V - 2) / 2
  3 / (4 * M) + 1 / 2 - 1 / (2 * M * R)

/-- 收缩增量：δ₁ = f(V, 1/(2V)) − 1/(2V) = (2−2V−V²)/(4MV)。
    分子 2−2V−V² = −(V²+2V−2) 恰是极小多项式 → 在 V=√3−1 处为 0。 -/
lemma delta_one (V : ℝ) (hV : V ≠ 0) (h3V2 : 3 * V - 2 ≠ 0) :
    ratioStep V (1 / (2 * V)) - 1 / (2 * V) =
      (2 - 2 * V - V ^ 2) / (4 * M V * V) := by
  dsimp [ratioStep, M]
  field_simp [hV, h3V2]
  ring

/-- 3·V − 2 ≠ 0（即 3√3 ≠ 5，因为 √3 > 5/3）。 -/
lemma three_V_ne_two : 3 * V - 2 ≠ 0 := by
  dsimp [V]
  have h : (5 / 3 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ (5 / 3 : ℝ))]
    norm_num
  nlinarith

/-- 在 V=√3−1 处收缩增量为 0：极限比 √3 是精确坍缩（非近似）。 -/
lemma delta_one_vanishes :
    ratioStep V (1 / (2 * V)) - 1 / (2 * V) = 0 := by
  have hV : V ≠ 0 := ne_of_gt V_pos
  have h3V2 : 3 * V - 2 ≠ 0 := three_V_ne_two
  rw [delta_one V hV h3V2]
  have hnum : 2 - 2 * V - V ^ 2 = 0 := by
    nlinarith [V_poly]
  rw [hnum]
  norm_num

end

end RudinKey
