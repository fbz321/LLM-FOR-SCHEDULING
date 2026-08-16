/-
Faigle–Kern–Turán (1989) m ≥ 4 下界 1+√2/2 ≈ 1.707 的"机制探针"。

目的：不重证全部调度定理，只复现"为什么比值恰是 1+√2/2"的代数心脏。
与 Braun/Rudin 探针同构——"魔法常数由极小多项式锁定 → 碰撞比精确坍缩"：

  Braun Thm1: α = 1+√3（α²−2α−2=0），比值 → √3
  Braun Thm2: c₁（6c³−28c²+38c−13=0），绝对比 = c₁
  Rudin m=4:  V = √3−1（V²+2V−2=0），比值 = 1+V = √3−ε
  FKT  m≥4:   fkt = 1+√2/2（2x²−4x+1=0 的唯一根 > 1），比值 = fkt

FKT 构造（3 阶段，全部作业归一化）：
  1. m 个作业，尺寸 a = √2/2 − 1/2；
  2. m 个作业，尺寸 b = 1/2；若某机 ≥ a+2b → 碰撞比 = (a+2b)/(a+b) = fkt；
     否则全机负载 = a+b = √2/2 → 继续；
  3. 终作业 1 → makespan ≥ √2/2 + 1，OPT ≤ √2/2 + 1/m，比 ≥ fkt（m ≥ 4）。

正确性 = 精确代数机制：
  1. fkt = 1+√2/2 是 2x²−4x+1=0 的唯一根 > 1（另一根 1−√2/2 < 1）；
  2. 尺寸 a、b 使 a+b = √2/2，且碰撞比 (a+2b)/(a+b) = 1+1/√2 = fkt（精确）；
  3. 均匀路径比 (√2/2+1)/(√2/2+1/4) ≥ fkt（m=4 最紧）。

只 import Mathlib，单文件编译，秒级验证。
-/

import Mathlib

namespace FKTKey

noncomputable section

/-! ### 魔法常数 fkt = 1 + √2/2 -/

/-- FKT 目标比：1 + √2/2 ≈ 1.707。 -/
def fkt : ℝ := 1 + Real.sqrt 2 / 2

/-- fkt 的极小多项式：2·fkt² − 4·fkt + 1 = 0。 -/
lemma fkt_poly : 2 * fkt ^ 2 - 4 * fkt + 1 = 0 := by
  dsimp [fkt]
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- fkt > 1。 -/
lemma fkt_gt_one : 1 < fkt := by
  dsimp [fkt]
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- 唯一性：2x²−4x+1=0 且 x>1 的实根恰为 fkt=1+√2/2
    （另一根 1−√2/2 < 1 被排除）。"为什么比值只能是 1+√2/2"。 -/
lemma fkt_unique (x : ℝ) (hx : 2 * x ^ 2 - 4 * x + 1 = 0) (hgt : 1 < x) : x = fkt := by
  have hfac : 2 * (x - (1 + Real.sqrt 2 / 2)) * (x - (1 - Real.sqrt 2 / 2)) = 0 := by
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hprod : (x - (1 + Real.sqrt 2 / 2)) * (x - (1 - Real.sqrt 2 / 2)) = 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using hfac)).resolve_left h2
  have hpos2 : 0 < x - (1 - Real.sqrt 2 / 2) := by
    have h1 : (1 - Real.sqrt 2 / 2) < 1 := by
      have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      linarith
    linarith
  have hx_eq : x - (1 + Real.sqrt 2 / 2) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hpos2)
  dsimp [fkt]
  linarith

/-- fkt = 1 + 1/√2（因为 1/√2 = √2/2）。 -/
lemma fkt_eq_one_add_one_div_sqrt2 : fkt = 1 + 1 / Real.sqrt 2 := by
  have h : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [fkt]
  field_simp [h]
  nlinarith [hs]

/-! ### 尺寸 a、b 与碰撞坍缩 -/

/-- a = √2/2 − 1/2。 -/
def fkt_a : ℝ := Real.sqrt 2 / 2 - 1 / 2

/-- b = 1/2。 -/
def fkt_b : ℝ := 1 / 2

/-- a + b = √2/2（均匀路径的每机负载）。 -/
lemma fkt_a_add_b : fkt_a + fkt_b = Real.sqrt 2 / 2 := by
  dsimp [fkt_a, fkt_b]
  ring

/-- 碰撞坍缩：(a+2b)/(a+b) = 1+1/√2 = fkt。
    即某机收到 2 个 b（负载 a+2b）时，与 OPT = a+b 之比恰 = fkt。 -/
lemma fkt_collision_ratio : (fkt_a + 2 * fkt_b) / (fkt_a + fkt_b) = fkt := by
  rw [fkt_a_add_b]
  have h_add : fkt_a + 2 * fkt_b = Real.sqrt 2 / 2 + 1 / 2 := by
    dsimp [fkt_a, fkt_b]
    ring
  rw [h_add]
  have h_ne : Real.sqrt 2 / 2 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [fkt]
  field_simp [h_ne]
  nlinarith [hsq]

/-! ### 均匀路径（终作业）坍缩 -/

/-- 均匀路径比 ≥ fkt（m=4 最紧）：fkt·(√2/2 + 1/4) ≤ √2/2 + 1。
    即 makespan ≥ √2/2+1，OPT ≤ √2/2+1/4，比 = makespan/OPT ≥ fkt。 -/
lemma fkt_final_ratio : fkt * (Real.sqrt 2 / 2 + 1 / 4) ≤ Real.sqrt 2 / 2 + 1 := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt2_le_2 : Real.sqrt 2 ≤ 2 := by
    have hlt : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
      norm_num
    exact le_of_lt hlt
  dsimp [fkt]
  nlinarith [hsq, hsqrt2_le_2]

end

end FKTKey
