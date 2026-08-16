/-
Tan–Li (2015) 伪下界（pseudo lower bound）构造的"机制探针"。

目的：不重证全部调度定理，只复现"为什么比值是 1+γ_m、γ_m 被 α 封顶"的代数心脏。
与 Braun/Rudin/FKT 探针同构——"魔法常数由极小多项式锁定"：

  Braun Thm1: α = 1+√3（α²−2α−2=0），比值 → √3
  Braun Thm2: c₁（6c³−28c²+38c−13=0），绝对比 = c₁
  Rudin m=4:  V = √3−1（V²+2V−2=0），比值 = 1+V = √3−ε
  FKT  m≥4:   fkt = 1+√2/2（2x²−4x+1=0），比值 = fkt
  TanLi m≥4:  α = (3+√57)/12（6x²−3x−2=0，即 x(x−1/2)=1/3），比值 = 1+γ_m

Tan–Li 构造（5 阶段自适应 adversary）的"魔法常数"：
  α = (3+√57)/12 是 x(x−1/2)=1/3（⟺ 6x²−3x−2=0）的唯一正根。
  构造的比值是 1+γ_m，其中 γ_m = min(β_m, α)（β_m 由 f_i/g_i/x_i 递推决定，
  超出本探针范围），所以 α 是 γ_m 的**上限**——这就是"为什么 α 这么选"：
  α 精确封顶了 5 阶段 adversary 能推到的 γ。

正确性 = 精确代数机制：
  1. α = (3+√57)/12 是 6x²−3x−2=0 的唯一正根（另一根 (3−√57)/12 < 0）；
  2. 等价地 α(α−1/2) = 1/3（tanAlpha_sq），这是论文里的原始形式；
  3. α ∈ (0, 1)（可行性）；γ_m = min(β_m, α) ≤ α，比值 1+γ_m ≤ 1+α。

只 import Mathlib，单文件编译，秒级验证。
-/

import Mathlib

namespace TanLiKey

noncomputable section

/-! ### 魔法常数 α = (3 + √57)/12 -/

/-- Tan–Li 伪下界的魔法常数：α = (3+√57)/12 ≈ 0.879。 -/
def tanAlpha : ℝ := (3 + Real.sqrt 57) / 12

/-- 极小多项式（原始形式）：α(α − 1/2) = 1/3。 -/
lemma tanAlpha_sq : tanAlpha * (tanAlpha - 1 / 2) = 1 / 3 := by
  dsimp [tanAlpha]
  have hsq : (Real.sqrt 57) ^ 2 = 57 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 57)
  nlinarith

/-- 极小多项式（多项式形式）：6α² − 3α − 2 = 0。 -/
lemma tanAlpha_poly : 6 * tanAlpha ^ 2 - 3 * tanAlpha - 2 = 0 := by
  nlinarith [tanAlpha_sq]

/-- α > 0。 -/
lemma tanAlpha_pos : 0 < tanAlpha := by
  dsimp [tanAlpha]
  have h : 0 < Real.sqrt 57 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 57)
  nlinarith

/-- α ≤ 1（即 √57 ≤ 9）。 -/
lemma tanAlpha_le_one : tanAlpha ≤ 1 := by
  have hlt : Real.sqrt 57 < 9 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 9)]
    norm_num
  dsimp [tanAlpha]
  nlinarith [hlt]

/-- 唯一性：6x²−3x−2=0 且 x>0 的实根恰为 α=(3+√57)/12
    （另一根 (3−√57)/12 < 0 被排除）。"为什么 α 只能是 (3+√57)/12"。 -/
lemma tanAlpha_unique (x : ℝ) (hx : 6 * x ^ 2 - 3 * x - 2 = 0) (hpos : 0 < x) : x = tanAlpha := by
  have hfac : 6 * (x - (3 + Real.sqrt 57) / 12) * (x - (3 - Real.sqrt 57) / 12) = 0 := by
    have hsq : (Real.sqrt 57) ^ 2 = 57 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 57)
    nlinarith
  have hprod : (x - (3 + Real.sqrt 57) / 12) * (x - (3 - Real.sqrt 57) / 12) = 0 := by
    have h6 : (6 : ℝ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using hfac)).resolve_left h6
  have hpos2 : 0 < x - (3 - Real.sqrt 57) / 12 := by
    have hneg : (3 - Real.sqrt 57) / 12 < 0 := by
      have h57 : 7 < Real.sqrt 57 := by
        rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
        norm_num
      have h57' : 3 - Real.sqrt 57 < 0 := by nlinarith [h57]
      exact div_neg_of_neg_of_pos h57' (by norm_num : (0 : ℝ) < 12)
    nlinarith
  have hx_eq : x - (3 + Real.sqrt 57) / 12 = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hpos2)
  dsimp [tanAlpha]
  linarith

/-! ### 坍缩：γ_m = min(β_m, α) ≤ α -/

/-- γ_m = min(β_m, α) ≤ α（γ 被魔法常数 α 封顶，这是"α 这么选"的原因）。 -/
lemma gamma_le_alpha (beta : ℝ) : min beta tanAlpha ≤ tanAlpha := min_le_right beta tanAlpha

/-- 比值 1+γ_m ≤ 1+α（α 精确封顶 5 阶段 adversary 能推到的比值增量）。 -/
lemma one_add_gamma_le (beta : ℝ) : 1 + min beta tanAlpha ≤ 1 + tanAlpha := by
  linarith [min_le_right beta tanAlpha]

end

end TanLiKey
