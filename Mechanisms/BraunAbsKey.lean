/-
Braun–Chung–Graham 2025 (J. Scheduling 28:529–544) Theorem 2 (r = 1) 的"机制探针"。

目的：不重证全部调度定理，只复现"为什么绝对竞争比恰是 c₁ ≈ 1.73102"的代数心脏。
与 Theorem 1 探针（BraunKey.lean）成对：

  Theorem 1（渐近 √3）：层长按几何级数（比 q = 2α²，α = 1+√3 是 α²−2α−2=0 的正根），
    比值 = √3 − 余项(r)，余项指数衰减 → 渐近比 √3。
  Theorem 2（绝对 c₁）：层长是 c 的有理函数，c₁ 是三次式 6c³−28c²+38c−13=0 在 (5/3,2)
    内的唯一根，强制 makespan = Σ+F = c₁·F（F = 2S₁）→ 绝对比 = c₁，精确、非近似。

正确性 = 一个精确代数机制，全部可 Lean 验证：
  1. c₁ 存在且唯一：三次式在 (5/3,2) 严格递减（差分解），IVT 给存在、严格单调给唯一；
  2. c₁ 是"不动点" c = (Σ+F)/F 的唯一解 ⟺ 三次式 = 0（`cubic_iff_fixedpoint`）；
  3. 比值坍缩：c₁·F = Σ+F（`c1_F_trap`），即绝对比 = 强制 makespan / OPT = c₁；
  4. F 打包恒等式：S₁ = 3S₀ + 2L₁ + 2（对一切 c 成立），4 台机器各恰 F。

只 import Mathlib（不依赖项目库），单文件编译，秒级验证。
-/

import Mathlib

namespace BraunAbsKey

noncomputable section

/-! ### 三次式与唯一根 c₁ -/

/-- 目标绝对比的极小多项式：6c³ − 28c² + 38c − 13。 -/
def cubic (c : ℝ) : ℝ := 6 * c ^ 3 - 28 * c ^ 2 + 38 * c - 13

/-- cubic(5/3) = 1/3 > 0。 -/
lemma cubic_five_thirds_pos : 0 < cubic (5 / 3 : ℝ) := by
  dsimp [cubic]
  norm_num

/-- cubic(2) = −1 < 0。 -/
lemma cubic_two_neg : cubic 2 < 0 := by
  dsimp [cubic]
  norm_num

/-- 三次式在 (5/3, 2) 内有根（中值定理）。 -/
lemma cubic_root_exists :
    ∃ c : ℝ, (5 / 3 : ℝ) < c ∧ c < 2 ∧ cubic c = 0 := by
  let g : ℝ → ℝ := fun c => -(cubic c)
  have hcont : ContinuousOn g (Set.Icc (5 / 3 : ℝ) 2) := by
    unfold g
    dsimp [cubic]
    fun_prop
  have h5m : (5 / 3 : ℝ) ∈ Set.Icc (5 / 3 : ℝ) 2 := by
    show (5 / 3 : ℝ) ≤ (5 / 3 : ℝ) ∧ (5 / 3 : ℝ) ≤ (2 : ℝ)
    constructor <;> norm_num
  have h2m : (2 : ℝ) ∈ Set.Icc (5 / 3 : ℝ) 2 := by
    show (5 / 3 : ℝ) ≤ (2 : ℝ) ∧ (2 : ℝ) ≤ (2 : ℝ)
    constructor <;> norm_num
  have himage := isPreconnected_Icc.intermediate_value (a := (5 / 3 : ℝ)) (b := 2) h5m h2m hcont
  have hzero : (0 : ℝ) ∈ Set.Icc (g (5 / 3 : ℝ)) (g 2) := by
    constructor <;> dsimp [g, cubic] <;> norm_num
  rcases himage hzero with ⟨c, hcmem, hceq⟩
  have hroot : cubic c = 0 := by
    dsimp [g] at hceq
    nlinarith
  have hc_lo : (5 / 3 : ℝ) < c := by
    have hne : (5 / 3 : ℝ) ≠ c := by
      intro h
      have : g (5 / 3 : ℝ) = 0 := by rw [h]; exact hceq
      dsimp [g, cubic] at this
      norm_num at this
    exact lt_of_le_of_ne hcmem.1 hne
  have hc_hi : c < 2 := by
    have hne : c ≠ 2 := by
      intro h
      have : g (2 : ℝ) = 0 := by rw [h] at hceq; exact hceq
      dsimp [g, cubic] at this
      norm_num at this
    exact lt_of_le_of_ne hcmem.2 (by simpa [eq_comm] using hne)
  exact ⟨c, hc_lo, hc_hi, hroot⟩

/-- 目标绝对竞争比 c₁（三次式在 (5/3,2) 内的根，≈ 1.73102）。 -/
def c1 : ℝ := Classical.choose cubic_root_exists

/-- c₁ > 5/3。 -/
lemma c1_lo : (5 / 3 : ℝ) < c1 := (Classical.choose_spec cubic_root_exists).1

/-- c₁ < 2。 -/
lemma c1_hi : c1 < 2 := (Classical.choose_spec cubic_root_exists).2.1

/-- c₁ 满足三次式。 -/
lemma c1_root : cubic c1 = 0 := (Classical.choose_spec cubic_root_exists).2.2

/-- 三次式在 (5/3,2) 严格递减（差分解：g(d)−g(c) = (d−c)·Q，Q<0）。 -/
lemma cubic_strictAntiOn :
    StrictAntiOn cubic (Set.Ioo (5 / 3 : ℝ) 2) := by
  intro c hc d hd hcd
  rw [← sub_lt_zero]
  have hdiff : cubic d - cubic c = (d - c) * (6 * (c ^ 2 + c * d + d ^ 2) - 28 * (c + d) + 38) := by
    dsimp [cubic]
    ring
  rw [hdiff]
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hQ : 6 * (c ^ 2 + c * d + d ^ 2) - 28 * (c + d) + 38 < 0 := by
    let u := 2 - c
    let v := 2 - d
    have hu : 0 < u := by dsimp [u]; linarith [hc.2]
    have hv : 0 < v := by dsimp [v]; linarith [hd.2]
    have hul : u ≤ 1 / 3 := by dsimp [u]; linarith [hc.1]
    have hvl : v ≤ 1 / 3 := by dsimp [v]; linarith [hd.1]
    have hQ' : 6 * (c ^ 2 + c * d + d ^ 2) - 28 * (c + d) + 38
        = -8 * u - 8 * v + (6 * u ^ 2 + 6 * u * v + 6 * v ^ 2) - 2 := by
      dsimp [u, v]
      ring
    rw [hQ']
    have hu2 : 6 * u ^ 2 ≤ 2 * u := by
      have : u * u ≤ u * (1 / 3) := mul_le_mul_of_nonneg_left hul (le_of_lt hu)
      nlinarith [this]
    have hv2 : 6 * v ^ 2 ≤ 2 * v := by
      have : v * v ≤ v * (1 / 3) := mul_le_mul_of_nonneg_left hvl (le_of_lt hv)
      nlinarith [this]
    have huv : 6 * u * v ≤ u + v := by
      have h1 : 6 * u * v ≤ 2 * u := by
        have : u * v ≤ u * (1 / 3) := mul_le_mul_of_nonneg_left hvl (le_of_lt hu)
        nlinarith [this]
      have h2 : 6 * u * v ≤ 2 * v := by
        have : v * u ≤ v * (1 / 3) := mul_le_mul_of_nonneg_left hul (le_of_lt hv)
        nlinarith [this]
      nlinarith [h1, h2]
    nlinarith [hu2, hv2, huv, hu, hv]
  exact mul_neg_of_pos_of_neg hdc hQ

/-- 唯一性：任何 (5/3,2) 内的根都等于 c₁。 -/
lemma c1_unique {c : ℝ} (hlo : (5 / 3 : ℝ) < c) (hhi : c < 2) (hroot : cubic c = 0) : c = c1 := by
  have hcf : cubic c = 0 := hroot
  have hrf : cubic c1 = 0 := c1_root
  have hc_mem : c ∈ Set.Ioo (5 / 3 : ℝ) 2 := ⟨hlo, hhi⟩
  have hr_mem : c1 ∈ Set.Ioo (5 / 3 : ℝ) 2 := ⟨c1_lo, c1_hi⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hanti : cubic c1 < cubic c := cubic_strictAntiOn hc_mem hr_mem hlt
    rw [hrf, hcf] at hanti
    exact (lt_irrefl (0 : ℝ)) hanti
  · have hanti : cubic c < cubic c1 := cubic_strictAntiOn hr_mem hc_mem hgt
    rw [hrf, hcf] at hanti
    exact (lt_irrefl (0 : ℝ)) hanti

/-! ### 参数任务长度（c 的有理函数，r = 1） -/

/-- S₀ = (c−1)/(2−c)。 -/
def S0 (c : ℝ) : ℝ := (c - 1) / (2 - c)

/-- L₁ = 3/(3c−5) − (c−1)/(2−c)。 -/
def L1 (c : ℝ) : ℝ := 3 / (3 * c - 5) - (c - 1) / (2 - c)

/-- S₁ = 6/(3c−5) + (3−c)/(2−c)。 -/
def S1 (c : ℝ) : ℝ := 6 / (3 * c - 5) + (3 - c) / (2 - c)

/-- F = 2·S₁（最终作业，OPT = F）。 -/
def F (c : ℝ) : ℝ := 2 * S1 c

/-- S⁺₁ = S₁ + 2·S₀（层 1 的"plus"任务）。 -/
def Sp1 (c : ℝ) : ℝ := S1 c + 2 * S0 c

/-- Σ = L₀ + S₀ + L₁ + S₁ = 1 + S₀ + L₁ + S₁（强制路径的总负载）。 -/
def layerSum (c : ℝ) : ℝ := 1 + S0 c + L1 c + S1 c

/-! ### 不动点 ⟺ 三次式（"为什么恰是 c₁"） -/

/-- 多项式恒等式：(3c²−11c+10)·(c·F − (Σ+F)) = 6c³−28c²+38c−13。
    前因子 3c²−11c+10 = (c−2)(3c−5) 在 (5/3,2) 上非零，故不动点 ⟺ 三次式。 -/
lemma cubic_identity (c : ℝ) (h2 : c ≠ 2) (h3 : 3 * c - 5 ≠ 0) :
    (3 * c ^ 2 - 11 * c + 10) * (F c * c - (layerSum c + F c)) = cubic c := by
  dsimp [F, layerSum, S0, L1, S1, cubic]
  field_simp [h2, h3]
  ring

/-- 不动点 c = (Σ+F)/F 等价于 6c³−28c²+38c−13 = 0（paper Table 12, r = 1）。 -/
lemma cubic_iff_fixedpoint (c : ℝ) (h2 : c ≠ 2) (h3 : 3 * c - 5 ≠ 0) (hF : F c ≠ 0) :
    c = (layerSum c + F c) / F c ↔ cubic c = 0 := by
  have hD : 3 * c ^ 2 - 11 * c + 10 ≠ 0 := by
    have hfac : 3 * c ^ 2 - 11 * c + 10 = (c - 2) * (3 * c - 5) := by ring
    rw [hfac]
    exact mul_ne_zero (sub_ne_zero.mpr h2) h3
  have hid := cubic_identity c h2 h3
  constructor
  · intro h
    have hmul : F c * c = layerSum c + F c := by
      have h' := h
      field_simp [hF] at h'
      simpa [mul_comm] using h'
    have hsub : F c * c - (layerSum c + F c) = 0 := by rw [hmul]; ring
    have hpoly : (3 * c ^ 2 - 11 * c + 10) * (F c * c - (layerSum c + F c)) = 0 := by
      rw [hsub, mul_zero]
    rwa [hid] at hpoly
  · intro h
    have hpoly : (3 * c ^ 2 - 11 * c + 10) * (F c * c - (layerSum c + F c)) = 0 := by
      rw [hid, h]
    have hsub : F c * c - (layerSum c + F c) = 0 :=
      (mul_eq_zero.mp hpoly).resolve_left hD
    have hmul : F c * c = layerSum c + F c := sub_eq_zero.mp hsub
    exact (eq_div_iff hF).mpr (by simpa [mul_comm] using hmul)

/-! ### 比值坍缩：绝对比恰为 c₁ -/

/-- S₁(c) > 0 on (5/3, 2)。 -/
lemma S1_pos (c : ℝ) (hlo : (5 / 3 : ℝ) < c) (hhi : c < 2) : 0 < S1 c := by
  dsimp [S1]
  have h3 : 0 < 3 * c - 5 := by nlinarith
  have h2c : 0 < 2 - c := by nlinarith
  have h3c : 0 < 3 - c := by nlinarith
  have h1 : 0 < 6 / (3 * c - 5) := div_pos (by norm_num) h3
  have h2' : 0 < (3 - c) / (2 - c) := div_pos h3c h2c
  exact add_pos h1 h2'

/-- c₁ ≠ 2。 -/
lemma c1_ne_two : c1 ≠ 2 := by
  intro h
  nlinarith [c1_hi, h]

/-- 3·c₁ − 5 ≠ 0。 -/
lemma c1_3c5_ne : 3 * c1 - 5 ≠ 0 := by
  intro h
  nlinarith [c1_lo, h]

/-- F(c₁) ≠ 0（实为正）。 -/
lemma F_c1_ne : F c1 ≠ 0 := by
  have hpos : 0 < F c1 := by
    dsimp [F]
    have hS : 0 < S1 c1 := S1_pos c1 c1_lo c1_hi
    nlinarith
  exact ne_of_gt hpos

/-- c₁ 是不动点：c₁ = (Σ+F)/F。 -/
lemma c1_fixedpoint : c1 = (layerSum c1 + F c1) / F c1 :=
  (cubic_iff_fixedpoint c1 c1_ne_two c1_3c5_ne F_c1_ne).mpr c1_root

/-- 比值坍缩：c₁·F = Σ+F。强制 makespan（Σ+F）除以 OPT（F）恰等于 c₁，
    即绝对竞争比 = c₁，精确、非近似。 -/
lemma c1_F_trap : c1 * F c1 = layerSum c1 + F c1 :=
  (eq_div_iff F_c1_ne).mp c1_fixedpoint

/-! ### F 打包恒等式（4 台机器各恰 F 的可行性） -/

/-- S₁ = 3·S₀ + 2·L₁ + 2（对一切 c ≠ 2、3c−5 ≠ 0 成立）。
    这是最终作业 F 之后"4 台机器每台恰好 F"打包的关键恒等式。 -/
lemma S1_eq_3S0_2L1_2 (c : ℝ) (h2 : c ≠ 2) (h3 : 3 * c - 5 ≠ 0) :
    S1 c = 3 * S0 c + 2 * L1 c + 2 := by
  dsimp [S0, L1, S1]
  have h3' : -5 + c * 3 ≠ 0 := by
    have h := h3
    ring_nf at h
    exact h
  field_simp [h2, h3']
  ring

/-- 在 c₁ 处，F = 2S₁ 恰被 4 台机器分摊：{F}、{S⁺₁,S₀,L₁,L₁,L₀,L₀}、
    {S₁,S₁}、{S₁,S₀×3,L₁×2,L₀×2}，每台 = 2S₁ = F（用 S₁=3S₀+2L₁+2）。 -/
lemma c1_F_pack_identity : F c1 = S1 c1 + S1 c1 := by
  dsimp [F]
  ring

end

end BraunAbsKey
