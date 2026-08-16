# Findings: Braun–Chung–Graham 2025 主定理证明完成（2026-08-15 会话）

# Findings: BraunGraham2025 一般 r 强制归纳完成（2026-08-15 续，RESEARCH_PLAN 0.2b）

## 数学要点（一般 k 陷阱的代数坍缩，供报告用）

- **L_k 陷阱**（k≥2）：√3(S⁺_{k−1}+L_{k−1}+L_k) − d ≤ Φ_{k−1} + 2L_k。
  差 = q^{k−1}·(3/α − 2) ≤ 0，其中 3/α − 2 ≈ −0.902 是**精确常数**：
  两端乘 α 后系数为
  (α−1)(15α+11) − α(3−α)q − 2αq = 3 − 2α，由 α²=2α+2、α³=6α+4、α⁴=16α+12
  逐次降幂（`braun_SpL_pred_add_mul_alpha`：α(S⁺_{k−1}+L_{k−1}+L_k) =
  q^{k−1}(15α+11)；`braun_trap_Lk_coef`）。几何和的常数残差
  −(1+α)/(q−1) 与 +d 精确相消（(1+α)/(q−1) = 3−α = d）。k=2 是最紧层
  （差 ≈ −13.4），之后按 q 增长放宽。
- **S_k 陷阱**（k≥1）：√3(S_k+L_k) − d ≤ Φ_{k−1}+L_k+2S_k 由恒等式
  **(√3−2)S_k + √3·L_k = L_k**（⟺ α²−2α−1 = 1）坍缩为 0 ≤ Φ_{k−1}+(2−√3)，
  对一切 k 平凡成立（比 r=1 版本的 hα2..hα4 证明更简单，统一了 braun_trap_S1）。
- **OPT witness（一般 k）**：
  * L_k 陷阱 witness = prefix(k−1) ++ L_k×4，OPT ≤ S⁺_{k−1}+L_{k−1}+L_k：
    Table-6 打包 prefix（每机 ≤ S⁺_{k−1}+L_{k−1}）+ 对角 L_k。
  * S_k 陷阱 witness = prefix(k−1) ++ L_k×4 ++ S_k×3，OPT ≤ S_k+L_k：
    M3 吞全部 prefix（totalLoad = 3F_{k−1} − (4+6α)/(q−1) ≤ S_k，
    即 6α ≤ 2α³ ⟺ 3 ≤ α²）+ 对角 L_k + {S_k}×3。
- **非均匀不变式**：clean 路径每层结束 ∀i, Φ_k ≤ load_i（P4 高出 2S_{k−1}）。
  L_k 层分离在非均匀基上仍需成立（新引理 `braun_layer_separation_lb`：
  4 作业 4 机，要么某机 ≥ base+2x，要么每机恰 +x——纯计数，不依赖倍数结构）；
  S_k 三作业用 `braun_three_from_lb`（3 机各 +x + 1 机不动）。
- **最终定理**：`braun_asymptotic_lower_bound_general`：∀ r, ∀ alg,
  ∃ σ ≤ σ_r（前缀），√3·OPT(σ) − (2−√3) ≤ makespan。论文 Theorem 1 的
  "固定 σ_r 强制"字面表述对在线算法不成立（可猜 Table 7 打包达到 OPT=F），
  正确的形式化是自适应对抗 + 前缀 witness（r=1 会话已确立）。

## 工程坑（本轮新增，详见 progress.md 本轮条目）

1. 本工具链 `++` 左结合；`rfl` 不展开 semireducible def。
2. `rw [h]` 元变量单次固化 → 嵌套 step 链用 `simp only [h]`。
3. `rw` 副作用目标逆序；`card_insert_of_notMem`（大写 M）拼写。
4. `Nat.sub_add_cancel hk` 从 hk 推断 a（2≤k 会出 k−2+2）。
5. `mul_le_mul_left` 非 Iff → `le_of_mul_le_mul_left`。
6. simp 等式假设当重写规则毁目标 → `rw [if_pos h] + split_ifs`。
7. `subst h : i = m_j` 在分支内不可靠 → 保留 h_j 配 if_pos/if_neg。
8. `fin_cases` 后的 `(fun i => i) ⟨0,⋯⟩` 需 change；`Fin.sum_univ_three`
   对 `Fin (replicate…).length` 域需先 change。
9. pwsh Set-Content BOM 破坏 lean 解析 → WriteAllText + UTF8Encoding($false)。

# Findings: Braun–Chung–Graham 2025 主定理证明完成（2026-08-15 会话）

来源：`papers/_inbox/Braun2025-lower-bounds-four-processors.pdf`（pdftotext 提取，
`tmp/braun2025.txt`）。补完 `OnlineScheduling/LowerBounds/BraunGraham2025.lean`
（0 sorry，入湖，全量 lake build 8722 jobs 通过）。

## 数学要点（本会话推导，供报告用）

- Theorem 1 的 ∃-陈述只需论文的 **r=1 实例**（17 作业）——所有陷阱比率在 r=1 已全部
  ≥ √3 − (2−√3)/OPT：
  * L₀ 陷阱：2·1 vs OPT=1，2 ≥ 2√3−2 ✓
  * S₀ 陷阱：1+2α vs OPT=1+α，比率恰 = √3 ✓
  * L₁ 陷阱：Φ₀+2q vs OPT=Φ₀+q（对角打包 1+α+q），比率 1.800 ✓
  * S₁ 陷阱：Φ₀+q+2αq vs OPT=S₁+L₁=(α+1)q（3 机 {S₁,L₁}、4 机 {L₁,L₀×4,S₀×4}），
    比率 1.781 ✓（代数坍缩：29α+17 ≤ 29α+21）
  * S⁺₁ 陷阱：Φ₁+S⁺₁ = √3(S⁺₁+L₁) − (2−√3) 精确（braun_prefix_additive_identity）
  * F 收尾：Φ₁+F = √3F − (2−√3) 精确（braun_additive_identity）
- 关键代数恒等式（陷阱引理的降幂闭式）：
  * trap_S0：α²+α−4 ≤ 1+2α ⟺ α ≤ 3（α²=2α+2 代入）
  * trap_L1：2α³−α²+α−4 ≤ 1+α+4α² ⟺ 2α ≤ 7（α³=6α+4 代入后 11α+2 ≤ 9α+9）
  * trap_S1：2α⁴−2α²+α−3 ≤ 1+α+2α²+4α³ ⟺ 29α+17 ≤ 29α+21（平凡）
- 一般 r 的逐层强制归纳（论文 n=8r+9 全参数族）只差一步推广：每层用
  "全体机器 ≥ Φ_{k−1}" 下界不变式（非均匀），L_k 陷阱 Φ_{k−1}+2L_k ≥
  √3(S⁺_{k−1}+L_{k−1}+L_k)−d 依赖 Φ_{k−1}/L_k < (1+α)/(q−1) = 2−√3。留作
  RESEARCH_PLAN 0.2b。

## 工程坑（Lean，全部已解决，详见 progress.md 本轮条目）

1. Fin 域 `(replicate 4 x).length` vs `Fin 4` 的 defeq 差异会使
   `Fin.sum_univ_four` 的 rw 静默失败；count 引理的辅助函数域直接写 `Fin 4`。
2. `Real.sqrt` noncomputable → val 里出现 `replicate n (braunL k)` 即断送
   `native_decide`；Fin val 用纯 Nat 算术。native_decide + dsimp 对
   "链式 if 的 filter.card 计数"是最省事的路径。
3. rw 对嵌套 Fin 投影（`a ⟨↑⟨↑i, ⋯⟩, ⋯⟩`）不匹配 → change 规范化 + 显式
   binder 注解（`fun i : Fin 4 =>`）。
4. nlinarith 不做不等式乘法/乘积内替换 → 显式 `mul_le_mul_of_nonneg_right`
   与 `(cS : ℝ) * S = S`。
5. `simp [h] at * ⊢` 语法非法（`at *` 已含目标）；`simp [h, h.symm]` 死循环。
6. 依赖类型假设上的 rw 有 motive 错误 → 先 `have h' : … := by omega`。
7. omega 对 `List.length`/`replicate` 原子失明 → 先 have 长度等式。
8. 上轮遗留：braunLayerBlock_makespan_ge 的 split 结合性、if 卫生、
   nlinarith 非线性、`by simp` 界证明——本次全部重写为可编译版。

---

# Findings: Tan & Li 2015 General Construction

---

# Findings: Rudin m=4 √3 构造的数学缺口与修复（2026-08-06 会话）

来源：`papers/_inbox/Rudin2003-improved-bounds-online-scheduling.pdf`（pypdf 提取，
`tmp/pdfs/rudin_pypdf.txt` 比 pdftotext 干净，能正确显示 `max/min` 与下标）。

## 构造（论文 3.1 节，与我们 Lean 定义一致的部分）

- `S0 = 1, A0 = 1/(2V), B0 = S0−A0−M·A0 = 1/4, R0 = 1/(2V)`
- `Si = M·Ai−1, Ai = (Ai−1 − 2Bi−1)/4, i ≥ 1`；继续时 `Bi = Si − Ai − M·Ai`
- 终止：第一个 `Ri ≥ V` 的 i 记为 n；终止层 `Bn = Sn − An`；
  若 `Ai ≥ Si`（即 rawRn ≥ 1），论文"redefine Ai = Si, Bi = 0"（夹逼）
- 序列 = 层 n..0，每层 B 行 4×Bi + A 行 3×Ai + (Ai + 2Ai+1)（顶层 4×An），最后 2A0

## 数值仿真发现（python 扫描 ε ∈ (0, 1/100)）

- **rawRn > 1 真实存在**：ε≈2e-5 时 n=4、rawR4≈1.0131（窗口约 1.75e-7..3.1e-5 及
  0.0178..0.025 附近，且好坏窗口交错）；rawRn 最大值 ≈ f(V) ≈ 1.183
- **不夹逼**（当前已提交的 Lean 定义）：ε≈2e-5 时 B_n<0（负作业），缺陷算法
  （把 4 个负 B 全放一台机）使最终比率 < 1+V，构造失效
- **夹逼**：B_n=0 有效，但论文原 A4 界（OPT ≤ (3/2)A_{n−1}）在顶层下一层掉到
  1+V 以下（ε=2e-5 时 1.7304）；必须用更紧的 OPT 界

## 修复后的正确论证（统一的分层分离证明）

以下记 i 为当前层，S_{i+1} 为下层最小负载（S_n 为顶层），A_i、B_i 为夹逼后的值，
rawA_{i+1} = (A_i−2B_i)/4 为未夹逼值（A_{i+1} ≤ rawA_{i+1}）。

1. **B 行违规（层 i−1 的 B 行，i=1..n）**
   - i ≤ n−1（即层 ≤ n−2）：论文式：load ≥ S_i + 2B_{i−1}，
     OPT ≤ B_{i−1} + (3/2)A_i（`rudin_opt_le_B_violation` 已证），
     比率 ≥ 2(M+1−4MR_i)/(1−MR_i) > 1+V（用 R_i < V，`rudin_B_ratio_gt` 已证）
   - i = n（层 n−1 的 B 行）：**顶层打包**：OPT ≤ S_n + B_{n−1}
     （2 台 {B_{n−1}, B_n, A_n}=B_{n−1}+S_n，2 台 {B_n+A_n}=S_n），
     比率 ≥ (S_n+2B_{n−1})/(S_n+B_{n−1}) = 1 + b/(M+b)，b = B_{n−1}/A_{n−1}；
     用 b ≥ 1/2 − 2M·rawRn、rawRn ≤ f(V)，最终 1+b/(M+b) ≥ 1+V
     等价于 V(1+2M)... 干净代数（等价于 V ≤ √3−1 ✓）
2. **A 行第 4 作业（big job）违规**：load ≥ S_{i+1}+B_i+2A_i+2A_{i+1}
   - i ≤ n−2：OPT ≤ (3/2)A_i（Lemma 3.3 打包），比率 = 1+V 精确
   - i = n−1（夹逼层）：OPT ≤ A_i+B_i+2A_{i+1}（顶层分裂调度：big+bn 一台，
     A+B+A_n+B_n 三台；需 S_n ≤ B_{n−1} 与 S_n ≤ 2A_n，均可由
     V < 1/(1+2M) 等推出）；比率 ≥ 1+V 无条件成立（d = rawA−A ≥ 0 的代数）
3. **A 行第 2/3 作业违规**：load ≥ S_{i+1}+B_i+2A_i，OPT ≤ A_i+B_i
   （打包：2 台 {A+B}，1 台 {2B}，1 台全部下层 4S_{i+1} ≤ A+B ⟸ 4M ≤ 1）
   比率 = (A(M+2)+B)/(A+B) ≥ 1+V，用 M=(3V−2)/2 化简为恒真
   （等价于 2V·A_{i+1} ≥ 0），**无条件成立，比论文 div_sub_ge 路线更简单**
4. **分裂不变式**：层 i−1 的 B 行+A 行全分散 ⟹ 每台负载 ≥ S_{i−1} ✓
5. **顶层（层 n）基例**：B_n 行违规比率 2（B_n>0）；B_n=0 时无违规但无碍；
   A_n 行两作业同机：load ≥ S_n+A_n = (1+R_n)S_n ≥ (1+V)S_n，
   OPT ≤ S_n（4B_n+4A_n 均分）；全分散 ⟹ 每台 = S_n
6. **Lemma 3.5**：全分散 ⟹ 每台 ≥ S_0，终作业 2A_0：比率 ≥ (S_0+2A_0)/(2A_0) = 1+V；
   OPT(全序列) ≤ 2A_0（Lemma 3.3 三组打包 + 终作业单独一台）

## 对已提交代码的影响

- `rudinStep` 需加夹逼（终止时 A' := min A' S'；继续路径不受影响）
- `rudinA_succ` 变 `min((A−2B)/4, S')`；`rudinA_eq` 变不等式
  `A_i ≥ 2B_i + 4A_{i+1}`（`rudin_packing` 里等号改 ≤，nlinarith 仍能闭合）
- `rudinB_le_half_A`、`rudin_pos_le_n` 小改；终止/δ/数值证明路径（R_i<V 处）
  全部不变（夹逼只在 R≥V 的终止层生效）
- 新增：`rudinB_nonneg`、`rudinR_le_one`（夹逼后平凡）、`rudin_rawR_le_fV`、
  顶层 B 打包、A_i+B_i 打包、A4 顶层打包、`rudin_layer_separation`（运行追踪）
  与主定理

## 坑

- 论文原文 R_i 定义印刷为 `max(1, A_i/S_i)`，与"R_i<V 才继续"矛盾；逻辑上必须是
  min（夹逼）语义。别在论文符号上纠结，按数学自洽的版本走
- 顶层 B 违规的比率界在 ε→0 时**恰好取等** 1+V（b → VM/(1−V)），证明必须用
  精确代数（等价 V ≤ √3−1），不能用粗常数
- A4 界用 Lemma 3.3 的 (3/2)A 在夹逼层会差 (4/3)M(rawRn−1) 而失败；
  必须用更紧的顶层分裂调度界

来源：`papers/_inbox/Tan2015-pseudo-lower-bounds-online-scheduling.pdf`（6 页，已提取到
`%TEMP%/tan2015-extracted.txt`）。以下是通用 m ≥ 4 构造的权威内容。

## 定义（第 2 节）

- `f_i^(m)(x) = ((m−1−x)/m)^i`, i=1..m
- `g_i^(m)(x) = (1/i)[Σ_{j=1..i} f_j(x) − (m−1−mx)]`, i=1..t, t=⌊m/2⌋
- 恒等式 (3): `(i+1)g_{i+1} − i·g_i = f_{i+1}`
- 恒等式 (4): `Σ_{j≤i} f_j = (m/(1+x))·(f_1 − f_{i+1})`（几何级数，1−c=(1+x)/m）
- 恒等式 (5): `g_i = m/((1+x)i)·(x² − f_{i+1})`
- Lemma 2.1: f_i 在 [0,1] 严格减（f_i' = −(i/m)c^{i−1} ∈ [−1,0)）；g_i 严格增
  （g_i' = (1/i)(Σ f_j' + m) ≥ (m−i)/i > 0）
- Lemma 2.2: `g_i(x)=1/2` 在 [5/7, (m+t)/(2m−t)] 有唯一解，记为 `x_i^(m)`
- `I^(m) = {i | f_{i+1}(x_i) ≤ 1/2 ≤ f_i(x_i)}`；Lemma 2.3–2.5 证 `I^(m) ≠ ∅`
- `q_m = min I^(m)`，`β_m = x_{q_m}`，`α = (3+√57)/12 ≈ 0.87915`（x(x−1/2)=1/3 的正根），
  `γ_m = min{β_m, α}`

## 小 m 数值（(8)、(9)、Table 1）

- `g_1(x) = ((m−1)/m)·((m+1)x − (m−1))`，故 `x_1 = (2m²−3m+2)/(2m²−2)`，
  `f_1(x_1) = (2m²−4m+1)/(2(m²−1)) > 1/2`（m ≥ 4）
- m=4,5,6: q=1，γ = 11/15, 37/48, 4/5（与我们已证的三个文件一致）
- Table 1: m=7,8 → q=2；9,10,11 → q=3；12,13,14 → q=4；15,16,17 → q=5；
  18,19 → q=6；20 → q=7；50 → q=17；1000 → q=360
- γ_m = β_m 当 4 ≤ m ≤ 17；m > 17 时 γ_m = α
- β_7 ≈ 0.81585（g_2 是 x 的二次式），β_8 ≈ 0.82921

## Lemma 2.6（adversary 依赖的三条）

- (i) `f_{q+1}(β) ≤ 1/2 ≤ f_q(γ) ≤ f_{q−1}(γ) ≤ ... ≤ f_1(γ) ≤ 1`
- (ii) `γ(γ−1/2) ≤ min{1/3, 1/2−1/m}`（m≥6 用 γ≤α；m=4,5 直接算）
- (iii) `γ − 1/2 + (1/m)[(m−q)/2 + Σ_{j≤q} f_j(γ)] ≤ (m−1)/m`
  （用 g_q(γ) ≤ g_q(β)=1/2 的单调性）

## 5 阶段 adversary（定理 3.1）

- Phase 1: m 个 `a = (1−γ)(γ−1/2)`；碰撞 → makespan ≥ 2a = (1+γ)a·(2/(1+γ)) ≥ (1+γ)LB
  （LB=a）
- Phase 2: m 个 `b = γ(γ−1/2)`；碰撞 → a+2b = (1+γ)(γ−1/2) = (1+γ)LB（LB=γ−1/2）
- Phase 3: m−q 个 `1/2`；碰撞 → γ+1/2；需证 LB ≤ (γ+1/2)/(1+γ)
  - LB1 = γ − q/2m；LB2 = 1/2；LB3 = max{2γ(γ−1/2), 3(1−γ)(γ−1/2)} = 2γ(γ−1/2) ≤ 2/3
  - 注意：q=1 时论文“p_(2m−1)+p_(2m)+p_(2m+1)=3a”写法不严谨（实为 b+2a），但 max 值 2b 不变
- Phase 4: q 个作业 `f_q(γ), ..., f_1(γ)`；第 i 个（大小 f_{q+1−i}(γ)）首次撞上
  Phase 3/4 机器 → makespan ≥ γ + f_{q+1−i}(γ)；LB1 用部分和公式与 (iii)；
  LB2 = f_{q+1−i}(γ)；LB3 分 i<q（沿用 Phase 3 值）与 i=q（= γ(γ−1/2)+1/2 ≤ (m−1)/m）
- 不碰撞 ⇒ Phase 3+4 共 m 个作业各占一台 ⇒ 所有机器负载 ≥ γ
- Phase 5: 1 个 `1` → makespan ≥ γ+1，LB = 1

## 与现有 m=4/5/6 证明的关系

- 现有三个文件是 q=1 特例（Phase 3 = m−1 个 1/2，Phase 4 = 单个 d=f_1(γ)），
  PseudoLB 只用 LB1/LB2（LB3 在这些前缀不占优）
- 通用版本必须含 LB3 定义与上界（论文伪下界定义即“只用三条下界”）

## 技术风险

- Phase 2 的 IVT/严格单调/伯努利型不等式工作量大
- Lemma 2.6(iii) 依赖 g 单调性（→ 需要导数）
- Phase 4/5 的 LB3 需要排序位置论证（List.sort / Multiset）
- Phase 3/4 机级论证需列表级 pairwise distinct（不能逐个枚举机器）

---

# Findings: GoS 5/3 下界（Park-Chang-Lee 2006, ORL 34:692–696）

来源：`papers/_inbox/ParkChang2006-online-semi-online-GoS.pdf`（5 页，sci-hub.ru 获取）。

## 模型

- 两台机器：机器 1（论文“first machine”）只收 g=1 作业；机器 2 收 g=1 和 g=2。
  形式化中机器 0 = first（收全部），机器 1 = second（只收 g=two）。
- 原仓库 `GoSLowerBound.lean` 的主定理 axiom 陈述
  `(alg : OnlineAlgorithm 2) → 三分支析取` **数学上不成立**：
  List Scheduling 在 B1/B2a/B2b 三条序列上都只达到 4/3 < 5/3。
  必须改成 GoS 约束算法模型（`GoSAlgorithm2`：`choose` + `respects`），
  陈述为 `∀ alg : GoSAlgorithm2, ∃ gs, makespan(gs) ≥ (5/3)·OPT(gs)`。

## Lemma 1 的 adversary（已形式化）

| 分支 | 序列 | 条件 | makespan / OPT | 比率 |
|---|---|---|---|---|
| A | [1(g2), 1(g2)] | 两作业同机 | 2 / 1 | 2 |
| B1 | [1,1,1(g2), 3(g1)] | 1,2 分机 且 3→机0 | 5 / 3 | 5/3 |
| B2a | [1,1,1(g2), 3(g2)] | 3→机1 且 4→机1 | 5 / 3 | 5/3 |
| B2b | [1,1,1(g2), 3(g2), 6(g1)] | 3→机1 且 4→机0 | 10 / 6 | 5/3 |

技术要点：分支 A 复用 `Faigle.layer_separation`（m=2, x=1）；
B1/B2a/B2b 的负载用逐步步进引理 `gos_step_load` / `gos_step_load_other`
（避免 simp 把嵌套 gosStep 展开成 lambda 后模式无法匹配 choose 假设的问题）。

---

# Findings: 全库查重（2026-08-06）

## 抽取的通用引理（Basic.lean）

- `makespan_const (c : ℝ) : makespan m (fun _ : Fin m => c) = c`
  （用 mathlib `Finset.sup'_const`，一行）
- `opt_eq_of_const_schedule (σ) (c) (h : totalLoad σ = (m : ℝ) * c) : OPT σ = c`
  （上界：常量调度 `opt_le_of_schedule`；下界：`opt_ge_avg_load` + field_simp）

这两个引理直接消灭了全库约 10 处"makespan 常量 = c + le_antisymm"的重复块
（ClassicOnline ×3、GoSLowerBound ×4、KnownSumLowerBound ×2、KnownSumP3 ×2、
DecreasingLowerBound ×2，其中两处 OPT [1,1]/[1,1,1] 进一步用
`Faigle.opt_of_identical_jobs` 消掉）。

## 未处理的重复

| 重复 | 说明 | 处置 |
|---|---|---|
| `Lemmas.lean` 3 条 axiom vs `Faigle.lean` 同名已证引理 | 遗留层，仅 Template/bottleneck_reflection 引用，不在构建索引 | 保留（删除会破坏实验模板 import） |
| `PseudoLowerBound.lean`(m=4) vs `PseudoLowerBoundM5.lean`(m=5) 私有 `phase3_bound`/`s1..s5_pseudoLB` | m 特化同构证明 | 保留（已被 PseudoLowerBoundGeneral 取代） |
| `opt_two_ones`(ClassicOnline 私有) vs `gos_opt_A`(GoSLowerBound) | 同一事实 OPT [1,1] = 1 | 各自已改用通用引理 |
| BinStretching `h_opt_eq_one` | 非均匀调度（M0=1，其余 1/(m−1)），非常量 | 不适用新引理 |

## 坑

- `variable (m : ℕ)` 在 Basic.lean 是**显式**参数，新引理调用必须写 `(m := m)`
- `Finset.sup'_const` 第一个显式参数是 `H : s.Nonempty`（不是 s）
- 单文件检查用旧 .olean，新增 Basic 引理后必须先 `lake build` 再检查其他文件

---

# Findings: Braun–Chung–Graham 2025 精读（2026-08-08）

来源：`papers/_inbox/Braun2025-lower-bounds-four-processors.pdf`（J. Scheduling 28:529–544，CC-BY）。

## 主定理

- **Theorem 1（渐近+加性）**：∀ 确定性在线算法 A，∃ 长度 n=8r+9（r≥0）的序列 σ 使
  τ_A(σ) ≥ √3·τ_o(σ) − (2−√3)。加性下界构造是本文首创角度。
- **Theorem 2（有限任务数绝对比）**：同型序列使 τ_A(σ) ≥ (√3−ε_r)·τ_o(σ)，
  ε_r 显式列于附录 Table 21/22（按 r 枚举的具体任务长度表）。

## 构造（与 Rudin 不同，不可复用 Rudin.lean 序列机器）

- 2(r+1) 层，每层 m=4 个任务：**L 层**（4 个同长任务）+ **S 层**（3 个同长 + 1 个
  plus 任务 S⁺_k = S_k + 2S_{k−1}），最后终任务 F。层长严格递增（几何级数，比 2α²，
  α 的选择使极限比 = √3）。总任务数 n = 8r+9。
- **Lemma 1**：plus 任务 S⁺_k 处的竞争比 ≤ 同层其他 S_k 处、也 ≤ 前一层 L_k 处
  （OPT 打包 Table 4 + 负载 Table 3 直接比较）——即只需盯 plus 任务与 F。
- 目标：选任务尺寸使任何算法只能产生 Table 3 的"整齐"调度（每层各占一台），
  最后 F 落地时达到 √3 比。

## 重要修正：m=4 上界是 26/15，不是 7/4

- 论文引言明确：m=4 最小上界 **26/15（Chen et al. 1994）**，不是 LS 的 7/4。
  开放间隙 (√3, 26/15] ≈ (1.73205, 1.73333]，宽仅 ≈0.0013。
  这与 adversary-search-workflow.md 的目标区间一致（当时写对了）。

## 形式化路线草案（Phase 0 任务 0.2）

1. 数值仿真先行：按论文 Table 3/4 复现 r=0,1,2 的序列与比率，验证对 √3 的收敛
   （也验证我们没读错 α 的定义——论文排版把 √3 印丢过，需小心）
2. Lean：`braunL`/`braunS`/`braunSPlus`/`braunF` 层长定义（α 参数）→
   `braunSeq r : List ℝ`（8r+9 个）→ 调度追踪（归纳：每层被迫分散）→
   OPT 上界（Table 4 打包，复用 `opt_le_of_schedule`）→ 加性主定理
3. Theorem 2 暂缓：附录是有限枚举表，形式化价值低、工作量大

# Findings: Böhm–Simon 2022 认证架构（2026-08-08）

来源：`papers/_inbox/BohmSimon2022-discovering-certifying-bin-stretching.pdf`（TCS，arXiv:2001.01125）。

## 核心架构（方向 C 的蓝本）

- **下界 = 显式 DAG 证书**：节点 = 在线过程状态（各 bin 负载 + 下一个出现的物品尺寸）；
  边 = 在线算法的可能选择（只保留"合法"选择，即不立即失败的放置）；
  叶 = OPT 打包证明（所有已发物品确实能装进 m 个单位 bin）。
- **认证命题**：DAG 中每条根→叶路径（= 任意算法的任意运行）都到达"坏叶子"
  （stretching factor ≥ c），且叶子的 OPT 打包真实有效 ⇒ 下界成立。
- **Coq 角色**：形式化问题定义（bin stretching ≡ 已知 OPT 的 makespan 调度！）
  + 检查 DAG 的每条边合法、每个叶子打包有效。**这是首次用形式化工具认证在线问题下界**；
  他们顺带认证了历史上所有"声称但未形式证明"的装箱下界。
- 搜索侧：minimax + 若干算法改进（他们的新下界比旧构造复杂几个数量级，纯手写证明不可行——这正是需要机器认证的原因）。

## 对我们的映射（Lean 版）

- 证书类型：`inductive GameTree` 或结构体（状态 : 排序负载向量；标签 : 下一作业；子节点按机器选择分支）
- soundness：`tree.value ≥ ρ` → 对任意 `alg : OnlineAlgorithm m`，沿 alg 的选择走树必达坏叶
  → `∃ σ, makespan ≥ ρ · OPT`（前缀 = 路径上的作业序列）
- OPT 叶子证书：打包 = `Fin m → 子集` 分配 + 每机负载 ≤ c 的算术验证；
  我们的 OPT 枚举器（A1）必须同步输出打包证书，格式与 Lean 侧对齐
- 我们的搜索若找到 m=4 新下界：策略表 → DAG → Lean 认证 → 论文宣称
  "机器发现 + 机器验证"，比 Böhm–Simon（Coq 认证但未形式化调度问题本身）更进一步：
  我们连问题定义、makespan、OPT、竞争比都在 Lean 里。

# Findings: Gabay–Brauner–Kotov 2013 框架（2026-08-08，粗读）

来源：`papers/_inbox/GabayBraunerKotov2013-computing-lower-bounds-semi-online.pdf`（TCS）。

- **主张**：game-theoretic 技术可自动计算**任意**在线/半在线装箱或调度问题的下界
  （论文原话）——支撑我们线 A 的方法论合法性。
- 结果：bin stretching 下界提升到 19/14（m=3）；随机化下界 7/6（LP 方法）。
- 技术核心（待线 A 启动时细读）：把 adversary 搜索化为可计算博弈，
  用迭代法（类 fictitious play）求博弈值，再转成有限策略树。
  与 adversary-search-workflow.md §4 的策略迭代方案同源。

---

# Findings: Braun2025 数值验证 + 形式化启动（2026-08-08 会话）

## 数值仿真（精确 Q(√3) 算术，work/braun_sim.py）

全部按论文定义重建（α = 1+√3，q = 2α²，L_k = q^k，S_k = αq^k，S⁺_k = S_k+2S_{k−1}，
F = 2S_r，序列 = L₀×4,S₀×4,[L_k×4,S_k×3,S⁺_k]_{k=1..r},F；n = 8r+9）。

r = 0..4 全部验证通过：
1. **OPT(σ_r) = F = 2S_r**（穷举 OPT 与闭式精确相等）
2. **加性恒等式精确成立**：强制调度 makespan τ_A = √3·F − (2−√3)，对每个 r 精确
   （不是渐近！）。等价地 τ_A − √3·OPT = −(2−√3) 恒为常数
3. 比率 τ_A/OPT 从下方单调收敛 √3：1.6830, 1.7288, 1.7318, 1.73204, 1.73205
   （即 Theorem 2 的 √3 − ε_r）
4. **前缀 OPT 断言**（归纳步骤需要）：OPT(层 0..k 至 S⁺_k) = S⁺_k + L_k，
   r ≤ 3 全 k 验证通过（对应论文 Table 6）

## 关键代数（已在 Lean 中证明）

- α = 1+√3 满足 α²−2α−2 = 0 与 2α³−5α²−2α+2 = (2α−1)(α²−2α−2) = 0
- (1+α)q = 2α(√3−1)(q−1)（几何级数系数坍缩）
- 2α(√3−1)/q = 2−√3（加性常数的来源）
- 极限比 1 + α(1+α)/(q−1) = √3
- 总工作 = 4ΣL + 6ΣS；4F − 总工作 = (4+6α)/(q−1) ≈ 1.464（与 r 无关的打包松弛）

## 打包结构（形式化 OPT ≤ F 的路线）

- B1 = {F} 独占一机；其余三机装层级 r 的剩余 + 全部低层，递归自相似（Table 7）
- 顶层三机的一种可行分配：{S⁺_r, L_r, L_r}（残差 1/α·q^r）、{S_r, L_r, L_r}
  （残差 (α−2)q^r）、{S_r, S_r}（残差 0）；低层工作 ≈ (1/α+α−2)q^r 精确匹配残差和
- 正式证明需要按层归纳的不变式（各机残差的闭式），是下一步的核心工作

## Lean 进度（BraunGraham2025.lean，仓库根目录，未注册入构建）

已完成并编译通过（0 gap，39 个定义/引理）：
- 参数与多项式恒等式、层尺寸与正性、S⁺_k 闭式
- √3 恒等式三件套、几何级数闭式、序列定义（n = 8r+9 已证）
- `braun_additive_identity`：强制 makespan = √3·F − (2−√3)（精确）
- `braun_opt_ge_F`：F ≤ OPT（最大作业界）
剩余：强制调度归纳（Table 3）、OPT 打包（Table 7）、主定理

---

# Findings: OPT 公理不一致 —— 发现、证明与修复（2026-08-08 会话，重大）

## 发现

**旧 OPT 公理集不一致**（ProbeOPT.lean 已机器证明 `False`，存于仓库根目录）：

1. `opt_le_of_schedule` 只要求 `totalLoad σ = ∑ loads`，不要求 loads 来自真实分配。
   取常向量 `λ _ => totalLoad σ / 4` 即得 **∀σ, OPT σ ≤ totalLoad σ / 4**。
2. 与 `opt_ge_avg_load` 合并：**OPT σ = totalLoad σ / 4**（OPT 坍缩为平均负载）。
3. 与 `opt_ge_max_job` 合并：σ = [1] 时 1 ≤ OPT [1] = 1/4 → **False**。
   更一般：任何含"大于平均负载的作业"的序列都直接矛盾；且 OPT 与 m 无关而
   公理带 m 参数，m=2 与 m=4 的公理组合本身就矛盾。

**后果**：修复前库中所有用旧 OPT 的定理（含全部 12 个下界）在形式上皆空真。
数学内容无误（构造/比率都是对的），问题只在 OPT 的公理化方式。

## 修复（v2 基础，已实现于 Basic.lean）

- `scheduleLoads σ assign`：分配函数诱导的负载向量
- `optMakespan (m) σ`：**具体定义** = 全部分配上的 makespan 最小值
  （分配类型 Fin σ.length → Fin m 是有限集，inf' 是真最小值）
- 四条特征性质全部成为**定理**：
  `optMakespan_le_schedule` / `optMakespan_le_of_schedule`（需给出分配）
  `optMakespan_ge_max_job`（需作业非负）/ `optMakespan_ge_avg` / `optMakespan_nonneg`
- 关键辅助：`sum_scheduleLoads`（任意分配保总负载，用 `Fin.sum_univ_getElem` 桥接
  List.sum 与 Fin 求和）、`getElem_mem_fin`、`maxJobSize_le_of_forall`
- 旧 OPT + 公理保留但加 WARNING 注释（隔离），迁移完成后删除

## 迁移范围（24 个文件，~245 处 OPT，26 处 opt_le_of_schedule 调用点）

| 文件 | OPT 提及 | opt_le_of_schedule |
|---|---|---|
| Rudin.lean | 83 | 13 |
| DecreasingLowerBound | 25 | 4 |
| ClassicOnline | 18 | 1 |
| GoSLowerBound | 17 | 0 |
| Faigle | 13 | 3 |
| 其余 19 个文件 | ≤8 | ≤1 |

迁移模式：`OPT σ` → `optMakespan (m := M) σ`；`opt_le_of_schedule σ loads hsum`
→ 给出显式分配 `a` + 证 `loads = scheduleLoads σ a`；补作业非负侧条件
（各下界构造的作业都非负，现成可用）。
BraunGraham2025.lean 已率先迁移完成（braun_opt_ge_F 用 optMakespan）。

## 环境事故记录（同会话）

- shell 命令超时后 python 进程不会死：braun_witness.py 孤儿进程 memo 爆到 10.6GB，
  耗尽内存导致 lean 随机 "failed to read file"（每次不同文件、文件本身完好）。
  杀进程后恢复。教训：超时后检查孤儿 python；编译失败先查 FreePhysicalMemory。
- G: 盘偶发位翻转（读到 CoalgCa| 而非 CoalgCat，重试即消失）——留意磁盘健康。

---

# Findings: pattern_opt k=3 搜索的工程坑（2026-08-14 会话）

## scipy differential_evolution 的 workers 坑

- `workers>1` 时 scipy **禁用 callback**（progress callback 不触发），且会覆盖
  `updating='immediate'` 为 `'deferred'`（只打一条 warning，k3_run.log 即此）。
  后果：每代进度不打印，后台被杀后**零留档**。
  对策：进度改写到文件（`_log_eval` → evals.log，含 PID/序号/尺寸/值），
  与 workers 模式解耦；`--target` 可达性封顶（≥√3 提前剪枝）可大幅加速。

## python 命令被 WindowsApps stub 抢占（exit 9009）

- 某时刻起 `python` 解析到 `C:\Users\piggy\AppData\Local\Microsoft\WindowsApps\python.exe`
  （商店占位 stub），任何 `python ...` 静默失败（exit 1/9009，无输出），
  尽管 `D:\Anaconda3` 在 PATH 里。原因：PATH 顺序漂移 / App Execution Alias。
  对策：一律用绝对路径 `D:\Anaconda3\python.exe` 调用；`(Get-Command python).Source`
  先验证再跑长任务。

## k=3 搜索规模与预算（实测）

- k=3（4 尺寸 × 深度 13，scale=1000）单次 eval **60–100s**（k=2 只要 1s）。
- DE 默认 popsize 8 × 15 代 = 480 eval ≈ 单线程 13h+；用
  `--maxiter 10 --popsize 6 --workers 4`（≈240 eval ≈ 2–3h）。
- `--no-polish`：Nelder-Mead 精修每步也是一次完整 eval，k=3 太贵，候选出现后再手动精修。
- 首批（10:45 起）最高 v=1.7014（x=[1.43,0.448,0.723,0.307]），低于 √3≈1.73206。

## 内存爆炸根因与修复（本次会话，重要）

**现象**：`--workers 8` 跑 k=3 时 16GB 内存被打爆，python 进程被系统杀掉，
evals.log 只留 13 行（首个 eval 写日志后约 3 分钟内全灭）。

**根因分析**：
1. `m4_search.py` 的 `opt`（模块级）与 `AdversarySearch.value`（实例级）缓存
   都是 `maxsize=None`。`opt` 是全局的、**跨 eval 累积不释放**——8 个 worker
   进程各持一份无限增长的 opt 缓存，是主要元凶。
2. 单 eval 的 value 缓存可达数十万状态（深度 13 全树），实例随 GC 释放，
   但 DE 密集调用时 GC 不及时，峰值叠加。

**修复**（三管齐下，实测 97.5s/次 速度不变）：
- `opt` 上限 200k（LRU 淘汰，只影响速度不影响正确性）
- `value` **保持 maxsize=None** + `eval_free` 末尾显式 `search.value.cache_clear()`
  （**不要**给 value 设上限：实测 200k 上限把单 eval 从 100s 拖到 >600s，
  热点状态被 LRU 反复淘汰重算）
- 并发 workers 8 → 4（4×~800MB 峰值 ≈ 3.2GB，16GB 机器可用内存稳定在 5GB+）

**教训**：给 memo 缓存设上限前先区分"跨调用累积的全局缓存"（必须限）与
"单次调用生命周期内的实例缓存"（不该限，靠显式清理释放）；并发数要按
"单 worker 峰值 × 并发" 估算内存预算。

---

# 架构记录：LLM 模板生成 → 数值优化 → Lean 认证的对抗下界管线（2026-08-14）

> 来源：k=3 搜索负结果（1.702 < √3）+ Braun2025 精读后的设计讨论。
> 这是方向 C 的升级版（RESEARCH_PLAN.md 已同步）。

## 动机（为什么自由搜索不够）

1. **k=3 实测**：4 尺寸 × 深度 13 的自由搜索最优 1.7020，低于 FKT 1.707，
   更低于 √3≈1.732。DE 陷在"类 FKT 两层"（4 小+3 中+1 大）的平滑局部最优。
2. **经典结构的正确性来自精确代数关系**：Rudin 的 V=√3−1−ε 与 M=(3V−2)/2、
   Braun 的 α=1+√3 让 F 层代数坍缩——这些是"结构约束 + 尺寸精确匹配"的结果，
   不是自由搜索能随机撞到的点。
3. **规模硬墙**：Rudin √3 要 33 作业、10+ 尺寸；k=3 已需 2.7h（≈420 eval），
   k=4（5 尺寸 × 17 深）指数爆炸，纯自由搜索不可行。

## 核心设计：证明成本只付一次，模板降级为数据

逐模板写 Lean 证明不可行（Rudin 一个构造就 3700+ 行；100 个模板 = 100 个 Rudin）。
正确架构 = 三层：

```
┌─ 模板层（AI + 数值）─────────────────────────────────┐
│  LLM 生成候选模板（层模式：类型序列/作业数/尺寸递推）     │
│  → 固定结构，只优化 2-5 个自由尺寸参数（DE+minimax）     │
│  → 粗筛→精筛→尺寸有理化→独立 checker 验证              │
├─ 验证层（一次性 Lean 定理）────────────────────────────┤
│  GameTree（节点=负载+标签，边=算法选择，叶=打包证书）     │
│  soundness: value(tree)≥ρ → ∀alg, ∃σ, ratio alg σ ≥ρ  │
│  ← 只证一次；Böhm–Simon 2022 Coq 同招                  │
├─ 实例层（每个模板 = 数据）──────────────────────────────┤
│  幸存模板 → GameTree 结构体（尺寸参数填入）              │
│  Lean checker 机械验证边合法/叶打包有效 → 零新证明       │
└──────────────────────────────────────────────────────┘
```

## 分环节评估

- **① AI 提模板（最可行）**：LLM 擅长组合已知结构。种子 = FKT（双层）、
  Rudin（type-1/2 交替+夹逼）、Tan-Li（5 阶段）、Braun（L/S 交替+几何级数）。
  90% 产出无效没关系——模板池 + 自动粗筛正好消化。对应 adversary-search-workflow
  §6"LLM 分析策略状态表→提出参数族"，提前到模板层。
- **② 数值优化（可行，比 k=3 更聪明）**：固定层模式后参数降到 2-5 个
  （Braun 模板就 α、q 两个），搜索快几个数量级。顺便用 Braun/Rudin 结构
  做种子复现 √3，验证管线正确性（A2 冒烟测试的修正版——之前漏做了）。
- **③ Lean 验证（瓶颈，解法清晰）**：
  - soundness 定理是核心数学工作但只做一次，与方向 C 完全重合
  - OPT 打包证书：`m4_search.opt()` 改为输出打包（每机作业清单），
    直接喂 Lean 验证 `OPT ≤ c`——`scheduleLoads`/`optMakespan_le_of_schedule`
    已是现成基础设施
  - makespan 下界：GameTree 每条路径 = 一种算法行为，叶 makespan 显式可算，
    验证是机械算术

## 现实产出预期（重要：不指望突破 √3）

- **别指望 AI 搜出 >√3**：开放 20+ 年的问题，概率极低。
- **真实价值 = 方法论原创**："LLM 生成模板 → 精确数值优化 → Lean 认证下界"
  的完整闭环，全球无人做出（Pacut 还在设计阶段，我们领先）。
  Böhm–Simon 做到"Coq 认证下界"但没做到"自动发现+自动认证"——
  我们用 LLM 补上发现端，比他们进一步。
- **规模化复现**：管线批量复现/交叉验证 FKT、Rudin √3、Tan-Li 1+γ_m、
  Braun 加性界等所有已知下界 → 本身就是 B 线论文的案例章。
- k=3 的 1.702 负结果 + 完整复现经典构造 = 方法论文骨架。

## 与现有工作的关系

- RESEARCH_PLAN：方向 C 升级为 C0-C4（见该文件）；线 A 从"自由搜索"
  转向"模板约束搜索"；A2 冒烟测试重定义为"种子复现 √3"。
- 待办（按序）：
  1. pattern_opt 加 `--seed-structure`（rudin/braun/fkt）固定层模式只优化尺寸
  2. 用 Braun 参数 (α, q) 复现 √3，验证工具链
  3. `m4_search.opt()` 输出打包证书
  4. Lean GameTree + soundness（C1/C2）
  5. 模板池 + 粗筛管线（C0）

---

# 机制探针：为什么 Braun2025 自适应实例是正确的（2026-08-14，Lean 复现）

> `OnlineScheduling/BraunKey.lean`（独立探针，只 import Mathlib，24s 单文件编译通过，
> 不依赖项目库、不触发全库构建）。这是对用户提问"为什么 AI 能提模板、
> 为什么 2025 的自适应实例是正确的"的 Lean 侧回答。

## 探针复现了什么

Braun2025 构造的正确性 = 一个精确的**代数机制**，全部可 Lean 验证：

### 1. α = 1+√3 是唯一的（`α_unique`）

极小多项式 α² − 2α − 2 = 0 在正实数上**唯一解** = 1+√3（另一根 1−√3 < 0）。
→ "为什么尺寸比只能是 α"：任何其他尺寸比都会破坏后面的比值坍缩。
**这正是"为什么 AI 模板必须含精确代数关系"的数学根源**——不是任意尺寸都行，
正确性由方程唯一锁定。

### 2. 比值分解（`ratio_decomp`，机制核心）

```
τ_A(F)/τ_o(F) = 1 + (1+α)·Σ_{k≤r} q^k / (2α·q^r)
              = 1 + α(1+α)/(q−1)  −  (1+α)/(2α(q−1)·q^r)
              = √3               −  余项(r)        ← ratio_limit + 指数衰减
```

- 第一部分 `1 + α(1+α)/(q−1) = √3`（`ratio_limit`）：由 α 极小多项式**精确坍缩**，
  Lean 验证通过。这就是"为什么恰是 √3"——不是近似，是恒等式。
- 第二部分是**余项**：分母含 `q^r`（q = 2α² > 1），随 r 指数衰减到 0
  （`remainder_pos` 保证非负）。
- 推论：绝对比 = √3 − ε_r（Theorem 2，r 越大越接近 √3）；
  加性界 d = 2−√3 吸收余项后，渐近比 = √3（Theorem 1）。

### 3. 加性常数是精确的（`additive_coeff`、`forced_makespan_additive`）

- `2α(√3−1)/q = 2−√3`：几何级数系数坍缩留下的精确常数 = Theorem 1 的 d。
- `forced_makespan_additive`：强制 makespan = √3·F − (2−√3) 对**每个** r 精确成立
  （与 BraunGraham2025.lean 的 braun_additive_identity 同一事实，这里独立重证）。

## 回答："为什么 2025 的自适应实例是正确的"

Braun 构造正确 = 三件事同时成立，缺一不可：
1. **强制调度唯一**（Table 3）：任何算法若把 S⁺_k 放错机器，makespan 立即超界
   （layer-separation 论证，非本探针范围，见论文 Lemma 1）；
2. **唯一逃生路径的比值可算**：沿 Table 3 走，比值 = 1 + α(1+α)/(q−1) − 余项(r)；
3. **代数坍缩**：α=1+√3 使 `1 + α(1+α)/(q−1)` **精确等于 √3**（本探针验证），
   余项指数衰减，所以绝对比 √3−ε_r → √3，加性界 √3·OPT − (2−√3) 恒成立。

**"正确"不是构造技巧，是代数必然**：尺寸参数必须满足精确方程
（Braun 的 α²−2α−2=0、Rudin 的 V=√3−1−ε 与 M=(3V−2)/2），
这是经典构造的共同骨架，也是模板生成器必须输出的"结构信息"。

## 回答："为什么 AI 能提出对抗实例模板"

1. 对抗模板 = **层模式（结构）+ 尺寸参数（连续）+ 代数约束**。
   FKT/Rudin/Tan-Li/Braun 全是"每层 m 个作业、层间递推、终止条件"的组合，
   LLM 在训练语料里见过这些文献的数学结构，能**组合已知模式**生成变体。
2. LLM 的缺陷（尺寸参数不精确、代数关系错误）由**数值验证兜底**：
   模板 → DE 优化尺寸 → minimax 求值 → 低于 √3 就淘汰。LLM 只需给出
   "结构合理"的候选，不需要"数值正确"。
3. 但结构里最关键的**代数约束**（α 的唯一性这类）不是 LLM 能猜的——
   这正是 Lean 验证层的价值：结构 + 参数 → Lean 确认代数坍缩是否真实。
   **分工：LLM 提结构，优化器找尺寸，Lean 证代数。**

## 工程备注（快速复现方式）

- 探针只 `import Mathlib`，不依赖项目库 → `lean-check.ps1` 单文件编译 24s，
  **不触发全库 lake build**（全库串行构建约 10+ 分钟，见 progress 2026-08-10）。
- 坑：`Real.sqrt_lt_sqrt`/`sqrt_le_sqrt` 的 `norm_num` 论证需要显式 ℝ 类型标注
  （否则默认 Nat）；`rw [α_sq]` 匹配 `α^2` 不匹配 `α*(2α+2)` 展开形式，
  先 `ring_nf`/`show ... by ring` 展开再 rw；`div_eq_iff` 处理 `a/b = c` 要
  先证 b≠0。

---

# 进展：Braun2025 形式化推进（2026-08-14，BraunGraham2025.lean +434 行）

## 新证明的定理（单文件编译通过，24s，未触发全库构建）

1. `braunLayerBlock_sum`：一层块的和 = 4L_k + 3S_k + S⁺_k
2. `braunBlocks_sum`：blocks 1..r 的和（range 下标 k+1 形式）
3. `braunSeq_sum_decomp`：序列和 = 4L₀ + 4S₀ + blocks + F
4. **`braun_totalLoad_eq`**：totalLoad(σ_r) = 4·ΣL + 6·ΣS
5. **`braun_total_work`（关键打包不变量）**：
   totalLoad(σ_r) = **4·F − (4+6α)/(q−1)**，常数亏损 ≈ 1.464 与 r 无关
   —— Table 7 打包的代数心脏：4 台容量 4F 只比总工作多 1.464，必须几乎满载。

## 发现：Table 7 打包的递归容量恒等式（数值验证，精确相等）

- 递归结构：σ_r 打包 = 3 台继承 σ_{r−1} 打包（放大 q 倍）+ 顶层 8 作业 + F 独占
- **容量恒等式**：6α·(q−1) = (4+4α+1/α)·q（由 α²−2α−2=0 导出，数值差 = 0.000000）
  —— 顶层作业总量恰好等于 3 台机器的容量增量，**无 slack**。

## Table 7 四机负载全确定（Lean 已验证）

| 机器 | 内容 | 负载 | Lean 定理 |
|---|---|---|---|
| M0 | {F} | F | 定义 |
| M1 | Σ_{k=1..r}(S⁺_k + 2L_k) + 2S₀ | **F** | `braun_M1_eq_F`（系数 [(α+2)q+2α] = 2α(q−1) 坍缩，α 极小多项式） |
| M2 | {S_r, S_r} | F（2S_r = F） | 定义 |
| M3 | 剩余全部 | **F − (4+6α)/(q−1) < F** | `braun_M3_lt_F`（由 total_work + M1 推出） |

- 新增引理：`braun_geom_sum_lt`（Σ_{k<r}q^k 闭式）、`braun_totalLoad_eq`
  （totalLoad = 4ΣL + 6ΣS）、`braun_total_work`、`braun_M1_eq_F`、`braun_M3_lt_F`，
  以及辅助 `braunLayerBlock_sum`/`braunBlocks_sum`/`braunSeq_sum_decomp`。
- M3 是唯一有 slack 的机器（slack = 常数 ≈1.464，与 r 无关）。
- **剩余**：显式分配函数（σ_r → 4 机，按 block 内位置分类：
  block 的 4L_k 中 2 个给 M1、2 个给 M3；3S_k 顶层 2 个给 M2、其余给 M3；
  S⁺_k 给 M1；S₀ 中 2 个给 M1、2 个给 M3；L₀ 全给 M3；F 给 M0）
  → `scheduleLoads_append` + `optMakespan_le_of_schedule` 得 OPT ≤ F，
  与 `braun_opt_ge_F` 合得 **OPT = F**。纯组合构造，无新数学。

## 下一步（按序）

1. 完整 Table 7 打包：显式分配（见上表）→ OPT ≤ F → OPT = F
2. 强制调度归纳（Table 3）：任意算法每层被迫分散（layer-separation 论证）
3. 主定理：∀ε（或固定 r），makespan ≥ √3·OPT − (2−√3)（用 braun_additive_identity）

---

# 关键修正：Braun 主定理是「自适应对抗」，不是固定序列（2026-08-14）

## 发现：固定序列下界不成立

原 progress/findings 里"强制调度"隐含的固定序列版
`∀ alg, algorithmMakespan 4 alg (braunSeq r) ≥ braunForcedMakespan r`
**是错的**。反例（r=1）：存在确定性在线算法在 σ₁ 上直接复现 Table 7 打包
（L₀→M3×4、S₀→M1/M1/M3/M3、L₁→M1/M1/M3/M3、S₁→M2/M2/M3、S⁺₁→M1、F→M0），
makespan = F = OPT < √3·F − (2−√3)。所以任何"固定 σ_r 打败所有算法"的证法都不成立。

正确表述是**自适应对抗下界**（论文 Theorem 1 的标准读法）：
`∀ alg, ∃ σ, algorithmMakespan 4 alg σ ≥ √3·τ_o(σ) − (2−√3)`，
其中 σ 是观察 alg 的放置逐步释放作业、一旦偏离"整齐"调度即以短前缀终止所得的序列。

## 已就位的基础（BraunGraham2025.lean，0 sorry）

- `braun_opt_eq_F`：OPT(σ_r) = F（含 r=0 边界修复：`braunAssign0`）
- `braun_layer_separation_from_base`：均匀 base 上 4 个相同作业 → 要么 makespan ≥ base+2x，要么全平衡
- `braun_prefix_additive_identity`：Φ_k + S⁺_k = √3(S⁺_k+L_k) − (2−√3)（S⁺_k 偏离陷阱的比）

## 剩余（主定理组装）

1. `braun_opt_prefix_Sp k`（Table 6 打包）：前缀 OPT = S⁺_k + L_k
2. 自适应归纳：L₀/S₀ 基例（层分离判比 2 / √3）→ 每层 L_k 强制分散 → S⁺_k 偏离即 STOP →
   最终 F（clean 路径用 braun_additive_identity）
3. 主定理 `∀ alg, ∃ σ, makespan ≥ √3·OPT − (2−√3)`
