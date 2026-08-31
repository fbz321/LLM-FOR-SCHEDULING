# 多 AI 研究工作流设计（经济实惠版，2026-08-25）

> 配套 `M5_ADVERSARY_SKETCH.md`。原则：**每个环节用最擅长且最便宜的模型，
> 升级只由机器验证门触发，批量任务吃包月，按量付费只留给真正难的环节。**

## 0. 已有资产（不重复造）

| 资产 | 位置 | 能力 |
|---|---|---|
| ModelRouter（flash→pro 验证失败自动升级） | `bottleneck_reflection/model_router.py` | 已实现+已测 |
| DeepSeek 客户端（chat / reasoner / v4-pro） | `bottleneck_reflection/llm_client.py` | 已实现（另含 claude-sonnet 后端） |
| Qwen Token Plan 网关客户端（no-think、批量、JSON 抢救） | `adversary_search/generate.py` | EXP-A 已验证（17/17 schema 合法） |
| 验证门（非 LLM） | `template_schema.py` / `pool_screen.py` / `lake build` / sympy | 升级判据全部机械化 |

## 1. 模型分档（各自擅长什么）

| 档位 | 模型 | 擅长 | 不擅长 | 计费特性 |
|---|---|---|---|---|
| **指挥官** | 本交互会话（Qwen3.8） | 全局上下文、决策、数学探索、写文档 | — | 已付费，边际 ¥0 |
| **廉价批量档** | Qwen-flash / qwen3.8-max **no-think**（Token Plan 网关） | 指令跟随、结构化 JSON、批量生成、照格式填空 | 深数学、长证明 | **包月订阅，边际≈¥0** |
| **按量廉价档** | deepseek-chat | 通用、便宜、Lean 战术及格、长文抽取 | 深推理 | ¥2/M 入 ¥8/M 出（量级） |
| **推理档** | deepseek-reasoner | 长链数学推导、Lean 难题、结构归纳 | 慢、贵 | ¥4/M 入 ¥16/M 出（量级） |
| **攻坚档** | claude-sonnet（已有客户端）/ Qwen3.8-Max think | 个别卡死的 Lean 声明、战术精度 | 贵 | 按量，人工批准才用 |
| ❌ 不用 | 本地 7B 模型 | — | SFT 实验已证 pass@3≤3.3%，无 Lean 能力 | 白烧 GPU |

## 2. 每一步的分工表

| # | 环节 | 频率 | 用谁 | 验证门（升级判据） | 升级路径 |
|---|---|---|---|---|---|
| S0 | 数值侦察（minimax/冒烟） | 高 | **无 AI**（autodl CPU，¥0） | — | — |
| S1 | 模板批量生成（约束旋钮） | 高 | **廉价批量档**：8 模板/次、16k tokens、no-think | schema 校验 + 漏斗 | 同档重试 **≤1 次** → 丢弃 |
| S2 | 尺寸优化（DE/PSLQ/identity_search） | 高 | **无 AI** | — | — |
| S3 | 漏斗粗筛 | 高 | **无 AI** | — | — |
| M | 数学推导（m=5 递推、坍缩恒等式、打包设计） | 低（每周几次） | **推理档**（deepseek-reasoner；备选 Qwen3.8-Max think 走官方端点，注意网关 think 会挂） | **sympy 数值验证 + 人工复核** | 人参与，不自动 |
| L1 | Lean 子目标（批量） | 中 | **ModelRouter flash_first**：deepseek-chat 先试 | `lake build` 编译 | 编译失败自动升级 reasoner（已实现） |
| L2 | Lean 攻坚（pro 仍失败的个别声明） | 低 | **攻坚档**（claude-sonnet 或人工） | `lake build` | **人工批准**才花钱 |
| A | 实验分析、findings/progress 记录 | 中 | **指挥官**（本会话，¥0） | 人工 | — |
| R | 文献抽取（PDF→表格/构造参数） | 低 | **按量廉价档**（长上下文） | 人工抽检 | — |

流水线：`S1(廉价批量) → S3(机器筛) → 幸存者 S2(机器优化) → M(推理档, 仅必要时) → L1(双档路由) → L2(攻坚, 人工门) → A(免费记录)`

## 3. 省钱七原则

1. **包月优先**：批量任务全部吃 Token Plan 网关（Qwen），边际成本≈0；按量付费（DeepSeek）只留给 Lean 路由升级链。
2. **零 API 环节**：S0/S2/S3 是纯计算，全部本机/autodl（32 核 377GB，免费）跑。
3. **机器验证门决定升级**：升级判据 = 编译错误/漏斗拒绝/数值不符，绝不让 LLM 自评（自评既花钱又不可靠）。
4. **批量 + no-think**：8 模板/次调用（EXP-A 验证防截断）；批量生成禁思考模式——思考 token 贵数倍且该网关 think 会挂 7 分钟。
5. **修复设上限**：廉价档最多修 1 轮，失败即丢弃。EXP-A/B 已证明修复循环不收敛——不要用贵的模型二次验证一个已知负结论。
6. **贵模型前置过滤**：数学推导产物必须先过 sympy 数值验证才能进 Lean——防止把错误的数学送进昂贵的 Lean 调用链。
7. **成本入账**：每个实验记录 calls/tokens/估算费用到 EXPERIMENT_LOG（沿用现有登记惯例）。

## 4. 预算估算（数量级）

| 活动 | 估算 |
|---|---|
| EXP-A 级模板实验（5 调用 <40k tokens） | <¥0.1（走 Qwen 网关 ≈ ¥0） |
| 一轮 100 模板生成 + 1 轮重试 | ¥0.5–2（Qwen 网关 ≈ ¥0） |
| 一次数学推导（reasoner，~50k tokens 含思考） | ¥1–3 |
| 一个千行级 Lean 文件形式化（BraunAbs 规模，含修复轮） | ¥10–60（大头在 pro 档） |
| **m=5 整线到出论文级结果的预算上限** | **¥100–300** |

## 5. 落地步骤（复用现有代码，~半天）

1. `llm_client.py` 加 `qwen-gateway` provider（抄 `generate.py` 的 call_qwen 20 行）
2. `model_router.py` 任务分档表扩 4 行：`template_gen`→flash(Qwen)、`math_derive`→pro 直连、`lean_subgoal`→flash_first、`lean_hard`→pro_only+人工门
3. 新建 `workflow.yaml`：stage → model → max_calls → escalate_to → verify_cmd
4. 冒烟：`generate.py --n 3`（网关活着）+ `run_router.py --no-api`（路由活着）+ 一次 1 子目标的真实 Lean 路由

## 6. 明确不花的钱

- ❌ 新购海外订阅（GPT/Claude 月费+代理）——已有客户端够用，攻坚偶尔按量即可
- ❌ 本地 7B/14B 自训——2026-08 前的 SFT 实验（R9/R10）已证无效
- ❌ 昂贵模型跑修复循环（EXP-B 结论：结构性失败修不好）
- ❌ 批量生成用思考模式
