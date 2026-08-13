# Bottleneck Reflection System

受 Gilbert-Pollak 论文 (Ke et al., ICML 2026) 启发，用 **大模型 + Lean 4 验证 + 瓶颈反省循环** 
缩小 P|online,list|Cmax 竞争比间隙 [1.88, 1.9201]。

**核心思路**: 不让 LLM 写完整证明，而是把它当作一个"参数提议器"——LLM 只需提出
adversary 的 job sizes（有理数），填入预编译的 Lean 模板，由 Lean kernel 验证。

## 架构

```
Model A (参数提议)          Template Engine               Lean Kernel
─────────────────         ────────────────              ────────────
提出 job sizes        →    填入 Lean 模板         →     编译检查
{a1, a2, F, ρ}             生成完整证明                  0 errors = 突破！
                                                       失败 → 反馈调参
```

## 组件

| 文件 | 功能 |
|---|---|
| `lean_verifier.py` | 调用 `lake env lean` 编译检查，解析错误类型 |
| `bottleneck_extractor.py` | 解析 Lean 编译错误 → 瓶颈自然语言描述 |
| `prompt_builder.py` | 构建 system/initial/fix/rethink 四类 prompt |
| `prompts/system.txt` | 系统 prompt，含完整的 5/4 工作示例 |
| `prompts/initial_proposal.txt` | 初始提议 prompt |
| `prompts/bottleneck_fix.txt` | 瓶颈修复 prompt |
| `prompts/strategy_rethink.txt` | 策略重想 prompt |
| `llm_client.py` | DeepSeek API 客户端 (支持 v4-pro/chat/reasoner) |
| `state_manager.py` | 持久化每轮迭代状态和证明 |
| `orchestrator.py` | Evaluate→Reflect→Propose→Translate 主循环 |
| `template_engine.py` | 参数 → Lean 模板填充引擎 |
| `templates/adversary_template.lean` | 2/3 层 adversary 参数化模板 |

## 关键 Lean 模块

| 文件 | 状态 | 说明 |
|---|---|---|
| `OnlineScheduling/Basic.lean` | ✅ 编译 | 核心定义和引理 |
| `OnlineScheduling/LowerBounds/Lemmas.lean` | ✅ 编译 | 3 个关键引理 (axiom): layer_separation, layer_separation_from_base, opt_of_identical_jobs |
| `OnlineScheduling/Template.lean` | 🔧 修复中 | 参数化 adversary 模板 (5 errors remaining) |

## 运行

```bash
cd /root/autodl-tmp/ai4math/bottleneck_reflection

# 单次测试
DEEPSEEK_API_KEY="sk-xxx" python3 run_e1.py

# 后台运行
DEEPSEEK_API_KEY="sk-xxx" nohup python3 -u run_e1.py > /tmp/e1.log 2>&1 &
tail -f /tmp/e1.log
```

## 实验结果

| 实验 | 模型 | 轮次 | 结果 |
|---|---|---|---|
| E0 | deepseek-chat | 5 轮 16 调用 | ρ 未突破 1.88，代码含 sorry |
| E1 | deepseek-v4-pro | 5 轮 16 调用 | ρ 未突破 1.88，模板被复制但战术错误 |
| E2 | deepseek-v4-pro + 新 prompt | 10 轮 43 调用 | 403 行无 sorry 代码，但依赖的引理缺 .olean |
| E3 | deepseek-v4-pro + Lemmas | 10 轮 | 引理可用但战术细节不准 |

## 经验教训

1. **deepseek-chat/v4-pro 能写出正确的 adversary 结构，但 Lean 4 战术细节不准**
2. **瓶颈反省循环能正确识别问题，但 LLM 的修复不收敛（错误越修越多）**
3. **关键突破: 编译了 Lemmas.lean（3个关键引理），让 LLM 可复用已验证的逻辑**
4. **方向: 多模型架构——Model A 提参数 + 预编译模板填充，完全避免 LLM 写战术**
5. **当前卡点: Template.lean 有 5 个战术错误待修复，修复后系统即可自动运行**

## 下一步

1. 修复 `Template.lean` 剩余 5 个编译错误
2. 将 `Template.lean` 编译为 `.olean`
3. 运行完整多模型流程：V4 Pro 提参数 → 填充模板 → Lean 验证 → 反馈
4. 目标: 从 ρ=1.88 突破至 1.89+
