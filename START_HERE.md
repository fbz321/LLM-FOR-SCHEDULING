# START_HERE — 新机器/新会话接手指南

> 本仓库 = 在线调度竞争比下界研究：**Lean 4 机械化证明库** + **AI 辅助对抗搜索**。
> 目标：把 P|online,list|Cmax 的下界从已知结果继续推进（m=4 间隙 [√3, 26/15]；渐近间隙 [1.88, 1.9201]）。

## 我是新服务器/新会话，先看这三个文件

1. `docs/research/RESEARCH_PLAN.md` — 总计划与里程碑（A/B/C/D 四条线）
2. `docs/research/progress.md` — 最新工作日志（文件开头 = 最近一次会话）
3. `docs/research/findings.md` — 数学发现与踩坑记录（含"LLM 提结构、优化器找尺寸、Lean 证代数"分工结论）

## 目录地图

| 目录/文件 | 内容 |
|---|---|
| `OnlineScheduling/` | Lean 4 库（Lean v4.33.0-rc1 + mathlib）：已证下界定理（Rudin √3、FKT、Braun2025 Thm1/Thm2-r1 等），0 sorry |
| `Mechanisms/` | 5 个机制探针（*Key.lean，只 import Mathlib、秒级编译）：每个经典构造的魔法常数+极小多项式 |
| `adversary_search/` | Python 搜索引擎：`m4_search.py`（精确 minimax+枚举 OPT）、`pattern_opt.py`（DE 尺寸优化）、`template_eval.py`（模板约束求值器，FKT/Braun/Rudin 种子已通过冒烟）；结果在 `RESULTS.md` |
| `bottleneck_reflection/` | LLM 循环框架（orchestrator/模型路由/模板引擎/Lean 验证器）；运行说明见其 `RUN_PROMPT.md` |
| `docs/research/` | 研究记录：RESEARCH_PLAN / progress / findings / LOWER_BOUND_TODOLIST / adversary-search-workflow |
| `scripts/`, `training/`, `validation/` | 辅助脚本与训练数据工具 |

## 环境搭建

```bash
# 1) Lean（版本由 lean-toolchain 锁定：v4.33.0-rc1）
curl https://elan-init.org/elan-init.sh -sSf | sh   # 或 Windows 版 elan
cd OnlineScheduling
lake exe cache get        # 拉 mathlib 缓存（若无缓存权限，可从本机 rsync .lake/）
lake build                # 全库构建；磁盘不稳时改串行：逐模块 lake build <模块名>

# 2) Python 3.11+（Anaconda 亦可）
pip install numpy scipy

# 3) LLM API（仅 bottleneck_reflection 需要）
export DEEPSEEK_API_KEY=sk-...   # 或放 .env（已被 .gitignore 排除，勿提交）
```

## 常用实验命令

```bash
cd adversary_search
python m4_search.py --m 4 --grid 207,500,1000 --depth 9 --play     # 复现 FKT 1.707
python template_eval.py --seed fkt                                  # 模板求值冒烟（期望 1.707）
python template_eval.py --seed braun                                # 期望 >= c1 ~ 1.731019
python template_eval.py --seed rudin --eps 0.01 --order rev         # 期望 >= sqrt(3)-eps
python template_eval.py --seed rudin --eps 0.0001 --order rev --check 1.731  # 深模板用阈值模式（省内存）
# 注意：--check auto 对无理参数种子（Braun/Rudin）会因有理化误差（~1e-15）差一点点失败，
# 显式给略低于理论界的 tau 即可（实测状态数从 46 万降到 ~31）
python pattern_opt.py --k 3 --popsize 6 --maxiter 10 --workers 8 --no-polish  # DE 尺寸优化（小时级）

cd bottleneck_reflection
python run_router.py --target 1.89 --max-iterations 20              # LLM 循环（花 API 钱）
```

## 当前状态与下一步（2026-08-16）

- ✅ Braun2025 Thm1 + Thm2(r=1) 全部形式化（0 sorry）；k=3 自由搜索负结果（1.702 封顶）
- 🔜 **AI 辅助模板构造（A3'/C0）**：模板 schema + LLM 生成 + template_eval 粗筛；
  下一步是模板池 + LLM 模板生成 prompt（用 Mechanisms 探针做 few-shot）
- 详见 `docs/research/progress.md` 顶部会话记录

## 注意事项

- `.env` 含 API key，永不提交（gitignore 已排除）
- 深模板精确求值吃内存（33 作业级需 64–128GB），优先用 `--check` 阈值模式
- `adversary_search/RESULTS.md` 是所有搜索结果的唯一登记处，跑完实验必须记录
