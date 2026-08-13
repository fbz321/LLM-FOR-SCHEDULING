# Lake 使用指南

## 基本命令

```bash
cd /root/autodl-tmp/ai4math

# 单文件快速检查（推荐，跳过 lake 的 git 检查）
/root/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/bin/lean \
  OnlineScheduling/LowerBounds/Faigle.lean -R .lake/packages

# 全量构建（先做单文件检查，确认无误再跑）
lake build

# 只看错误
lake build 2>&1 | grep "error:"
```

## 依赖管理

```
ai4math/
├── lakefile.lean          # 项目声明 + mathlib 依赖
├── lake-manifest.json     # 所有包（10个）的固定 git commit
├── lean-toolchain         # Lean 版本（v4.33.0-rc1）
└── .lake/
    ├── packages/           # 依赖源码
    │   └── mathlib/        # ~1.1G 源码，8271 oleans (12GB)
    └── build/              # 项目自身编译产物 (132MB)
```

**关键**：`lake-manifest.json` 固定了每个依赖的 git commit。如果 `.lake/packages/<pkg>` 的实际 git HEAD 与 manifest 不一致，lake 会**删除该包并尝试从 github 重新 clone**，在无网络环境下直接失败。

## 编译错误速查

### 1. manifest out of date / git revision changed

**现象**：
```
warning: manifest out of date: git revision of dependency 'mathlib' changed
info: mathlib: cloning https://github.com/...
error: RPC failed; curl 16 Error in the HTTP2 framing layer
```

**原因**：`.lake/packages/mathlib` 是裸 git 仓库（只有 `objects/`），HEAD 与 manifest 不一致时 lake 会尝试重新 clone，但 github 不可达。

**修复**：无需重新编译 mathlib，只需欺骗 lake 让 git HEAD 匹配 manifest：
```bash
# 查看 manifest 期望的 commit
python3 -c "import json; m=json.load(open('lake-manifest.json')); \
  [print(p['rev']) for p in m['packages'] if p['name']=='mathlib']"

# 写入 fake HEAD（替换为实际 manifest 中的 commit）
echo "<FULL_COMMIT_HASH>" > .lake/packages/mathlib/.git/HEAD
mkdir -p .lake/packages/mathlib/.git/refs/heads
echo "<FULL_COMMIT_HASH>" > .lake/packages/mathlib/.git/refs/heads/master
```
同理适用于其他 9 个依赖包。

### 2. `lake env lean` 很慢

**现象**：`lake env lean Foo.lean` 卡住 >60s

**原因**：lake 检查所有 10 个依赖包的 git 状态，裸仓库的 "has local changes" 警告拖慢启动。

**修复**：绕过 lake，直接调 lean 二进制：
```bash
/root/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/bin/lean \
  OnlineScheduling/<Path>/Foo.lean -R .lake/packages
```

### 3. noncomputable 错误

```
error: failed to compile definition, consider marking it as 'noncomputable'
```

在 `def` 前加 `noncomputable`。原因：Lean 4 中 `ℝ` 除法是 noncomputable 的。

### 4. opt_le_of_schedule 参数不足

```
error: Tactic `apply` failed: could not unify the conclusion
```

这个 axiom 需要 3 个参数：`(σ) (loads) (h_valid : totalLoad = sum)`：
```lean
opt_le_of_schedule (m := 2) σ loads h_valid
```

### 5. opt_ge_max_job 不接受 `m :=` 命名参数

```lean
-- ❌ 错误
opt_ge_max_job (m := 2) [1, 1]

-- ✅ 正确
opt_ge_max_job [1, 1]
```

### 6. `let` 绑定不能被 simp/rw/subst 展开

在 Lean 4 中，`let` 定义的变量不会被 `simp`、`rw`、`subst`、`fin_cases` 自动展开。
改用 `set x := ... with hx_def`，然后用 `rw [hx_def]` 手动展开，参考 `ClassicOnline.lean` 中 P2/P3 证明的写法。

### 7. mathlib API 不存在

```lean
-- ❌ mathlib 44040b4c 中不存在
Real.pow_sqrt_eq_abs 2

-- ✅ 替代
Real.sq_sqrt (show 0 ≤ 2 from by norm_num)
```
