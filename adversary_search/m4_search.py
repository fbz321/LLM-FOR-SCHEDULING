#!/usr/bin/env python3
"""m=4 下界自动对抗搜索原型：精确 minimax + 枚举 OPT。

博弈模型（与 Gormley et al. 2000 的游戏树同构）：
  - 对抗者（最大化）：每轮从有限网格里选一个作业尺寸，可随时停止；
  - 调度器（最小化）：把作业放到某台机器（负载相同的机器等价，只留一个分支）；
  - 停止收益 = makespan / OPT(当前前缀)，OPT 用分支定界枚举精确计算。

value(loads, jobs) = 从该状态出发对抗者能保证的最大收益（记忆化递归，
深度隐含在 len(jobs) <= n_max 里）。

用法示例：
  python m4_search.py --m 4 --grid 1,2 --depth 12
  python m4_search.py --m 4 --grid 207,500,1000 --depth 9 --play
"""

import argparse
import sys
import time
from fractions import Fraction
from functools import lru_cache

sys.setrecursionlimit(100000)


# ----------------------------------------------------------------------
# 精确 OPT：分支定界枚举（作业降序放置，对称 + 支配剪枝，整数算术）
# ----------------------------------------------------------------------
# opt 是模块级全局缓存，跨 eval 累积——必须设上限防内存无限增长
# （k=3 深度 13 时 8 并发曾打爆 16GB）。LRU 淘汰只影响速度，不影响正确性。
@lru_cache(maxsize=200_000)
def opt(jobs, m):
    """jobs: 排序后的整数尺寸元组；返回 m 台机的最优 makespan（整数）。"""
    if not jobs:
        return 0
    jobs = tuple(sorted(jobs, reverse=True))
    n = len(jobs)
    best = sum(jobs)  # 平凡上界：全部放一台
    loads = [0] * m
    total_remaining = sum(jobs)

    def dfs(i):
        nonlocal best, total_remaining
        if i == n:
            mx = max(loads)
            if mx < best:
                best = mx
            return
        mx = max(loads)
        if mx >= best:
            return
        # 下界：当前最大负载 与 剩余平均负载 的较大者
        lb = max(mx, -(-(sum(loads) + total_remaining) // m))
        if lb >= best:
            return
        p = jobs[i]
        total_remaining -= p
        seen = set()
        for j in range(m):
            l = loads[j]
            if l in seen:
                continue
            seen.add(l)
            loads[j] = l + p
            dfs(i + 1)
            loads[j] = l
        total_remaining += p

    dfs(0)
    return best


# ----------------------------------------------------------------------
# 博弈搜索
# ----------------------------------------------------------------------
class AdversarySearch:
    def __init__(self, m, grid, n_max, target=None):
        self.m = m
        self.grid = tuple(sorted(set(grid)))
        self.n_max = n_max
        self.target = target  # 若设置，收益封顶到 target（可达性搜索用）
        self.nodes = 0

    # value 缓存：实例级，单次 eval_free 生命周期内有效。
    # 实测 k=3 全树状态数 > 1M：任何 maxsize 上限（200k/1M 都试过）都会
    # 触发 LRU 淘汰风暴，把单 eval 从 ~95s 拖到 >600s。故必须 maxsize=None；
    # 内存控制靠 eval_free 末尾 cache_clear + gc.collect + 限制并发 worker 数。
    @lru_cache(maxsize=None)
    def value(self, loads, jobs):
        self.nodes += 1
        loads = tuple(sorted(loads))
        r = Fraction(max(loads), opt(jobs, self.m)) if jobs else Fraction(0)
        if len(jobs) >= self.n_max:
            return r
        best = r  # 停止选项
        for p in self.grid:
            worst = None
            seen = set()
            for j, l in enumerate(loads):
                if l in seen:
                    continue
                seen.add(l)
                nl = list(loads)
                nl[j] = l + p
                v = self.value(tuple(nl), tuple(sorted(jobs + (p,))))
                if worst is None or v < worst:
                    worst = v
            if worst is not None and worst > best:
                best = worst
            if self.target is not None and best >= self.target:
                return self.target
        return best

    def root_value(self):
        self.nodes = 0
        return self.value((0,) * self.m, ())

    def play(self, verbose=True):
        """按最优策略走一步：对抗者选最大收益的作业，调度器按最坏响应放置。"""
        loads = (0,) * self.m
        jobs = ()
        path = []
        while len(jobs) < self.n_max:
            r_now = Fraction(max(loads), opt(jobs, self.m)) if jobs else Fraction(0)
            best_move, best_val = None, r_now
            for p in self.grid:
                worst, worst_mach = None, None
                seen = set()
                for j, l in enumerate(loads):
                    if l in seen:
                        continue
                    seen.add(l)
                    nl = list(loads)
                    nl[j] = l + p
                    v = self.value(tuple(nl), tuple(sorted(jobs + (p,))))
                    if worst is None or v < worst:
                        worst, worst_mach = v, j
                if worst is not None and worst > best_val:
                    best_val, best_move = worst, (p, worst_mach)
            if best_move is None or best_val <= r_now:
                break  # 对抗者选择停止
            p, j = best_move
            path.append((p, j))
            loads = list(loads)
            loads[j] += p
            loads = tuple(sorted(loads))
            jobs = tuple(sorted(jobs + (p,)))
            if verbose:
                o = opt(jobs, self.m)
                r = Fraction(max(loads), o) if jobs else Fraction(0)
                print(
                    f"  作业 {p:>6}: 放到负载 {loads[j] - p:>4} 的机器 -> "
                    f"负载 {list(loads)}, OPT={o}, 比值={float(r):.6f}"
                )
        return path, loads, jobs


def main():
    ap = argparse.ArgumentParser(description="m 台机在线调度对抗搜索原型")
    ap.add_argument("--m", type=int, default=4)
    ap.add_argument("--grid", type=str, default="1,2", help="逗号分隔的作业尺寸（整数）")
    ap.add_argument("--depth", type=int, default=10, help="作业数上界 n_max")
    ap.add_argument("--target", type=str, default=None, help="目标比值（可达性搜索，封顶加速）")
    ap.add_argument("--play", action="store_true", help="输出一条最优对抗路径")
    args = ap.parse_args()

    grid = tuple(int(x) for x in args.grid.split(","))
    target = Fraction(args.target) if args.target else None
    s = AdversarySearch(args.m, grid, args.depth, target)

    t0 = time.time()
    v = s.root_value()
    dt = time.time() - t0
    print(f"m={args.m}  grid={list(grid)}  n_max={args.depth}")
    print(f"根值（对抗者能保证的最大竞争比） = {float(v):.6f} = {v}")
    print(f"节点数 = {s.nodes}，耗时 = {dt:.2f}s")
    if args.play:
        s.play()


if __name__ == "__main__":
    main()
