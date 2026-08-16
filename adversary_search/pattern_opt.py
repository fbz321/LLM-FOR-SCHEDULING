#!/usr/bin/env python3
"""尺寸集合优化：固定 k+1 个作业尺寸与作业数上界 k·m+1，
把尺寸当连续变量，用自由 minimax（对抗者可自适应选择尺寸、随时停止）
作为精确目标函数，最大化可保证的竞争比。

搜索器（m4_search.AdversarySearch）对任意尺寸集合给出精确的
"任意确定性算法竞争比 ≥ 值" 的真下界，因此优化结果可直接作为
数学定理的候选；最后用高精度重算 + --play 输出对抗路径供分析。
"""

import argparse
import gc
import os
import sys
import time

import numpy as np
from scipy.optimize import differential_evolution, minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import m4_search as core

_EVAL_LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "evals.log")
_eval_count = 0


def _log_eval(x, v, tag=""):
    """进度写文件（workers 并行时 callback 被禁用，靠文件日志留档）。"""
    global _eval_count
    _eval_count += 1
    with open(_EVAL_LOG, "a", encoding="utf-8") as f:
        f.write(f"{time.strftime('%H:%M:%S')} [{os.getpid()}] "
                f"#{_eval_count} {tag} x={np.round(x, 6).tolist()} v={v:.6f}\n")


def _scaled_sizes(sizes, scale):
    """归一化（max -> 1）并放大为整数。"""
    mx = max(sizes)
    return tuple(max(1, int(round(s / mx * scale))) for s in sizes)


def eval_free(sizes, m=4, k=2, scale=1000, target=None):
    """自由 minimax 值：网格 = k+1 个尺寸，深度 = k·m+1。
    target 非空时封顶（可达性加速）。"""
    grid = tuple(sorted(set(_scaled_sizes(sizes, scale))))
    search = core.AdversarySearch(m, grid, k * m + 1, target)
    v = float(search.root_value())
    # 显式释放实例级 value 缓存并强制 GC：Python 分配器不返还 OS 内存，
    # 不清的话 DE 密集调用会让进程水位（高水位标记）持续上涨，
    # 实测 4 worker × ~2GB 把 16GB 内存打爆。cache_clear 只清缓存对象，
    # 仍需 gc.collect() 让可回收对象真正释放。
    search.value.cache_clear()
    gc.collect()
    return v


def _objective(x, m, k, scale, target, tag=""):
    v = eval_free(list(x), m, k, scale, target)
    _log_eval(x, v, tag)
    return -v


def optimize(k, m=4, scale=1000, popsize=8, maxiter=15, seed=0, init_points=None,
             workers=1, polish=True, target=None):
    n_params = k + 1
    bounds = [(0.05, 2.0)] * n_params

    init = "sobol" if init_points is None else np.array(init_points, dtype=float)

    def cb(xk, conv):
        # 每代记录最优尺寸向量（flush，后台被杀也能留档；值在结束时由 report 输出）
        print(f"[gen] best_x={np.round(xk, 6).tolist()} convergence={conv:.6f}",
              flush=True)

    res = differential_evolution(
        _objective,
        bounds,
        args=(m, k, scale, target, "de"),
        popsize=popsize,
        maxiter=maxiter,
        seed=seed,
        tol=1e-10,
        polish=False,
        updating="immediate",
        workers=workers,
        init=init,
        callback=cb,
    )
    x = np.clip(res.x, 0.05, 2.0)
    v = eval_free(list(x), m, k, scale)

    # 从当前最优出发做高精度局部精修（目标 = 当前值，走可达性加速）
    best_x, best_v = list(x), v
    if not polish:
        return best_x, best_v
    for _ in range(3):
        res2 = minimize(
            _objective,
            np.array(best_x),
            args=(m, k, 10000, best_v, "polish"),
            method="Nelder-Mead",
            options=dict(maxiter=100, xatol=1e-5, fatol=1e-8),
        )
        x2 = np.clip(res2.x, 0.05, 2.0)
        v2 = eval_free(list(x2), m, k, 10000, None)  # 精确复评
        if v2 > best_v:
            best_x, best_v = list(x2), v2
        else:
            break
    return best_x, best_v


def report(k, x, v, m=4):
    s = _scaled_sizes(x, 10 ** 6)
    print(f"\nk={k}（{k + 1} 个尺寸，n_max={k * m + 1}）")
    print(f"归一化尺寸: {[round(float(t), 6) for t in x]}")
    print(f"精确尺寸 (×10^6): {s}")
    print(f"值 = {v:.8f}")
    print(f"对照：√3 ≈ 1.7320508，26/15 ≈ 1.7333333")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, default=2, help="行数/尺寸数-1")
    ap.add_argument("--m", type=int, default=4)
    ap.add_argument("--popsize", type=int, default=8)
    ap.add_argument("--maxiter", type=int, default=15)
    ap.add_argument("--workers", type=int, default=1, help="差分演化并行进程数")
    ap.add_argument("--no-polish", action="store_true", help="跳过 Nelder-Mead 局部精修")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--target", type=float, default=None,
                    help="主 DE 阶段的目标比值（可达性封顶加速，如 1.73206 逼近 √3）")
    ap.add_argument("--check", action="store_true", help="对给定尺寸只求值")
    ap.add_argument("--sizes", type=str, default=None)
    ap.add_argument("--play", action="store_true", help="输出最优尺寸的对抗路径")
    ap.add_argument("--baseline", action="store_true", help="评估 FKT 尺寸 (0.2071,0.5,1)")
    args = ap.parse_args()

    if args.check:
        sizes = [float(x) for x in args.sizes.split(",")]
        k = len(sizes) - 1
        v = eval_free(sizes, args.m, k)
        print("sizes:", sizes, "-> 自由 minimax 值 =", v)
        return

    if args.baseline:
        for s in [(0.2071, 0.5, 1.0), (0.25, 0.5, 1.0)]:
            k = len(s) - 1
            print(s, "->", eval_free(list(s), args.m, k))
        return

    t0 = time.time()
    x, v = optimize(args.k, args.m, popsize=args.popsize, maxiter=args.maxiter,
                    seed=args.seed, workers=args.workers, polish=not args.no_polish,
                    target=args.target)
    report(args.k, x, v, args.m)
    print(f"优化耗时 {time.time() - t0:.1f}s")

    if args.play:
        s = _scaled_sizes(x, 1000)
        grid = tuple(sorted(set(s)))
        search = core.AdversarySearch(args.m, grid, args.k * args.m + 1)
        print("对抗路径（自由 minimax 最优策略，调度器按最坏响应）：")
        search.play()


if __name__ == "__main__":
    main()
