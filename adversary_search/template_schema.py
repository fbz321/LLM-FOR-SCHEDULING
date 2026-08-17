#!/usr/bin/env python3
"""模板 schema：校验 + 解释器（C0 模板层的数据格式）。

模板 = 层模式（结构）+ 尺寸参数（连续）+ 代数约束（方程），JSON 表示。
本模块负责：validate(tpl) 校验合法性；materialize(tpl) 展开为作业序列
（Fraction 列表），交给 template_eval 的 eval_sequence/check_sequence 求值。

格式规格见 SCHEMA.md（同时作为 LLM 生成模板的 prompt 附件）。

表达式语言（Decimal 精确到 60 位，最终有理化到分母 <= 10^20）：
  数字、变量名、+ - * /、**（幂，注意 Python 优先级：^ 是位异或勿用）、一元负号、比较（仅 where 内）、
  where(cond, a, b)  —— 惰性求值，只算选中分支（Rudin 顶层需要）
  sqrt(x)、abs(x)

CLI：
  python template_schema.py seeds/fkt.json            # 校验并展开
  python template_schema.py seeds/rudin.json --show   # 打印作业序列
"""

import ast
import json
import sys
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 60
DENOM_CAP = 10 ** 20


class TplError(Exception):
    pass


def dec2frac(x):
    return Fraction(x).limit_denominator(DENOM_CAP)


# ---------------------------------------------------------------- expression
def _cmp(op, a, b):
    if isinstance(op, ast.GtE): return a >= b
    if isinstance(op, ast.Gt): return a > b
    if isinstance(op, ast.LtE): return a <= b
    if isinstance(op, ast.Lt): return a < b
    if isinstance(op, ast.Eq): return a == b
    if isinstance(op, ast.NotEq): return a != b
    raise TplError(f"不支持的比较运算符 {type(op).__name__}")


def _eval_node(node, env):
    if isinstance(node, ast.Expression):
        return _eval_node(node.body, env)
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool):
            raise TplError("布尔常量不允许")
        if isinstance(node.value, (int, float)):
            return Decimal(str(node.value))
        raise TplError(f"不支持的常量 {node.value!r}")
    if isinstance(node, ast.Name):
        if node.id in env:
            return env[node.id]
        raise TplError(f"未定义的名字 '{node.id}'")
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -_eval_node(node.operand, env)
    if isinstance(node, ast.BinOp):
        a = _eval_node(node.left, env)
        b = _eval_node(node.right, env)
        if isinstance(node.op, ast.Add): return a + b
        if isinstance(node.op, ast.Sub): return a - b
        if isinstance(node.op, ast.Mult): return a * b
        if isinstance(node.op, ast.Div):
            if b == 0: raise TplError("除以零")
            return a / b
        if isinstance(node.op, (ast.Pow, ast.BitXor)):  # ^ 约定为幂
            if b != int(b): raise TplError("只支持整数幂")
            return a ** int(b)
        raise TplError(f"不支持的二元运算 {type(node.op).__name__}")
    if isinstance(node, ast.Call):
        if not isinstance(node.func, ast.Name):
            raise TplError("只允许直接函数调用")
        fn = node.func.id
        if fn == "where":
            if len(node.args) != 3:
                raise TplError("where 需要 3 个参数")
            cond = _eval_node(node.args[0], env)
            if not isinstance(cond, bool):
                raise TplError("where 条件必须是布尔值")
            return _eval_node(node.args[1] if cond else node.args[2], env)
        if fn == "sqrt":
            v = _eval_node(node.args[0], env)
            if v < 0: raise TplError("sqrt 负数")
            return v.sqrt()
        if fn == "abs":
            return abs(_eval_node(node.args[0], env))
        raise TplError(f"未知函数 {fn}")
    if isinstance(node, ast.Compare):
        left = _eval_node(node.left, env)
        for op, comp in zip(node.ops, node.comparators):
            right = _eval_node(comp, env)
            if not _cmp(op, left, right):
                return False
            left = right
        return True
    raise TplError(f"不支持的语法 {type(node).__name__}")


def _parse(expr):
    try:
        return ast.parse(str(expr), mode="eval")
    except SyntaxError as e:
        raise TplError(f"表达式语法错误 {expr!r}: {e}")


def eval_expr(expr, env):
    return _eval_node(_parse(expr), env)


def solve_equation(eq, var, guess, env=None, iters=300):
    """牛顿法解 eq(var,...)=0，Decimal 高精度。"""
    base = dict(env or {})
    tree = _parse(eq)

    def f(x):
        e = dict(base)
        e[var] = x
        return _eval_node(tree, e)

    x = Decimal(str(guess))
    for _ in range(iters):
        fx = f(x)
        h = max(abs(x), Decimal(1)) * Decimal("1e-25")
        dfx = (f(x + h) - f(x - h)) / (2 * h)
        if dfx == 0:
            raise TplError(f"牛顿法导数为零 ({var}={x})")
        xn = x - fx / dfx
        if abs(xn - x) < Decimal("1e-45"):
            return xn
        x = xn
    raise TplError(f"牛顿法未收敛: {var}")


# ---------------------------------------------------------------- validate
def _exprs_of(tpl):
    """收集所有表达式 (位置描述, 表达式串)。"""
    out = []
    for p in tpl.get("params", []):
        out.append((f"params.{p.get('name')}.value", str(p.get("value"))))
    for s in tpl.get("solve", []):
        out.append((f"solve.{s.get('name')}.equation", s.get("equation", "")))
    for d in tpl.get("defs", []):
        out.append((f"defs.{d.get('name')}", d.get("expr", "")))
    rec = tpl.get("recurrence")
    if rec:
        for k, v in rec.get("init", {}).items():
            out.append((f"recurrence.init.{k}", v))
        for k, v in rec.get("step", {}).items():
            out.append((f"recurrence.step.{k}", v))
        if "until" in rec:
            out.append(("recurrence.until", rec["until"]))
    for li, item in enumerate(tpl.get("layers", [])):
        for ei, e in enumerate(item.get("emit", [])):
            out.append((f"layers[{li}].emit[{ei}].size", e.get("size", "")))
            out.append((f"layers[{li}].emit[{ei}].repeat", str(e.get("repeat", 1))))
        if "loop" in item:
            out.append((f"layers[{li}].loop.from", str(item["loop"].get("from", 0))))
            out.append((f"layers[{li}].loop.to", str(item["loop"].get("to", ""))))
    for fi, e in enumerate(tpl.get("final", [])):
        out.append((f"final[{fi}].size", e.get("size", "")))
        out.append((f"final[{fi}].repeat", str(e.get("repeat", 1))))
    return out


def validate(tpl):
    """返回错误列表（空 = 合法）。只做结构/语法检查，不做求值。"""
    errs = []
    for key in ("schema_version", "name", "m", "layers"):
        if key not in tpl:
            errs.append(f"缺少必需字段 {key}")
    if errs:
        return errs
    if tpl.get("schema_version") != 1:
        errs.append("schema_version 必须是 1")
    if not isinstance(tpl.get("m"), int) or tpl["m"] < 2:
        errs.append("m 必须是 >= 2 的整数")
    if not isinstance(tpl.get("layers"), list) or not tpl["layers"]:
        errs.append("layers 必须是非空列表")
    if tpl.get("order", "fwd") not in ("fwd", "rev"):
        errs.append("order 必须是 fwd 或 rev")
    for p in tpl.get("params", []):
        if "name" not in p or "value" not in p:
            errs.append(f"params 项缺 name/value: {p}")
    for s in tpl.get("solve", []):
        for k in ("name", "equation", "guess"):
            if k not in s:
                errs.append(f"solve 项缺 {k}: {s}")
    for d in tpl.get("defs", []):
        if "name" not in d or "expr" not in d:
            errs.append(f"defs 项缺 name/expr: {d}")
    for li, item in enumerate(tpl.get("layers", [])):
        if "emit" not in item or not item["emit"]:
            errs.append(f"layers[{li}] 缺 emit 或为空")
            continue
        if "loop" in item and "recurrence" not in tpl:
            errs.append(f"layers[{li}] 用了 loop 但没有 recurrence")
    for where_, expr_ in _exprs_of(tpl):
        try:
            _parse(expr_)
        except TplError as e:
            errs.append(f"{where_}: {e}")
    return errs


# ---------------------------------------------------------------- materialize
def _emit_layer(emit_list, env, check_positive=True):
    jobs = []
    for e in emit_list:
        r = int(eval_expr(e.get("repeat", 1), env))
        if r <= 0:
            raise TplError(f"repeat 必须为正: {e}")
        sz = eval_expr(e["size"], env)
        if check_positive and sz <= 0:
            raise TplError(f"作业尺寸必须为正: {e['size']} = {sz}")
        jobs.extend([sz] * r)
    return jobs


def materialize(tpl, check_positive=True):
    """模板 -> (Fraction 作业列表, meta)。"""
    errs = validate(tpl)
    if errs:
        raise TplError("模板非法: " + "; ".join(errs))

    env = {}
    for p in tpl.get("params", []):
        env[p["name"]] = Decimal(str(p["value"]))
    for s in tpl.get("solve", []):
        env[s["name"]] = solve_equation(s["equation"], s["name"], s["guess"], env)
    for d in tpl.get("defs", []):
        env[d["name"]] = eval_expr(d["expr"], env)

    states = []
    n = None
    rec = tpl.get("recurrence")
    if rec:
        st = {}
        for k, e in rec["init"].items():
            st[k] = eval_expr(e, {**env, **st})
        states.append(dict(st))
        until = rec.get("until")
        done = bool(eval_expr(until, {**env, **st})) if until else False
        i = 0
        while not done and i < rec.get("max_iter", 100):
            new = dict(st)
            for k, e in rec["step"].items():   # 顺序赋值语义
                new[k] = eval_expr(e, {**env, **new})
            st = new
            states.append(dict(st))
            i += 1
            if until:
                done = bool(eval_expr(until, {**env, **st}))
        if until and not done:
            raise TplError(f"递推在 {rec.get('max_iter', 100)} 步内未终止")
        n = len(states) - 1
        env["n"] = Decimal(n)

    layers = []
    for item in tpl["layers"]:
        if "loop" in item:
            lp = item["loop"]
            lo = int(eval_expr(str(lp.get("from", 0)), env))
            hi = int(eval_expr(str(lp["to"]), env))
            var = lp.get("var", "i")
            for k in range(lo, hi + 1):
                e2 = {**env, var: Decimal(k)}
                for nm, val in states[k].items():
                    e2[nm] = val
                if k + 1 < len(states):
                    for nm, val in states[k + 1].items():
                        e2[nm + "_next"] = val
                layers.append(_emit_layer(item["emit"], e2, check_positive))
        else:
            layers.append(_emit_layer(item["emit"], env, check_positive))

    if tpl.get("order", "fwd") == "rev":
        layers = layers[::-1]

    env_fin = dict(env)
    if states:
        for nm, val in states[0].items():
            env_fin[nm + "_first"] = val
        for nm, val in states[-1].items():
            env_fin[nm + "_last"] = val

    jobs = [j for layer in layers for j in layer]
    for e in tpl.get("final", []):
        r = int(eval_expr(e.get("repeat", 1), env_fin))
        sz = eval_expr(e["size"], env_fin)
        if check_positive and sz <= 0:
            raise TplError(f"final 尺寸必须为正: {e['size']}")
        jobs.extend([sz] * r)

    meta = {
        "name": tpl["name"], "m": tpl["m"], "n_jobs": len(jobs),
        "n_layers": len(layers), "n_recurrence": n,
        "params": {k: float(v) for k, v in env.items()
                   if isinstance(v, Decimal) and k in
                   {p["name"] for p in tpl.get("params", [])} |
                   {s["name"] for s in tpl.get("solve", [])}},
    }
    return [dec2frac(j) for j in jobs], meta


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    tpl = json.load(open(sys.argv[1], encoding="utf-8"))
    errs = validate(tpl)
    if errs:
        print("INVALID:")
        for e in errs:
            print(" -", e)
        sys.exit(1)
    jobs, meta = materialize(tpl)
    print(f"VALID: {meta['name']}  jobs={meta['n_jobs']} layers={meta['n_layers']}"
          + (f" recurrence_n={meta['n_recurrence']}" if meta['n_recurrence'] is not None else ""))
    print("params:", {k: round(v, 8) for k, v in meta['params'].items()})
    if "--show" in sys.argv:
        for i, j in enumerate(jobs):
            print(f"  [{i}] {float(j):.8f}  ({j})")


if __name__ == "__main__":
    main()
