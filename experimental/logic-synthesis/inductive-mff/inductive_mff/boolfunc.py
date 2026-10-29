"""Truth-table semantics for Boolean functions.

This module provides a *semantic oracle* used by the decision procedure:
cofactor, equivalence, essential-variable status, and the universal
literal-count lower bound

        LB(f) = alpha(f) + 2 * beta(f)

where alpha = number of essential unate variables and beta = number of
essential binate variables.

The oracle is truth-table based (complete but exponential in the number of
variables).  In a production setting one would replace it with a BDD / SAT
package; the decision *procedure* itself does not depend on which oracle is
used, only that the oracle answers the following queries exactly:

    cofactor(f, x, b)         -- f with x forced to b
    f == g                    -- functional equivalence
    f == 0  /  f == 1         -- constant tests
    alpha, beta, LB(f)        -- unate / binate classification
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Set, Tuple

from .ast import And, Gnd, Lit, Node, Or, eval_node


@dataclass(frozen=True)
class BoolFunc:
    """A Boolean function over an ordered tuple of variables.

    `tt` is an integer bit-mask: bit i is the value of the function on the
    assignment whose j-th variable takes the value of bit j of i
    (little-endian variable order).
    """

    vars: Tuple[str, ...]
    tt: int

    @property
    def n(self) -> int:
        return len(self.vars)

    @property
    def mask(self) -> int:
        return (1 << (1 << self.n)) - 1


def truth_table(expr: Node, universe: Tuple[str, ...]) -> BoolFunc:
    """Build the truth table of an expression over a fixed variable universe."""
    n = len(universe)
    tt = 0
    for i in range(1 << n):
        ass: Dict[str, int] = {universe[j]: (i >> j) & 1 for j in range(n)}
        if eval_node(expr, ass):
            tt |= 1 << i
    return BoolFunc(universe, tt)


def cofactor(fn: BoolFunc, var: str, value: int) -> BoolFunc:
    """Cofactor of fn w.r.t. var=value, kept over the *same* variable set."""
    if var not in fn.vars:
        return fn
    j = fn.vars.index(var)
    n = fn.n
    out = 0
    for i in range(1 << n):
        i2 = (i & ~(1 << j)) | (value << j)
        out |= ((fn.tt >> i2) & 1) << i
    return BoolFunc(fn.vars, out)


def eq(a: BoolFunc, b: BoolFunc) -> bool:
    assert a.vars == b.vars, "comparing functions over different universes"
    return a.tt == b.tt


def is_zero(fn: BoolFunc) -> bool:
    return fn.tt == 0


def is_one(fn: BoolFunc) -> bool:
    return fn.tt == fn.mask


def var_status(fn: BoolFunc, var: str) -> str:
    """Classify var within fn as one of:

    'nonessential'  -- fn does not depend on var
    'pos-unate'     -- fn is monotone nondecreasing in var
    'neg-unate'     -- fn is monotone nonincreasing in var
    'binate'        -- fn depends on var in both polarities
    """
    c0 = cofactor(fn, var, 0)
    c1 = cofactor(fn, var, 1)
    if c0.tt == c1.tt:
        return "nonessential"
    full = fn.mask
    decreasing = c0.tt & (~c1.tt & full)  # cof0 = 1 and cof1 = 0
    increasing = c1.tt & (~c0.tt & full)  # cof1 = 1 and cof0 = 0
    if decreasing == 0 and increasing != 0:
        return "pos-unate"
    if increasing == 0 and decreasing != 0:
        return "neg-unate"
    return "binate"


def alpha_beta(fn: BoolFunc) -> Tuple[int, int]:
    """Return (alpha, beta): #essential unate vars, #essential binate vars."""
    alpha = 0
    beta = 0
    for v in fn.vars:
        st = var_status(fn, v)
        if st in ("pos-unate", "neg-unate"):
            alpha += 1
        elif st == "binate":
            beta += 1
    return alpha, beta


def lower_bound(fn: BoolFunc) -> int:
    """Universal lower bound on literal count of any factored form of fn."""
    a, b = alpha_beta(fn)
    return a + 2 * b


def essential_vars(fn: BoolFunc) -> Set[str]:
    return {v for v in fn.vars if var_status(fn, v) != "nonessential"}