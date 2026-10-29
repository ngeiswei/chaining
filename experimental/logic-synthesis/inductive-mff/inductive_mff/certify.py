"""The inductive decision procedure for minimal factored forms.

Given a factored form ``F`` over {∧, ∨, ¬-on-leaves}, the procedure decides
whether ``F`` is *minimum* among all factored forms equivalent to it, where
size is the number of literals ``rho(F)``.

It is a *decision* procedure (yes / no / unknown), not a rewriting tool,
although every ``NOT_MINIMAL`` answer carries a strictly smaller equivalent
form as a certificate.

The verdicts are three-valued and *sound*:

    MINIMAL      there is a proof that rho(F) == rho(function).
    NOT_MINIMAL  a smaller equivalent factored form is exhibited.
    UNKNOWN      neither certificate was found (the gap must be closed by a
                 complete but expensive Boolean-division / QBF search).

With ``exact=True`` the UNKNOWN gaps are closed by exhaustive enumeration of
ordered ∧/∨ binary trees (complete, but exponential; bounded by a budget).
"""
from __future__ import annotations

import time
from dataclasses import dataclass
from enum import Enum
from functools import lru_cache
from itertools import product
from typing import Dict, Optional, Tuple

from .ast import (And, G0, G1, Gnd, Lit, Node, Or, cofactor_expr, parse,
                  rho, simplify, to_str, vars_of)
from .boolfunc import (BoolFunc, cofactor, eq, essential_vars, is_one,
                       is_zero, lower_bound, truth_table)


class Verdict(str, Enum):
    MINIMAL = "MINIMAL"
    NOT_MINIMAL = "NOT_MINIMAL"
    UNKNOWN = "UNKNOWN"


@dataclass
class Result:
    verdict: Verdict
    expr: Node          # the expression being decided
    best: Node          # best known equivalent form (== expr unless smaller)
    fn: BoolFunc        # semantics of `expr`
    reason: str
    elapsed: float = 0.0  # seconds spent certifying this expression

    @property
    def input_cost(self) -> int:
        return rho(self.expr)

    @property
    def cost(self) -> int:
        return rho(self.best)


class BudgetExceeded(Exception):
    """Raised when the exact global search exceeds its work budget."""


# --------------------------------------------------------------------------
# Shannon re-composition
# --------------------------------------------------------------------------
def shannon_join(x: str, w0: Node, w1: Node, h0: BoolFunc, h1: BoolFunc) -> Node:
    """Combine h = (x'·h0) ∨ (x·h1) back into a factored form.

    ``w0``/``w1`` are (already discovered) forms equivalent to the cofactors
    ``h0``/``h1``.  The number of x-literals is chosen from the cofactors:

        h0 ≡ h1        x is not read at all            (0 literals)
        h0 ≡ 0 or 1    unate in x                      (1 literal)
        h1 ≡ 0 or 1    unate in x                      (1 literal)
        otherwise      binate in x, full MUX/shannon   (2 literals)
    """
    if eq(h0, h1):
        return w0 if rho(w0) <= rho(w1) else w1
    if is_zero(h0):
        return And(Lit(x, False), w1)
    if is_zero(h1):
        return And(Lit(x, True), w0)
    if is_one(h0):
        return Or(Lit(x, True), w1)
    if is_one(h1):
        return Or(Lit(x, False), w0)
    return Or(And(Lit(x, True), w0), And(Lit(x, False), w1))


# --------------------------------------------------------------------------
# Ordered binary and/or trees with `k` leaves (used by the exact fallback)
# --------------------------------------------------------------------------
@lru_cache(maxsize=None)
def leaf_shapes(k: int) -> Tuple:
    """All ordered full binary trees with `k` leaves, internal nodes being
    either And or Or, and leaves left as ``None`` placeholders."""
    if k == 1:
        return (None,)
    out = []
    for i in range(1, k):
        for left in leaf_shapes(i):
            for right in leaf_shapes(k - i):
                out.append(And(left, right))  # type: ignore[arg-type]
                out.append(Or(left, right))   # type: ignore[arg-type]
    return tuple(out)


def _fill(shape, leaves):
    it = iter(leaves)

    def go(s):
        if s is None:
            return next(it)
        if isinstance(s, And):
            return And(go(s.left), go(s.right))
        if isinstance(s, Or):
            return Or(go(s.left), go(s.right))
        return s

    return go(shape)


# --------------------------------------------------------------------------
# The decision procedure
# --------------------------------------------------------------------------
class Certifier:
    """Decide whether a factored form is a minimum factored form.

    Parameters
    ----------
    universe:
        Ordered variable universe.  If omitted it is inferred from the first
        formula (sorted).
    exact:
        If True, close every UNKNOWN gap with an exhaustive search over all
        ordered ∧/∨ binary trees (complete for a bounded leaf count).
    search_budget:
        Maximum number of candidate trees the exact fallback may build before
        giving up (raising BudgetExceeded internally and degrading to
        UNKNOWN).  Guards against the exponential worst case.
    """

    def __init__(self, universe: Optional[Tuple[str, ...]] = None, *,
                 exact: bool = False, search_budget: int = 500_000):
        self.universe: Optional[Tuple[str, ...]] = (
            None if universe is None else tuple(universe))
        self.exact = exact
        self.search_budget = search_budget
        self._memo: Dict = {}

    # -- public entry points ------------------------------------------------
    def certify(self, expr, universe: Optional[Tuple[str, ...]] = None) -> Result:
        if isinstance(expr, str):
            expr = parse(expr)
        univ = universe if universe is not None else self.universe
        if univ is None:
            univ = tuple(sorted(vars_of(expr)))
            self.universe = univ
        missing = vars_of(expr) - set(univ)
        if missing:
            raise ValueError(
                f"variables {sorted(missing)} not in universe {univ}")
        return self._decide(expr, univ)

    def decide(self, expr, universe=None) -> Result:
        return self.certify(expr, universe=universe)

    # -- recursion ----------------------------------------------------------
    def _decide(self, expr: Node, univ: Tuple[str, ...]) -> Result:
        key = (univ, expr)
        hit = self._memo.get(key)
        if hit is not None:
            return hit
        t0 = time.perf_counter()
        res = self._decide_uncached(expr, univ)
        res.elapsed = time.perf_counter() - t0
        self._memo[key] = res
        return res

    def _decide_uncached(self, expr: Node, univ: Tuple[str, ...]) -> Result:
        fn = truth_table(expr, univ)
        K = rho(expr)
        lb = lower_bound(fn)

        # ---- (1) universal lower-bound certificate ------------------------
        # rho(function) >= LB always, so K == LB proves K == rho(function).
        if K == lb:
            return Result(
                Verdict.MINIMAL, expr, expr, fn,
                f"ρ({to_str(expr)}) = {K} equals the universal lower bound "
                f"α+2β = {lb}; hence no smaller factored form exists.")

        if isinstance(expr, (Gnd, Lit)):
            # Unreachable for a sane universe (a literal always has LB == 1 == rho).
            return Result(
                Verdict.UNKNOWN, expr, expr, fn,
                f"degenerate leaf with cost {K} but lower bound {lb}.")

        # ---- (0) local equivalence-preserving folds ------------------------
        # simplify() never adds literals.  If it strictly reduces, the input
        # was redundantly built and hence not minimal.  If it rewrites with
        # the same literal count (e.g. 1∧a -> a), the decision reduces to the
        # simplified form.
        folded = simplify(expr)
        if rho(folded) < K:
            return Result(
                Verdict.NOT_MINIMAL, expr, folded, fn,
                f"local folding yields {to_str(folded)} with {rho(folded)} < {K} literals.")
        if folded != expr:
            sub = self._decide(folded, univ)
            return Result(
                sub.verdict, expr, sub.best, fn,
                f"equivalent to {to_str(folded)} after folding; " + sub.reason)

        L = expr.left
        R = expr.right

        # ---- (2) a non-minimal operand makes the whole non-minimal ---------
        cL = self._decide(L, univ)
        cR = self._decide(R, univ)
        if cL.verdict == Verdict.NOT_MINIMAL:
            new = simplify(type(expr)(cL.best, R))
            return Result(
                Verdict.NOT_MINIMAL, expr, new, fn,
                f"left operand has a smaller form "
                f"({to_str(cL.best)}, {rho(cL.best)} < {rho(L)}); "
                f"substitution gives {rho(new)} < {K}.")
        if cR.verdict == Verdict.NOT_MINIMAL:
            new = simplify(type(expr)(L, cR.best))
            return Result(
                Verdict.NOT_MINIMAL, expr, new, fn,
                f"right operand has a smaller form "
                f"({to_str(cR.best)}, {rho(cR.best)} < {rho(R)}); "
                f"substitution gives {rho(new)} < {K}.")

        supL = vars_of(L)
        supR = vars_of(R)

        # ---- (3) disjoint-support composition -----------------------------
        # If supports are disjoint, rho(f∘g) = rho(f) + rho(g) (Wang Lemma
        # 3.5.2).  At this point both operands may be constants only if they
        # were already folded in step (0); so the lemma applies.
        if not (supL & supR):
            if cL.verdict == Verdict.MINIMAL and cR.verdict == Verdict.MINIMAL:
                return Result(
                    Verdict.MINIMAL, expr, expr, fn,
                    f"disjoint supports {sorted(supL)} ∩ {sorted(supR)} = ∅; "
                    f"by composition ρ = ρ(left) + ρ(right) = "
                    f"{cL.cost} + {cR.cost} = {K}.")

        # ---- (4) Shannon-split merge certificate --------------------------
        shared = supL & supR
        if shared:
            x = sorted(shared)[0]
        else:
            ess = essential_vars(fn)
            x = sorted(ess)[0] if ess else None

        if x is not None:
            h0 = cofactor(fn, x, 0)
            h1 = cofactor(fn, x, 1)
            E0 = simplify(type(expr)(cofactor_expr(L, x, 0),
                                     cofactor_expr(R, x, 0)))
            E1 = simplify(type(expr)(cofactor_expr(L, x, 1),
                                     cofactor_expr(R, x, 1)))
            c0 = self._decide(E0, univ)
            c1 = self._decide(E1, univ)
            w = shannon_join(x, c0.best, c1.best, h0, h1)
            total = rho(w)
            if total < K:
                return Result(
                    Verdict.NOT_MINIMAL, expr, w, fn,
                    f"Shannon split on {x} reconstructs {to_str(w)} "
                    f"with {total} < {K} literals.")

        # ---- (5) exact global fallback (bounded) --------------------------
        if self.exact:
            try:
                found = self._global_search(fn, K - 1)
            except BudgetExceeded:
                return Result(
                    Verdict.UNKNOWN, expr, expr, fn,
                    f"exact search exceeded budget; cannot certify below {K}.")
            if found is not None:
                return Result(
                    Verdict.NOT_MINIMAL, expr, found, fn,
                    f"exhaustive search found {to_str(found)} "
                    f"with {rho(found)} < {K} literals.")
            return Result(
                Verdict.MINIMAL, expr, expr, fn,
                f"exhaustive search up to {K - 1} literals found no "
                f"smaller equivalent factored form.")

        return Result(
            Verdict.UNKNOWN, expr, expr, fn,
            f"cost {K} is above the lower bound {lb} and no inductive "
            f"certificate closed the gap (cross-boundary Boolean division "
            f"would be required).")

    # -- exact search -------------------------------------------------------
    def _global_search(self, fn: BoolFunc, max_leaves: int) -> Optional[Node]:
        key = ("gs", fn.vars, fn.tt, max_leaves)
        hit = self._memo.get(key)
        if hit is not None:
            return hit
        res = self._global_search_uncached(fn, max_leaves)
        self._memo[key] = res
        return res

    def _global_search_uncached(self, fn: BoolFunc, max_leaves: int) -> Optional[Node]:
        if fn.tt == 0:
            return G0
        if fn.tt == fn.mask:
            return G1
        if max_leaves < 1:
            return None
        univ = fn.vars
        lits = tuple(Lit(v, neg) for v in univ for neg in (False, True))
        used = 0
        for k in range(1, max_leaves + 1):
            shapes = leaf_shapes(k)
            est = len(shapes) * (len(lits) ** k)
            if used + est > self.search_budget:
                raise BudgetExceeded()
            for shape in shapes:
                for assignment in product(lits, repeat=k):
                    built = _fill(shape, assignment)
                    used += 1
                    if truth_table(built, univ).tt == fn.tt:
                        return simplify(built)
        return None


def render_result(res: Result) -> str:
    """Human-readable single-result report."""
    lines = [
        f"input   : {to_str(res.expr)}",
        f"rho     : {res.input_cost} literals",
        f"verdict : {res.verdict.value}",
        f"reason  : {res.reason}",
        f"time    : {res.elapsed * 1e3:.3f} ms",
    ]
    if res.verdict == Verdict.NOT_MINIMAL:
        lines.append(f"smaller : {to_str(res.best)}  ({res.cost} literals)")
    elif res.verdict == Verdict.MINIMAL:
        lines.append(f"certified minimum literal count: {res.cost}")
    return "\n".join(lines)


def certify(expr, *, universe=None, exact=False, search_budget=500_000) -> Result:
    """Convenience wrapper.

    Examples
    --------
    >>> certify("(a ∧ ¬b) ∨ (¬a ∧ b)").verdict.value
    'MINIMAL'
    >>> r = certify("(a ∨ b) ∧ (a ∨ c)")
    >>> r.verdict.value, to_str(r.best)
    ('NOT_MINIMAL', '(a ∨ (b ∧ c))')
    """
    c = Certifier(universe=universe, exact=exact, search_budget=search_budget)
    return c.certify(expr)