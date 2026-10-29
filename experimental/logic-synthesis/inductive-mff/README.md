# Inductive decision procedure for minimal factored forms

This directory contains a small, self-contained Python library that **decides
whether a Boolean factored form already has the minimum possible number of
literals** among all equivalent factored forms.  It is a *decision* procedure,
not a rewriting/minimization tool — although every `NOT_MINIMAL` verdict also
hands you a strictly smaller equivalent form as a certificate.

The input language is deliberately simple:

```
form     ::=  0 | 1 | literal | form '∨' form | form '∧' form
literal  ::=  VAR | '¬' VAR
```

`¬` appears only at the leaves (on literals), exactly as requested.  ASCII
aliases are accepted (`& * ·` for `∧`, `| +` for `∨`, `~ !` or a trailing `'`
for `¬`).

```
experimental/logic-synthesis/inductive-mff/
├── inductive_mff/
│   ├── __init__.py        # public API re-exports
│   ├── ast.py             # expression AST, parser, rho, simplify, cofactor
│   ├── boolfunc.py        # truth-table semantic oracle, alpha/beta, lower bound
│   └── certify.py         # the decision procedure
├── tests/
│   ├── test_ast.py
│   ├── test_boolfunc.py
│   └── test_certify.py
├── conftest.py            # puts the package on sys.path
├── pyproject.toml
└── README.md
```

No third-party dependencies.  Python ≥ 3.9.

---

## 1. What "minimal factored form" means here

A *factored form* is an `∧`/`∨` expression tree whose leaves are signed
literals (a variable or its negation).  Its cost is the **literal count**

```
rho(F) = number of leaves
```

and for a Boolean *function* `f` we write

```
rho(f) = min { rho(F) : F is a factored form and F ≡ f }.
```

`rho(F)` over a concrete form is trivial to compute.  `rho(f)` over the
function is the hard object.  The decision problem is:

> Given a factored form `F`, is `rho(F) = rho(f)` where `f` is the function
> of `F`?

Computing `rho(f)` (minimum factored-form size) is `Σ₂^P`-complete in general
(Buchfuhrer & Umans 2008/2011).  We do **not** claim to solve it in
polynomial time.  What we claim — and what the code demonstrates — is that a
decision procedure can be organised so that the expensive search is only
reached on the genuinely hard "interface", while a large class of inputs is
discharged by cheap **inductive certificates**.

---

## 2. The two pieces of machinery

### 2.1 The universal lower bound

For a function `f`, let

- `α(f)` = number of **essential unate** variables (the function is monotone
  in each such variable, up or down),
- `β(f)` = number of **binate** variables (the function depends on the
  variable in *both* polarities).

Then **every** factored form of `f` has at least

```
LB(f) = α(f) + 2β(f)
```

literals.

**Why.**  A factored form built only with `∧` and `∨` is monotone in any
variable that occurs in a single polarity; hence a binate variable must occur
at least twice (once positive, once negative), and an essential variable must
occur at least once.  Summing per variable gives the bound.  This is exactly
the lower-bound half of the Read-Polarity-Once (RPO) theory
(Callegaro et al., *SBCCI 2013*): equality `rho(f) = α + 2β` holds iff `f` is
RPO.

`α` and `β` are computed from the *function*, not the syntactic form, via
cofactor comparison — see `boolfunc.py`.

### 2.2 Disjoint-support composition (Wang's lemma)

If two functions have disjoint essential supports, `sup(f) ∩ sup(g) = ∅`, then
the minimum literal count is additive:

```
rho(f ∧ g) = rho(f) + rho(g)       rho(f ∨ g) = rho(f) + rho(g)
```

(Wang, *Algorithms for Multi-Level Logic Optimization*, Lemma 3.5.2; also
De Micheli §8.4.2).  This is the one genuine lever that lets a *composition*
inherit optimality from its parts.

### 2.3 Why a purely local rule is not complete

A tempting local rule is "minimal children + disjoint supports ⇒ minimal
composition".  It is **sound but incomplete**:

| `f` | `g` | `f ∧ g` | supports | `rho(f)+rho(g)` | `rho(f∧g)` |
|---|---|---|---|---|---|
| `a∨b` | `c∨d` | `(a∨b)(c∨d)` | disjoint | 4 | 4 ✔ |
| `a∨b` | `¬a∨c` | `(a∨b)(¬a∨c) = ac ∨ ¬a·b` | share `a` | 4 | 4 ✔ |
| `a∨b` | `a∨c` | `(a∨b)(a∨c) = a ∨ bc` | share `a` | 4 | **3** ✘ |

Row 2 is the trap: support *overlaps* yet equality still holds (consensus
cancels).  Row 3 is the payoff: overlap strictly *helps*.  Minimality at the
top node is therefore not a syntactic property of the children — deciding it
amounts to evaluating the shared interface, which is Boolean division in
disguise.

---

## 3. The decision procedure

`certify(F)` returns a `Result` with a three-valued verdict:

| verdict | meaning | certificate |
|---|---|---|
| `MINIMAL` | `rho(F) = rho(f)` | the proof (LB tight or composition) |
| `NOT_MINIMAL` | `rho(F) > rho(f)` | a strictly smaller equivalent form |
| `UNKNOWN` | neither certificate found | the remaining gap |

Every verdict is **sound**: `MINIMAL` is only returned when a lower bound is
proved equal to `rho(F)`; `NOT_MINIMAL` always carries an actual smaller form;
`UNKNOWN` is always honest.

The decision of an input `F` proceeds in five steps (see
`Certifier._decide_uncached` in `certify.py`):

### Step 0 — local folds

`simplify(F)` applies only equivalence-preserving, literal-count
non-increasing rewrites (`a∧0→0`, `a∨1→1`, `a∧a→a`, `a∨¬a→1`, ...).  If it
strictly reduces `F`, return `NOT_MINIMAL` with the folded form as witness.
If it rewrites with the same literal count (e.g. `1∧a → a`), the decision is
reduced to the folded form.  This step handles constants, idempotence and
complementary siblings and keeps the later steps free of degenerate constant
operands.

### Step 1 — the universal-lower-bound certificate

```
if rho(F) == LB(f):  return MINIMAL
```

Because `LB(f) ≤ rho(f) ≤ rho(F)` always, `rho(F) == LB(f)` proves
`rho(f) = rho(F)`.  This is a *proof*, not a search, and it is what certifies
all RPO-tight forms (unate sums-of-products, XOR, disjoint forms, ...).

### Step 2 — non-minimal operands

For `F = L ∘ R`, if either operand is known `NOT_MINIMAL`, replace it by its
smaller form.  The composition is strictly smaller and equivalent, so `F` is
`NOT_MINIMAL`.

### Step 3 — disjoint-support composition

If the syntactic supports of `L` and `R` are disjoint **and** both operands
are certified `MINIMAL`, then Wang's lemma gives

```
rho(f) = rho(L) + rho(R) = rho(F),
```

so return `MINIMAL`.

### Step 4 — Shannon-split merge certificate

For overlapping supports, pick a shared variable `x`, cofactor the two
operands, recombine via Shannon:

```
h  =  x'·h0 ∨ x·h1,       h0 = h|_{x=0},  h1 = h|_{x=1}
```

with the number of `x`-literals chosen from the cofactor functions:

| cofactors `h0`, `h1` | `x`-literals | reconstruction |
|---|---|---|
| `h0 ≡ h1` | 0 | `h0` (or `h1`) |
| `h0 ≡ 0` | 1 | `x ∧ w1` |
| `h1 ≡ 0` | 1 | `¬x ∧ w0` |
| `h0 ≡ 1` | 1 | `¬x ∨ w1` |
| `h1 ≡ 1` | 1 | `x ∨ w0` |
| otherwise (`x` binate) | 2 | `(¬x ∧ w0) ∨ (x ∧ w1)` |

where `w0`, `w1` are the best forms discovered for `h0`, `h1` by recursing on
the corresponding cofactored expressions.  If the reconstructed form `w` has
`rho(w) < rho(F)`, return `NOT_MINIMAL` with `w` as the certificate.

**This is the part that exploits the inductive hypothesis.**  The recursion
into `h0`, `h1` re-enters the whole procedure on strictly smaller functions;
disjoint subtrees are cut in O(1) by Steps 1 and 3, and only the shared
interface percolates up.

### Step 5 — exact global fallback (only when `exact=True`)

If Steps 1–4 left a gap, exhaustively enumerate ordered `∧`/`∨` binary trees
over the literals of the universe, in increasing leaf count, up to
`rho(F) − 1` leaves, checking functional equivalence.  If a smaller tree is
found, `NOT_MINIMAL`; if the enumeration completes without one, `MINIMAL`.
The search is bounded by `search_budget` candidate trees; on overflow it
degrades to `UNKNOWN` rather than lying.  This is complete for small enough
`rho(F)`, and it is precisely the `Σ₂^P`-hard core — no induction removes it.

---

## 4. Worked examples

Run these to see the procedure in action:

```python
from inductive_mff import certify, render_result

# MINIMAL by the lower-bound certificate (disjoint, unate):
print(render_result(certify("(a ∨ b) ∧ (c ∨ d)")))

# MINIMAL by the lower-bound certificate (RPO-tight binate, XOR):
print(render_result(certify("(a ∧ ¬b) ∨ (¬a ∧ b)")))

# NOT_MINIMAL by the Shannon-split merge (absorption / factoring):
print(render_result(certify("(a ∨ b) ∧ (a ∨ c)")))

# NOT_MINIMAL by local folding (idempotence):
print(render_result(certify("a ∧ a")))

# majority-3 in its 5-literal minimum form: inductively UNKNOWN ...
print(render_result(certify("(a ∧ (b ∨ c)) ∨ (b ∧ c)")))

# ... but the exact fallback closes the gap with a proof:
print(render_result(certify("(a ∧ (b ∨ c)) ∨ (b ∧ c)", exact=True)))
```

Actual outputs:

```
input   : ((a ∨ b) ∧ (c ∨ d))
rho     : 4 literals
verdict : MINIMAL
reason  : ρ(((a ∨ b) ∧ (c ∨ d))) = 4 equals the universal lower bound α+2β = 4; hence no smaller factored form exists.
certified minimum literal count: 4

input   : ((a ∧ ¬b) ∨ (¬a ∧ b))
rho     : 4 literals
verdict : MINIMAL
reason  : ρ(((a ∧ ¬b) ∨ (¬a ∧ b))) = 4 equals the universal lower bound α+2β = 4; hence no smaller factored form exists.
certified minimum literal count: 4

input   : ((a ∨ b) ∧ (a ∨ c))
rho     : 4 literals
verdict : NOT_MINIMAL
reason  : Shannon split on a reconstructs (a ∨ (b ∧ c)) with 3 < 4 literals.
smaller : (a ∨ (b ∧ c))  (3 literals)

input   : (a ∧ a)
rho     : 2 literals
verdict : NOT_MINIMAL
reason  : local folding yields a with 1 < 2 literals.
smaller : a  (1 literals)

input   : ((a ∧ (b ∨ c)) ∨ (b ∧ c))
rho     : 5 literals
verdict : UNKNOWN
reason  : cost 5 is above the lower bound 3 and no inductive certificate closed the gap (cross-boundary Boolean division would be required).

input   : ((a ∧ (b ∨ c)) ∨ (b ∧ c))
rho     : 5 literals
verdict : MINIMAL
reason  : exhaustive search up to 4 literals found no smaller equivalent factored form.
certified minimum literal count: 5
```

The **majority-3** example is the instructive one.  `α = 3, β = 0`, so
`LB = 3`, but the true minimum is `5` (`a(b∨c) ∨ bc`).  The gap `3 < 5` is
exactly the "cross-boundary interaction" that no per-variable Shannon split
can see, so the inductive procedure correctly reports `UNKNOWN`; the exact
search then proves minimality by exhaustion.  This is the honest signature of
the residual `Σ₂^P` hardness.

---

## 5. Soundness, completeness, complexity

**Soundness (all verdicts).**  `MINIMAL` is returned only on a lower-bound
proof (`rho == LB`) or the disjoint-composition theorem; `NOT_MINIMAL` only
with a concrete smaller equivalent form; `UNKNOWN` never asserts anything.

**Inductive pruning ⇔ average-case help.**  Steps 1 and 3 resolve a large
fraction of standard benchmarks (all unate/RPO forms, XOR/parity, disjoint
structures) with no search.  The recursion confines state-space explosion to
the shared-support interface.  The worst case remains exponential — that is
the `Σ₂^P`-completeness of minimum factoring, which no procedure can remove.

**Why no local rule suffices.**  Section 2.3's table shows the top `∧`/`∨`
node is minimal-or-not depending on cross-boundary consensus, not on the
children alone.  So the inductive hypothesis is a *pruning* instrument, not a
complete one, outside the restricted classes (read-once, DSD, RPO) where a
dedicated structural theorem supplies the missing lower bound.

---

## 6. API

```python
from inductive_mff import certify, Certifier, Verdict, render_result

r = certify("(a ∨ b) ∧ (a ∨ c)")          # parse + decide
r = certify(expr_ast)                       # or pass an AST node directly
r.verdict                                   # Verdict.MINIMAL / NOT_MINIMAL / UNKNOWN
r.input_cost                                # rho of the input expression
r.cost                                      # rho of r.best
r.best                                      # smaller equivalent form if NOT_MINIMAL
r.reason                                    # human-readable justification

# persistent, configurable certifier (memoised across calls):
c = Certifier(universe=("a", "b", "c"), exact=False, search_budget=500_000)
c.certify("a ∨ (b ∧ c)")
```

Useful re-exports: `parse`, `to_str`, `ascii_repr`, `rho`, `vars_of`,
`simplify`, `cofactor_expr`, `truth_table`, `BoolFunc`, `cofactor`, `eq`,
`is_zero`, `is_one`, `var_status`, `alpha_beta`, `lower_bound`,
`essential_vars`.

---

## 7. Running the tests

```
python3 -m unittest discover -s tests -v        # stdlib, no dependencies
# or, with pytest installed:
python3 -m pytest
```

The suite covers the parser, the semantic oracle (cofactor/classification),
and the decision procedure, including the three verdicts and the exact
fallback on the majority-3 boundary case.

---

## 8. Relation to the literature

- **Wang (UCB/ERL M89/50, 1989), De Micheli §8.4.2** — the disjoint-support
  additivity lemma used in Step 3.
- **Callegaro, Martins, Ribas, Reis, *SBCCI* 2013; Callegaro thesis (UFRGS
  2016) Ch. 4** — Read-Polarity-Once theory: the `α + 2β` bound is the RPO
  lower bound, and read-once / DSD composition give the structural classes
  where the induction closes every gap.
- **Buchfuhrer & Umans (2008/2011)** — minimum formula (and minimum factored
  form) is `Σ₂^P`-complete; the exact fallback is the witness.
- **Yoshida & Fujita (IPSJ T-SLDM 2011)** — exact minimum factoring via QBF
  (`∃C ∀V …`), the practical incarnation of the global fallback.

---

## 9. Limitations

- The semantic oracle is a **truth table** (`2^n` bits), so don't run this on
  more than ~15–20 variables.  It is a *reference semantics*; swap in a
  BDD/SAT package and the decision procedure is unchanged.
- `exact=True` enumerates all ordered binary `∧`/`∨` trees, feasible only for
  `rho(F) ≤ 5`-ish over ≤ 4 variables; it is bounded and degrades to
  `UNKNOWN`, never to a wrong answer.
- `NOT_MINIMAL.best` is *a* smaller form, not necessarily the minimum.
- `¬` is restricted to leaves, as specified; `¬(a ∨ b)` is rejected rather
  than silently De-Morganised.
