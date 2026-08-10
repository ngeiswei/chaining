# Emulating Backward Chaining via Forward Chaining

## Overview

Forward chaining starts from a truth to produce more truth.  Backward
chainging on the other hand starts from a hypothesis to produce more
hypotheses (and possibly turns them into truths if reaches axioms).

There is actually a way to reconsile both approaches.

It is been already known that backward chaining can emulate forward
chainging by formulating the query `(: (. $x AXIOM) $a)` where `AXIOM`
is the name of the axiom to start forward chaining from.  Since the
proof is constrained to start from a given axiom and the theorem,
`$a`, is completely unconstrained, the backward chainer will have no
other option than producing proofs starting from the given axiom, that
is going forward.

It turns out one can also emulate backward chaining with forward
chaining.  It is a bit more complicated than just formulating the
right query.  First, inference rules have to be inverted, using here
the blackbird combinator:

```
(: .: (-> (-> $c $d)
          (-> (-> $a (-> $b $c))
              (-> $a
                  (-> $b
                      $d)))))
```

For instance applying the backbird to modus ponens

```
(: mp (-> (→ $a $b)
          (-> $a
              $b)))
```

produces

```
(: mpⁱ (-> (-> $b $c)
           (-> (→ $a $b)
               (-> $a
                   $c))))
```

Note how the conclusion, `$c`, is preserved in the input and the
output of rule, this is what allows to emulate backward expansion
while going forward.

Second, the target query `(: $x THEOREM)` must be turn into a source
query provided to the forward chainer, as follows:

`(: $x (-> THEOREM THEOREM))`

Then the forward chainer will have the effect of either expanding
backward using `mpⁱ` or eliminating hypotheses using the axioms and
will eventually reach `(: PROOF THEOREM)` if such proof exists.

## Experiments

To establish a fair comparison, it is important that both the backward
chainer and the forward chainer emulating backward chaining explore
exactly the same spaces, or rather isomorphic spaces.  To do that the
following changes must be operated:

1. The backward chainer must set a limit on the size of the proof
   rather than its depth.  This is actually a very good change because
   the size of search space grows super exponentially with the maximum
   depth of the proof, while it grows at most exponentially with the
   maximum size of the proof.  This provides a finer parameter to
   control the size of the search space and can dramatically speed up
   the search.
2. Due to the way the forward chainer emulates backward chaining, the
   forward chainer can keep the maximum depth as control parameter but
   must add an extra pruning parameter based on the number of
   hypotheses currently expanded.  If that number is greater than the
   depth (or the size, as they are the same) of the proof, then such
   proof will never reach the target because it not have possibility
   to eliminate all hypotheses.  This condition is crutial and allows
   to speed up the forward chainer many fold, to reach near parity
   with the backward chainer it is trying to emulate.

### Comparing Emulated vs Regular Backward Chaining in MeTTa

We begin our comparison in MeTTa only, to hopefully measure the
overhead of emulating backward chaining using forward chaining and
nothing else.  Once this has been establish we will move to a MORK
implementation, but for now we remain inside MeTTa using PeTTa as
back-end.

The code can be found in [obfc-xp.metta](obfc-xp.metta) and
[obc-xp.metta](obc-xp.metta).  The main two chainer implementations
being compared are `obfc` which stands for Optimized Backward via
Forward Chainer, and `obc` which stands for Optimized Backward
Chainer.  Benchmarks of two types are conducted:

1. Over four exhaustive enumerations (all theorems and their proofs up
   to a certain size) of proof sizes, 11, 13, 15 and 17 respectively.
1. Over three theorems selected from the Metamath corpus with varying
   proof sizes, 15, 19 and 26 respectively.

The data obtained from these experiments have been compiled in
[regular-vs-emulated-petta-benchmark.csv](regular-vs-emulated-petta-benchmark.csv)
and are plotted below.

![Regular vs Emulated for Exhaustive Enumeration](plots/regular-vs-emulated-bc-all.png)
![Regular vs Emulated for Exhaustive Enumeration (Ratio)](plots/regular-vs-emulated-bc-all-ratio.png)

As indicated in the figure above the slowdown incurred by the
emulation for exhaustive enumeration of proofs and theorems ranges
from a bit over 1.05x to a bit under 1.4x.

![Regular vs Emulated for a Selection of Theorems](plots/regular-vs-emulated-bc-some.png)

![Regular vs Emulated for a Selection of Theorems (Ratio)](plots/regular-vs-emulated-bc-some-ratio.png)

As indicated in the figure above the slowdown incurred by the
emulation for a selection of theorems ranges from a bit over 1.4x to a
bit under 2x.  The factor seems to increase with the size of the
proof.  It is unclear however if the factor converges to a limit as
the size increases, or diverges to infinity.  Either way, we do not
see the trend as problematic because the sizes considered are already
quite high, 26, and even if it diverges it seems to be in a
logarithmic fashion.  In other words, the forward emulation of
backward chaining looks like it could be a competitive approach,
especially for rewriting systems like MORK, which we will study next.

### Comparing MORK Backward Emulation vs Regular MeTTa Backward Chaining

For comparing regular MeTTa backward chaining with MORK forward
chaining emulation, see [obfc-xp.mm2](obfc-xp.mm2).  Do not forget to
run [gen-peano.mm2](gen-peano.mm2) and [gen-lte.mm2](gen-lte.mm2) in
that order, to generate tables used by [obfc-xp.mm2](obfc-xp.mm2) and
[obc-xp.mm2](obc-xp.mm2).

So far the results are disappointing.  On jarr, the backward chaining
emulation via forward chaining on MM2 is 290x slower than direct
backward chaining on PeTTa (40.435s on MM2 vs 0.130s on PeTTa).  I
have tried a few things like simplifying arthimetic operations and
swapping arguments to speed up the MM2 implementation, but it is still
too slow.  Maybe I could try to replace arthimetic tables by pure
functions but I doubt it will make a substantial difference.

#### Faster variant: `obfc-xp-fast.mm2`

A structural rewrite of `obfc-xp.mm2` is available as
[obfc-xp-fast.mm2](obfc-xp-fast.mm2).  It runs roughly **2.3× to I2.5×
faster** than `obfc-xp.mm2` and produces identical results (obtained
by running [bench.sh](bench.sh)):

```
                          obfc-xp.mm2     obfc-xp-fast.mm2    speedup
jarr  (size 13)           ~0.34 s         ~0.14 s             2.4×
imim1 (size 15)           ~2.10 s         ~0.90 s             2.3×
loowoz (size 19, est.)    ~89 s           ~40 s               2.2×
```

(`bfc()` benchmark in MORK's `kernel/src/main.rs` runs jarr in
~0.1s, confirming that the simplified representation leaves little
headroom.)

The key changes from `obfc-xp.mm2` to `obfc-xp-fast.mm2` are:

1. **No `pure` sink in axiom/mpⁱ application.**  In `obfc-xp.mm2`
   each axiom application invokes the `pure` sink to compute the
   new `FLAG` (a precomputed `is_mpⁱ_expandable`).  That sink
   allocates a `PathMap<()>` and a 4 GiB buffer per call and walks
   the path tree on `finalize`, dominating the per-sol cost.
   `obfc-xp-fast.mm2` drops the `FLAG` field entirely.

2. **Hypothesis count derived from the budget.**  Instead of
   carrying `HYPCNT` in the sol tuple and gating `mpⁱ` via `FLAG`,
   the hypcnt is recovered at every iteration via cheap
   `(gte $ki $hi)` / `(inc $hi $shi)` table lookups.  This replaces
   the entire `=pure` flag precomputation mechanism.

3. **Single-conjunct axiom application exec.**  The axiom
   application pattern is reduced from three conjuncts
   `(decFn ...)` / `(sol ...)` / `(axiom ...)` to just `(sol ...)`,
   since the axiom constraint is bound in the inner exec's LHS via
   `(axiom $r $constraint)`.

4. **Plain integers for the budget countdown.**  Peano
   `(S (S ... Z))` structures and `toPeanoFn`/`fromPeanoFn`
   conversions are replaced by a direct integer representation and
   a precomputed `(dec N N-1)` / `(inc N N+1)` table.

5. **Self-contained.**  `gen-peano.mm2` and `gen-lte.mm2` are no
   longer needed — the dec/inc/lte/gte tables are inlined directly
   in the file (covering integers 0..26, sufficient for all
   propositional calculus theorems up to size 26).

The same structural insight is implemented as the `bfc()` benchmark
in MORK's `kernel/src/main.rs`, which is what motivated this
rewrite.  The only differences between `obfc-xp-fast.mm2` and
`bfc()` are notational: `→` for implication (vs `>` in `bfc`),
`mpⁱ` for mp-application (vs `M`), and theorem/proof wrapper `(C
...)` (same as `bfc`).
