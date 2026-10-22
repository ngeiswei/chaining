# Logic Synthesis

Backward-chaining experiments to synthesize Boolean expressions in
various normal forms such as [algebraic normal
form](https://en.wikipedia.org/wiki/Algebraic_normal_form), given
partial or complete truth tables.

## Algebraic Normal Form (ANF)

### Representing truth table as product

#### Only search candidates that fit the truth table

In that experiment we attempt to reproduce a form of Inductive Logic
Programming (ILP) such that only candidate solutions that would be
able to fit the target truth table are searched in the first place.
It does not work as intended, as explained below.

The files of interest are [anf-prod.metta](anf-prod.metta) and
[test-anf-prof.metta](test-anf-prod.metta).  Within the query the
target truth table looks like

```
(: $prf (, (≗ $pred 0 ⊤)
        (, (≗ $pred 1 ⊤)
        (, (≗ $pred 2 ⊤)
           (≗ $pred 3 ⊥)))))
```

At first the backward chainer will split in half the search space by
only considering candidate solutions that outputs `⊤` at `0`, but due
to how depth first search runs in the backward chainer it will
immediately explore all possible paths leading to candidate solutions
outputting `⊤` at `0` instead of progressively pruning the search
space by testing candidate solutions against the other input/output
pairs.  Due to that, even though they are only 16 candidates, since
ANF is canonical, the number of backward chainer calls rapidely
explodes.

See the table below:

| Full | Tabling | `trace!` calls | Wall time | Tests |
|---|---|---|---|---|
| disabled | enabled | 843 | 0.65 s | 16 ✅ / 0 ❌ |
| disabled | disabled | 432,430 | 5.20 s | 16 ✅ / 0 ❌ |
| enabled | enabled | 844 | 0.70 s | 16 ✅ / 0 ❌ |
| enabled | disabled | 1,641,628 | 17.96 s | 16 ✅ / 0 ❌ |

The number of `trace!` calls directly indicates the number of backward
chainer calls.  `Full` records whether `cebl`/`cebr` fully determine
the conjunction (i.e.  ground both operands of `(∧ $f $g)`):
`disabled` for the current code.  Leaving one `$f` or `$g`
undetermined makes checking for ANF more costly and lets go through
more candidates that would not end up in ANF in the end.  However it
is still cheaper to leave them undetermined because it saves the
backward chainer from deeping the search into one extra premise within
`cebl` and `cebr`.

In that test the maximum difficulty is binary synthesis.

#### Prebuild the candidates before fitting the truth table

In that experiment, since the candidate space is very small, due to
being represented in ANF, the backward chainer first build the set of
candidates, then confront them to the target truth table.

The files of interest are
[anf-prod-prebuild.metta](anf-prod-prebuild.metta) and
[test-anf-prod-prebuild.metta](test-anf-prod-prebuild.metta).

All the ANF check is moved to a unary parameterized type `ANF`.  Now
the query looks like

```
(: $prf (, (ANF $pred)
        (, (≗ $pred 0 ⊤)
        (, (≗ $pred 1 ⊤)
        (, (≗ $pred 2 ⊤)
           (≗ $pred 3 ⊥))))))
```

For a maximum difficulty of binary synthesis we get the following
results:

| Tabling | `trace!` calls | Wall time | Tests |
|---|---|---|---|
| enabled | 623 | 0.73 s | 16 ✅ / 0 ❌ |
| disabled | 13,919 | 0.87 s | 16 ✅ / 0 ❌ |

which in terms of number of backward chainer calls is considerably
better than [test-anf-prod.metta](test-anf-prod.metta).

For a maximum difficulty of ternary synthesis we get the following
results:

| Tabling | `trace!` calls | Wall time | Tests |
|---|---|---|---|
| enabled | 1,941 | 0.79 s | 17 ✅ / 0 ❌ |
| disabled | 162,634 | 2.54 s | 17 ✅ / 0 ❌ |
| enabled | 0 | 0.66 s | 17 ✅ / 0 ❌ |
| disabled | 0 | 1.02 s | 17 ✅ / 0 ❌ |

To see how far we can do we create an even parity problem synthesis
parameterized by the number of input features.  At 4 features, the
search space of candidates in ANF is only 4096, but at 5 features it
climbs to 4294967296 which should be intractable.
