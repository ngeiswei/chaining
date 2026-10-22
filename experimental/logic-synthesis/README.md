# Logic Synthesis

Backward-chaining experiments to synthesize Boolean expressions in
various normal forms such as [algebraic normal
form](https://en.wikipedia.org/wiki/Algebraic_normal_form), given
partial or complete truth tables.

## Algebraic Normal Form (ANF)

### Representing truth table as product

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
| disabled | enabled | 843 | 0.65 s | 42 ✅ / 0 ❌ |
| disabled | disabled | 432,430 | 5.20 s | 42 ✅ / 0 ❌ |
| enabled | enabled | 844 | 0.70 s | 42 ✅ / 0 ❌ |
| enabled | disabled | 1,641,628 | 17.96 s | 42 ✅ / 0 ❌ |

`Full` records whether `cebl`/`cebr` fully determine the conjunction
(i.e.  ground both operands of `(∧ $f $g)`): `disabled` for the
current code.  Leaving one `$f` or `$g` undetermined makes checking
for ANF more costly and lets go through more candidates that would not
end up in ANF in the end.  However it is still cheaper to leave them
undetermined because it saves the backward chainer from deeping the
search into one extra premise within `cebl` and `cebr`.
