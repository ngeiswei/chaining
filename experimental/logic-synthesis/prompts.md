# Useful prompts for this porject

## Study PeTTa

Could you study PeTTa, a Prolog based MeTTa back-end?  You can find it at `~/Work/TrueAGI/PeTTa/run.sh`.

## Working folder

Please note that we are now under folder `~/Work/TrueAGI/chaining/experimental/logic-synthesis`.

## Bug

Could you find out why the last call of test-anf-prod.metta does not return the answer to the query `(: $prf (, (≗ $pred 0 ⊥) (≗ $pred 0 ⊤)))`?

## More problems

Could you add similar tests as ./experimental/logic-synthesis/anf-map-parity.metta using as target truth tables:
1. disjunction, where the output is true iff any one of its N intputs is true.
2. majority, where the output is true iff among N inputs the number of true inputs is strictly greater than half of N.
3. multiplex, where the output is true iff an N-bit binary address specifies one and exactly one wire out of 2^N wires.  In this case N is not the number of inputs, the number of inputs is then N + 2^N.
You do not need to test them being N=2, in fact for the multiplex problem, you do not even need to test it beyond N=1.
