;; Multiplex test for anf-map.metta
;;
;; The goal of this test is to have bc *infer* an expression for a
;; 2^N-to-1 multiplexer.  A multiplexer has an N-bit binary address and
;; 2^N data wires, and its output is the value of the single wire that
;; the address selects.  So the output is True when exactly the
;; addressed wire is True, and False when it is False -- whatever the
;; other wires say.
;;
;; Note that here N is *not* the number of inputs: the number of inputs
;; is N + 2^N, the N address bits plus the 2^N data wires.  The inputs
;; are encoded as the bits of the domain point x ∈ {0, ..., 2^(N+2^N)
;; - 1}, in the natural way:
;;
;;   - f1, ..., fN are the address bits, fi(x) = (bit (i-1) of x), i.e.
;;     the address of x is (bit (N-1) ... bit 0) of x;
;;
;;   - f(N+1), ..., f(N+2^N) are the data wires, wire j (0-indexed) is
;;     f(N+j+1) = (bit (N+j) of x);
;;
;; and the target is the value of the wire named by the address, i.e.
;; the bit (N + address(x)) of x.

;; Load the code under test
!(import! &self ./anf-map.metta)

;; Import and enable tabling library
!(import! &self (library lib_tabling))

;;;;;;;;;;;;;;;;;;;;;;
;; Hyper-parameters ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Width of the address (i.e. number of address bits).  The number of
;; inputs, and therefore the number of bits of a domain point, is
;; (M) = N + 2^N.
(= (N) 2)

;; Number of inputs of the multiplexer, and number of bits of a domain
;; point.
(= (M) (+ (N) (pow-math 2 (N))))

;; Search budget.  Reasonable choices, with the expression bc finds:
;;
;; * N=1: (MkBudget 9 4) with solution:
;;
;;   - (⊻ f2 (⊻ (∧ f1 f2) (∧ f1 f3)))
;;
;;   where f1 is the single address bit, f2 is the wire 0 (selected
;;   when the address is 0) and f3 is the wire 1 (selected when the
;;   address is 1).  Indeed the expression above is
;;   d0 ⊻ (a ∧ d0) ⊻ (a ∧ d1), that is d0 when a is ⊥ and d1 when a is
;;   ⊤.  (MkBudget 13 4) is enough as well.
;;
;; * N=2: (MkBudget ? ?)
;;
;;   - TODO: try on bigger machine.
;;
;; Unlike the parity test, this one really wants tabling: with
;; (enableTabling) disabled the same N=1 search did not finish in a
;; minute, while with it enabled the answer is found in under a second.
;;
(= (SIZE) 50)
(= (DEPTH) 8)

;; Enable tabling
(= (enableTabling) True)

;;;;;;;;;;;;;
;; Helpers ;;
;;;;;;;;;;;;;

;; getBit x i: i-th bit of integer x (returns 0 or 1, 0-indexed).
(= (getBit $x $i)
   (if (== $i 0)
       (#mod $x 2)
       (getBit (#div $x 2) (#- $i 1))))

;; addressValue x i n: the value of the n-bit address held in bits
;; 0..n-1 of x, accumulated over bits i..n-1.
(= (addressValue $x $i $n)
   (if (== $i $n)
       0
       (+ (* (getBit $x $i) (pow-math 2 $i))
          (addressValue $x (#+ $i 1) $n))))

;; multiplexBit x n: the multiplexer output for the domain point x with
;; an n-bit address.  The data bits start at bit n, so the addressed
;; wire is bit (n + address of x).
(= (multiplexBit $x $n)
   (if (== (getBit $x (#+ $n (addressValue $x 0 $n))) 1)
       ⊤
       ⊥))

;; atomicPredName i: "f1", "f2", ..., the name of the i-th input feature.
(= (atomicPredName $i) (atom_concat "f" $i))

;; inputList x m: the map inputs, i.e. (Cons x (Cons x+1 ... Nil)) for
;; all domain points x, ..., 2^m - 1.
(= (inputList $x $m)
   (if (== $x (pow-math 2 $m))
       Nil
       (Cons $x (inputList (#+ $x 1) $m))))

;; featureOutputList i x m: fi(x) for all domain points x, ..., 2^m - 1.
(= (featureOutputList $i $x $m)
   (if (== $x (pow-math 2 $m))
       Nil
       (Cons (if (== (getBit $x (#- $i 1)) 1) ⊤ ⊥)
             (featureOutputList $i (#+ $x 1) $m))))

;; multiplexOutputList x n m: the multiplexer output for all domain
;; points x, ..., 2^m - 1, for an n-bit address.
(= (multiplexOutputList $x $n $m)
   (if (== $x (pow-math 2 $m))
       Nil
       (Cons (multiplexBit $x $n)
             (multiplexOutputList (#+ $x 1) $n $m))))

;; constantOutputList v x m: v repeated for all domain points.
(= (constantOutputList $v $x $m)
   (if (== $x (pow-math 2 $m))
       Nil
       (Cons $v (constantOutputList $v (#+ $x 1) $m))))

;;;;;;;;;;;;;;;;;;;;;
;; KB construction ;;
;;;;;;;;;;;;;;;;;;;;;

;; Add fi as a map over the whole domain, such as
;;
;; (: f1ₑ (≗ map f1 (Cons 0 ...) (Cons ⊥ ...)))
;;
;; The number of features and the number of domain bits are both (M).
(= (addFeatureAxiom $ab $i $m)
   (let* (($pname (atomicPredName $i))
          ($aname (atom_concat $pname "ₑ"))
          ($xs (inputList 0 $m))
          ($ys (featureOutputList $i 0 $m)))
     (add-atom $ab (: $aname (≗ map $pname $xs $ys)))))

;; Add f1, ..., fM.
(= (addFeatureAxioms $ab $i $m)
   (if (== $i 0)
       ()
       (progn (addFeatureAxiom $ab $i $m)
              (addFeatureAxioms $ab (#- $i 1) $m))))

;; Add the two constant predicates 𝕋 and 𝔽 as maps over the domain.
(= (addConstantAxioms $ab $m)
   (let* (($xs (inputList 0 $m))
          ($tt (constantOutputList ⊤ 0 $m))
          ($ff (constantOutputList ⊥ 0 $m)))
     (progn (add-atom $ab (: tet (≗ map 𝕋 $xs $tt)))
            (add-atom $ab (: feb (≗ map 𝔽 $xs $ff))))))

;; Master driver: populate &ab with everything needed.
(= (populateAxiomBase $ab $m)
   (progn (addFeatureAxioms $ab $m $m)
          (addConstantAxioms $ab $m)))

;;;;;;;;;;;;;;;;;;;;
;; Query building ;;
;;;;;;;;;;;;;;;;;;;;

;; The query asks for a predicate whose map is the multiplexer truth
;; table of an n-bit address over m inputs.
(= (buildMultiplexQuery $n $m)
   (: $prf
      (≗ map $pred (inputList 0 $m) (multiplexOutputList 0 $n $m))))

;;;;;;;;;;;;;;
;; Run test ;;
;;;;;;;;;;;;;;

;; Enable tabling for bc
!(if (enableTabling)
     (tabled (bc $ab $budget $query))
     (empty))

;; Populate kb
!(bind! &ab (new-space))
!(populateAxiomBase &ab (M))

;; Trace ab and query
!(trace! (ab (get-atoms &ab)) (empty))
!(trace! (query (buildMultiplexQuery (N) (M))) ())

;; Run the chainer
!(once (bc &ab (MkBudget (SIZE) (DEPTH)) (buildMultiplexQuery (N) (M))))
