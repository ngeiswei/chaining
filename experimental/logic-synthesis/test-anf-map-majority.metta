;; Majority test for anf-map.metta
;;
;; The goal of this test is to have bc *infer* an expression for the
;; majority of the N input features f1, ..., fN.  Majority here means:
;; True when strictly more than half of the Fi's are True, False
;; otherwise.  The features are encoded in the natural way,
;; fi(x) = (bit (i-1) of x), over the domain x ∈ {0, ..., 2^N - 1}.

;; Load the code under test
!(import! &self ./anf-map.metta)

;; Import and enable tabling library
!(import! &self (library lib_tabling))

;;;;;;;;;;;;;;;;;;;;;;
;; Hyper-parameters ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Number of input features (i.e. bits).  Features are named f1, f2,
;; ..., fN, and the domain is {0, 1, ..., 2^N - 1}.
(= (N) 5)

;; Search budget.  Reasonable choices, with the majority expression bc
;; finds:
;;
;; * N=1: (MkBudget 1 1) with solution:
;;
;;   - f1
;;
;; * N=2: (MkBudget 3 2) with solution:
;;
;;   - (∧ f1 f2)
;;
;; * N=3: (MkBudget 11 4)
;;
;;   - (⊻ (∧ f1 f2) (⊻ (∧ f1 f3) (∧ f2 f3)))
;;
;; * N=4: (MkBudget 31 7)
;;
;;   - (⊻ (∧ f1 (∧ f2 f3)) (⊻ (∧ f1 (∧ f2 f4)) (⊻ (∧ f1 (∧ f2 (∧ f3 f4))) (⊻ (∧ f1 (∧ f3 f4)) (∧ f2 (∧ f3 f4))))))
;;
;; * N=5: (MkBudget ? ?) with solution:
;;
;;   - TODO: try on bigger machine.
;;
(= (SIZE) 80)
(= (DEPTH) 10)

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

;; trueInputCount x n: number of bits 0..n-1 of x that are set, that is
;; the number of the N inputs fi(x) that are True.
(= (trueInputCount $x $n)
   (if (== $n 0)
       0
       (+ (getBit $x (#- $n 1))
          (trueInputCount $x (#- $n 1)))))

;; majorityBit x n: majority of bits 0..n-1 of x.  Returns ⊤ when
;; strictly more than half of them are set, ⊥ otherwise.
(= (majorityBit $x $n)
   (if (> (* 2 (trueInputCount $x $n)) $n) ⊤ ⊥))

;; atomicPredName i: "f1", "f2", ..., the name of the i-th input feature.
(= (atomicPredName $i) (atom_concat "f" $i))

;; inputList x n: the map inputs, i.e. (Cons x (Cons x+1 ... Nil)) for
;; all domain points x, ..., 2^n - 1.
(= (inputList $x $n)
   (if (== $x (pow-math 2 $n))
       Nil
       (Cons $x (inputList (#+ $x 1) $n))))

;; featureOutputList i x n: fi(x) for all domain points x, ..., 2^n - 1.
(= (featureOutputList $i $x $n)
   (if (== $x (pow-math 2 $n))
       Nil
       (Cons (if (== (getBit $x (#- $i 1)) 1) ⊤ ⊥)
             (featureOutputList $i (#+ $x 1) $n))))

;; majorityOutputList x n: the majority for all domain points
;; x, ..., 2^n - 1.
(= (majorityOutputList $x $n)
   (if (== $x (pow-math 2 $n))
       Nil
       (Cons (majorityBit $x $n)
             (majorityOutputList (#+ $x 1) $n))))

;; constantOutputList v x n: v repeated for all domain points.
(= (constantOutputList $v $x $n)
   (if (== $x (pow-math 2 $n))
       Nil
       (Cons $v (constantOutputList $v (#+ $x 1) $n))))

;;;;;;;;;;;;;;;;;;;;;
;; KB construction ;;
;;;;;;;;;;;;;;;;;;;;;

;; Add fi as a map over the whole domain, such as
;;
;; (: f1ₑ (≗ map f1 (Cons 0 ...) (Cons ⊥ ...)))
(= (addFeatureAxiom $ab $i $n)
   (let* (($pname (atomicPredName $i))
          ($aname (atom_concat $pname "ₑ"))
          ($xs (inputList 0 $n))
          ($ys (featureOutputList $i 0 $n)))
     (add-atom $ab (: $aname (≗ map $pname $xs $ys)))))

;; Add f1, ..., fN.
(= (addFeatureAxioms $ab $i $n)
   (if (== $i 0)
       ()
       (progn (addFeatureAxiom $ab $i $n)
              (addFeatureAxioms $ab (#- $i 1) $n))))

;; Add the two constant predicates 𝕋 and 𝔽 as maps over the domain.
(= (addConstantAxioms $ab $n)
   (let* (($xs (inputList 0 $n))
          ($tt (constantOutputList ⊤ 0 $n))
          ($ff (constantOutputList ⊥ 0 $n)))
     (progn (add-atom $ab (: tet (≗ map 𝕋 $xs $tt)))
            (add-atom $ab (: feb (≗ map 𝔽 $xs $ff))))))

;; Master driver: populate &ab with everything needed.
(= (populateAxiomBase $ab $n)
   (progn (addFeatureAxioms $ab $n $n)
          (addConstantAxioms $ab $n)))

;;;;;;;;;;;;;;;;;;;;
;; Query building ;;
;;;;;;;;;;;;;;;;;;;;

;; The query asks for a predicate whose map is the majority truth table.
(= (buildMajorityQuery $n)
   (: $prf
      (≗ map $pred (inputList 0 $n) (majorityOutputList 0 $n))))

;;;;;;;;;;;;;;
;; Run test ;;
;;;;;;;;;;;;;;

;; Enable tabling for bc
!(if (enableTabling)
     (tabled (bc $ab $budget $query))
     (empty))

;; Populate kb
!(bind! &ab (new-space))
!(populateAxiomBase &ab (N))

;; Trace ab and query
!(trace! (ab (get-atoms &ab)) (empty))
!(trace! (query (buildMajorityQuery (N))) ())

;; Run the chainer
!(once (bc &ab (MkBudget (SIZE) (DEPTH)) (buildMajorityQuery (N))))
