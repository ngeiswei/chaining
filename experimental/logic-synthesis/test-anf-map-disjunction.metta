;; Disjunction test for anf-map.metta
;;
;; The goal of this test is to have bc *infer* an expression for the
;; disjunction of the N input features f1, ..., fN.  Disjunction here
;; means: True when at least one of the Fi's is True, False when they
;; are all False.  The features are encoded in the natural way,
;; fi(x) = (bit (i-1) of x), over the domain x ∈ {0, ..., 2^N - 1}.
;;
;; Note that the disjunction over N features has a much longer
;; algebraic normal form than parity: its ANF is the exclusive
;; disjunction of the conjunction of *every* non-empty subset of the
;; features, that is
;;
;;   N=1: f1
;;   N=2: f1 ⊻ f2 ⊻ (f1 ∧ f2)
;;   N=3: f1 ⊻ f2 ⊻ f3 ⊻ (f1∧f2) ⊻ (f1∧f3) ⊻ (f2∧f3) ⊻ (f1∧f2∧f3)
;;
;; so the number of terms grows as 2^N - 1 while parity's grows as N.
;; N=2 is therefore the largest case that stays small, and N=3 already
;; needs a budget far beyond the one N=2 needs (see below).

;; Load the code under test
!(import! &self ./anf-map.metta)

;; Import and enable tabling library
!(import! &self (library lib_tabling))

;;;;;;;;;;;;;;;;;;;;;;
;; Hyper-parameters ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Number of input features (i.e. bits).  Features are named f1, f2,
;; ..., fN, and the domain is {0, 1, ..., 2^N - 1}.
(= (N) 3)

;; Search budget.  Reasonable choices, with the disjunction expression
;; bc finds:
;;
;; * N=1: (MkBudget 1 1) with solution:
;;
;;   - f1
;;
;; * N=2: (MkBudget 7 4) with solution:
;;
;;   - (⊻ f1 (⊻ f2 (∧ f1 f2)))
;;
;; * N=3: (MkBudget 23 8) with solution:
;;
;;   - (⊻ f1 (⊻ f2 (⊻ f3 (⊻ (∧ f1 f2) (⊻ (∧ f1 f3) (⊻ (∧ f1 (∧ f2 f3)) (∧ f2 f3)))))))
;;
;; * N=4: (MkBudget ? ?) with solution:
;;
;;   - TODO: try on bigger machine.
;;
(= (SIZE) 23)
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

;; disjunctionBit x n: disjunction of bits 0..n-1 of x.  Returns ⊤ if
;; at least one of them is set, ⊥ otherwise.
(= (disjunctionBit $x $n)
   (if (== $n 0)
       ⊥
       (if (== (getBit $x (#- $n 1)) 1)
           ⊤
           (disjunctionBit $x (#- $n 1)))))

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

;; disjunctionOutputList x n: the disjunction for all domain points
;; x, ..., 2^n - 1.
(= (disjunctionOutputList $x $n)
   (if (== $x (pow-math 2 $n))
       Nil
       (Cons (disjunctionBit $x $n)
             (disjunctionOutputList (#+ $x 1) $n))))

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

;; The query asks for a predicate whose map is the disjunction truth
;; table.
(= (buildDisjunctionQuery $n)
   (: $prf
      (≗ map $pred (inputList 0 $n) (disjunctionOutputList 0 $n))))

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
!(trace! (query (buildDisjunctionQuery (N))) ())

;; Run the chainer
!(once (bc &ab (MkBudget (SIZE) (DEPTH)) (buildDisjunctionQuery (N))))
