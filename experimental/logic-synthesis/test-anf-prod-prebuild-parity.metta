;; Parity bit test for anf-prod-prebuild.metta
;;
;; The goal of this test is to have bc *infer* an expression for the
;; parity bit of the N input features f1, ..., fN.  Parity here means:
;; True when an even number of Fi's are True, False when an even
;; number are.  The features are encoded in the natural way, fi(x) =
;; (bit (i-1) of x), over the domain x ∈ {0, ..., 2^N - 1}.  This file
;; populates the knowledge base and builds the parity query
;; automatically from the single hyper-parameter `(paritySize)`, so
;; that changing N only requires changing that one place.

;; Load the code under test
!(import! &self ./anf-prod-prebuild.metta)

;; Import and enable tabling library
!(import! &self (library lib_tabling))

;;;;;;;;;;;;;;;;;;;;;;
;; Hyper-parameters ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Number of input features (i.e. bits).  Features are named f1, f2,
;; ..., fN, and the domain is {0, 1, ..., 2^N - 1}.
(= (N) 4)

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

;; parityBit x n: parity of bits 0..n-1 of x.  Returns ⊤ if the count
;; of set bits is even, ⊥ otherwise.
(= (parityBit $x $n)
   (if (== $n 0)
       ⊤
       (let* (($bit (== (getBit $x (#- $n 1)) 1))
              ($rest (parityBit $x (#- $n 1))))
         (if $bit
             (if (== $rest ⊥) ⊤ ⊥)
             $rest))))

;; atomicPredName i: "f1", "f2", ..., the name of the i-th input feature.
(= (atomicPredName $i) (atom_concat "f" $i))

;; Axiom name of the evaluation of atomic predicate fi at x.
;; Format: f{i}{(subscript x)}, e.g. f1₀, f2₃.
(= (atomicEvalAxiomName $i $x)
   (atom_concat (atom_concat "f" $i) (subscript $x)))

;; subscript x: decimal digits of x rendered with Unicode subscript
;; characters, e.g. 0 -> ₀, 12 -> ₁₂.
(= (subscriptDigit 0) ₀)
(= (subscriptDigit 1) ₁)
(= (subscriptDigit 2) ₂)
(= (subscriptDigit 3) ₃)
(= (subscriptDigit 4) ₄)
(= (subscriptDigit 5) ₅)
(= (subscriptDigit 6) ₆)
(= (subscriptDigit 7) ₇)
(= (subscriptDigit 8) ₈)
(= (subscriptDigit 9) ₉)

(= (subscript $x)
   (if (#< $x 10)
       (subscriptDigit $x)
       (atom_concat (subscript (#div $x 10)) (subscriptDigit (#mod $x 10)))))

;; fi(x) = (bit (i-1) of x)
(= (bitValueOfPred $i $x)
   (if (== (getBit $x (#- $i 1)) 1) ⊤ ⊥))

;;;;;;;;;;;;;;;;;;;;;
;; KB construction ;;
;;;;;;;;;;;;;;;;;;;;;

;; Add that atomic predicates f1, ..., fN are in ANF, such as
;;
;; (: f1ₐ (ANF f1))
(= (addAtomicPredANF $ab $i)
   (if (== $i 0)
       ()
       (let* (($pname (atomicPredName $i))
              ($aname (atom_concat $pname "ₐ"))
              ($_ (add-atom $ab (: $aname (ANF $pname)))))
         (addAtomicPredANF $ab (#- $i 1)))))

;; Add the truth value atom for fi at domain point x.
(= (addTruthAtom $ab $i $x)
   (let* (($y (bitValueOfPred $i $x))
          ($aname (atomicEvalAxiomName $i $x))
          ($pname (atomicPredName $i)))
     (add-atom $ab (: $aname (≗ $pname $x $y)))))

;; For fi, add truth value atoms at all x ∈ {0, ..., 2^N - 1}.
(= (addTruthAtomsForPred $ab $i $n $x)
   (if (== $x (pow-math 2 $n))
       ()
       (progn (addTruthAtom $ab $i $x)
              (addTruthAtomsForPred $ab $i $n (#+ $x 1)))))

;; Add truth value atoms for all F1, ..., FN.
(= (addAllTruthAtoms $ab $i $n)
   (if (== $i 0)
       ()
       (progn (addTruthAtomsForPred $ab $i $n 0)
              (addAllTruthAtoms $ab (#- $i 1) $n))))

;; Master driver: populate &ab with everything needed.
(= (populateAxiomBase $ab $n)
   (progn (addAtomicPredANF $ab $n)
          (addAllTruthAtoms $ab $n $n)))

;;;;;;;;;;;;;;;;;;;;
;; Query building ;;
;;;;;;;;;;;;;;;;;;;;

;; Build the left-leaning nested `,` of parity evaluations.
;; (buildParityQuery-rec $x $n $pred) =
;;   when x = 2^n - 1: (≗ $pred x (parityBit x n))
;;   otherwise:        (, (≗ $pred x (parityBit x n))
;;                         (buildParityQuery-rec (+ x 1) n $pred))
(= (buildParityQuery-rec $x $n $pred)
   (if (== $x (#- (pow-math 2 $n) 1))
       (≗ $pred $x (parityBit $x $n))
       (, (≗ $pred $x (parityBit $x $n))
          (buildParityQuery-rec (#+ $x 1) $n $pred))))

;; Like above but without needed to pass $pred.
(= (buildParityQuery $n) (: $prf
                            (, (ANF $pred)
                               (buildParityQuery-rec 0 $n $pred))))

;;;;;;;;;;;;;;
;; Run test ;;
;;;;;;;;;;;;;;

;; Enable tabling for bc
!(if (enableTabling)
     (tabled (bc $ab $rb $budget $query))
     (empty))

;; Populate kb
!(bind! &ab (new-space))
!(bind! &rb (new-space))
!(populateAxiomBase &ab (N))

;; Trace ab and query
!(trace! (ab (get-atoms &ab)) (empty))
!(trace! (query (buildParityQuery (N))) ())

;; Run the chainer to find every $pred over F1, ..., FN whose
;; evaluation matches the parity truth table.  Reasonable choices for
;; size and depth budgets are:
;;
;; * N=1: (MkBudget 11 3) with solution:
;;
;;   - (⊻ f1 𝕋)
;;
;; * N=2: (MkBudget 29 4) with solution:
;;
;;   - (⊻ f1 (⊻ f2 𝕋))
;;
;; * N=3: (MkBudget 71 5) with solution:
;;
;;   - (⊻ f1 (⊻ f2 (⊻ f3 𝕋)))
;;
;; * N=4: (MkBudget 169 6) with solution:
;;
;;   - (⊻ f1 (⊻ f2 (⊻ f3 (⊻ f4 𝕋))))
;;
;; * N=5: (MkBudget ? ?) with solution:
;;
;;   - ?
!(once
  (bc &ab &rb (MkBudget 169 6) (buildParityQuery (N))))
