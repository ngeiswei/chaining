;; Parity bit test for anf-map.metta
;;
;; The goal of this test is to have bc *infer* an expression for the
;; parity bit of the N input features f1, ..., fN.  Parity here means:
;; True when an even number of Fi's are True, False when an odd number
;; are.  The features are encoded in the natural way, fi(x) =
;; (bit (i-1) of x), over the domain x ∈ {0, ..., 2^N - 1}.
;;
;; Unlike anf-prod-prebuild.metta, whose query is a conjunction of one
;; (≗ $pred x y) per data point, the anf-map chainer reasons about the
;; whole truth table at once, as a single (≗ map $pred $xs $ys) atom.
;; This file therefore populates the axiom base with map-shaped axioms
;; and builds a single map-shaped query, automatically from the single
;; hyper-parameter `(N)`, so that changing N only requires changing
;; that one place (plus the size/depth budget, see the table below).

;; Load the code under test
!(import! &self ./anf-map.metta)

;; Import and enable tabling library
!(import! &self (library lib_tabling))

;;;;;;;;;;;;;;;;;;;;;;
;; Hyper-parameters ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Number of input features (i.e. bits).  Features are named f1, f2,
;; ..., fN, and the domain is {0, 1, ..., 2^N - 1}.
(= (N) 4)

;; Search budget.  Reasonable choices, with the parity expression bc
;; finds:
;;
;; * N=1: (MkBudget 3 2) with solution:
;;
;;   - (⊻ f1 𝕋)
;;
;; * N=2: (MkBudget 5 3) with solution:
;;
;;   - (⊻ f1 (⊻ f2 𝕋))
;;
;; * N=3: (MkBudget 7 4) with solution:
;;
;;   - (⊻ f1 (⊻ f2 (⊻ f3 𝕋)))
;;
;; * N=4: (MkBudget 9 5) with solution:
;;
;;   - (⊻ f1 (⊻ f2 (⊻ f3 (⊻ f4 𝕋))))
;;
;; * N=5: (MkBudget 11 6) with solution:
;;
;;   - (⊻ f1 (⊻ f2 (⊻ f3 (⊻ f4 (⊻ f5 𝕋)))))
;;
;; When tabling is enabled, with enough RAM it can go until N=7.  For
;; that one may need to increase the stack and the table limit of
;; PeTTa, for instance:
;;
;; ```bash
;; export PETTA_STACK_LIMIT=32g
;; export PETTA_TABLE_LIMIT=32g
;; ```
;;
(= (SIZE) 9)
(= (DEPTH) 5)

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

;; parityOutputList x n: the parity bit for all domain points x, ...,
;; 2^n - 1.
(= (parityOutputList $x $n)
   (if (== $x (pow-math 2 $n))
       Nil
       (Cons (parityBit $x $n)
             (parityOutputList (#+ $x 1) $n))))

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

;; The query asks for a predicate whose map is the parity truth table.
(= (buildParityQuery $n)
   (: $prf
      (≗ map $pred (inputList 0 $n) (parityOutputList 0 $n))))

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
!(trace! (query (buildParityQuery (N))) ())

;; Run the chainer
!(bc &ab (MkBudget (SIZE) (DEPTH)) (buildParityQuery (N)))
