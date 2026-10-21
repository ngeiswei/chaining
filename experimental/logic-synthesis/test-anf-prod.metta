;; Tests for anf-prod.metta

;; Load the code under test
!(import! &self ./anf-prod.metta)

;; Import memoization library
!(import! &self (library lib_memo))

;; ;; Enable memoization for bc
;; !(memoize bc)
;; !(config-memoize (unique-limit 10000) (strategy wtinylfu) (size-limit 5))

;;;;;;;;;;;;;;;;;;
;; ;;;;;;;;;;;; ;;
;; ;; Syntax ;; ;;
;; ;;;;;;;;;;;; ;;
;;;;;;;;;;;;;;;;;;

;; Test isConjunctionInductiveANF
!(test
  (isConjunctionInductiveANF (∧ f g))
  True)
!(test
  (isConjunctionInductiveANF (∧ $f g))
  True)
!(test
  (isConjunctionInductiveANF (∧ f $g))
  True)
!(test
  (isConjunctionInductiveANF (∧ $f 𝔽))
  False)
!(test
  (isConjunctionInductiveANF (∧ $f 𝕋))
  False)

;; Test isInductiveANF
!(test
  (isInductiveANF (∧ f g))
  True)
!(test
  (isInductiveANF (∧ f $g))
  True)
!(test
  (isInductiveANF (∧ $f g))
  True)
!(test
  (isInductiveANF (∧ $f 𝔽))
  False)
!(test
  (isInductiveANF (∧ $f 𝕋))
  False)

;; Test isANF
!(test
  (isANF 𝔽)
  True)
!(test
  (isANF 𝕋)
  True)
!(test
  (isANF f)
  True)
!(test
  (isANF (∧ f g))
  True)
!(test
  (isANF (∧ f (∧ g h)))
  True)
!(test
  (isANF (∧ (∧ g h) f))
  False)
!(test
  (isANF (∧ 𝔽 f))
  False)
!(test
  (isANF (∧ 𝕋 f))
  False)
!(test
  (isANF (∧ f 𝔽))
  False)
!(test
  (isANF (∧ f 𝕋))
  False)
!(test
  (isANF (⊻ f g))
  True)
!(test
  (isANF (⊻ f (⊻ g h)))
  True)
!(test
  (isANF (⊻ (⊻ g h) f))
  False)
!(test
  (isANF (⊻ f (∧ g h)))
  True)
!(test
  (isANF (⊻ f 𝔽))
  False)
!(test
  (isANF (⊻ 𝔽 f))
  False)
!(test
  (isANF (⊻ f 𝕋))
  True)
!(test
  (isANF (⊻ 𝕋 f))
  False)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;; ;;
;; ;; Backward chainer tests ;; ;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;; ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;
;; Nullary synthesis ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; Define empty axiom and rule base
!(bind! &ab0 (new-space))
!(bind! &rb0 (new-space))

;; Test constant synthesis of 𝕋 given one data point
!(test
  (bc &ab0 &rb0 (MkBudget 1 1) (: $prf (≗ $pred 0 ⊤)))
  (, (MkBudget 0 0) (: tet (≗ 𝕋 0 ⊤))))

;; Test constant synthesis of 𝔽 given one data point
!(test
  (bc &ab0 &rb0 (MkBudget 1 1) (: $prf (≗ $pred 0 ⊥)))
  (, (MkBudget 0 0) (: feb (≗ 𝔽 0 ⊥))))

;;;;;;;;;;;;;;;;;;;;;
;; Unary synthesis ;;
;;;;;;;;;;;;;;;;;;;;;

;; Define axiom base
!(bind! &ab1 (new-space))
!(add-atom &ab1 (: f₀ (≗ f 0 ⊥)))
!(add-atom &ab1 (: f₁ (≗ f 1 ⊤)))

;; Define rule base
!(bind! &rb1 (new-space))

;; Test unary synthesis of f given one data point
!(test
  (sort-atom (collapse (bc &ab1 &rb1 (MkBudget 1 1) (: $prf (≗ $pred 0 ⊥)))))
  (sort-atom
   ((, (MkBudget 0 0) (: f₀ (≗ f 0 ⊥)))
    (, (MkBudget 0 0) (: feb (≗ 𝔽 0 ⊥))))))
!(test
  (sort-atom (collapse (bc &ab1 &rb1 (MkBudget 1 1) (: $prf (≗ $pred 1 ⊤)))))
  (sort-atom
   ((, (MkBudget 0 0) (: f₁ (≗ f 1 ⊤)))
    (, (MkBudget 0 0) (: tet (≗ 𝕋 1 ⊤))))))

;; Test unary synthesis of f given two data points
!(test
  (bc &ab1 &rb1 (MkBudget 3 2) (: $prf (, (≗ $pred 0 ⊥)
                                          (≗ $pred 1 ⊤))))
  (, (MkBudget 0 0) (: (, f₀ f₁) (, (≗ f 0 ⊥)
                                    (≗ f 1 ⊤)))))

;; Test unary synthesis of (¬ f) given one data point
!(test
  (sort-atom (collapse (bc &ab1 &rb1 (MkBudget 3 2) (: $prf (≗ $pred 0 ⊤)))))
  (sort-atom
   ((, (MkBudget 2 1) (: tet (≗ 𝕋 0 ⊤)))
    (, (MkBudget 0 0) (: (eetr f₀ tet) (≗ (⊻ f 𝕋) 0 ⊤))))))
!(test
  (sort-atom (collapse (bc &ab1 &rb1 (MkBudget 3 2) (: $prf (≗ $pred 1 ⊥)))))
  (sort-atom
   ((, (MkBudget 2 1) (: feb (≗ 𝔽 1 ⊥)))
    (, (MkBudget 0 0) (: (eebt f₁ tet) (≗ (⊻ f 𝕋) 1 ⊥))))))

;; Test unary synthesis of (¬ f) given two data points
!(test
  (bc &ab1 &rb1 (MkBudget 7 3) (: $prf (, (≗ $pred 0 ⊤)
                                          (≗ $pred 1 ⊥))))
  (, (MkBudget 0 0)
     (: (, (eetr f₀ tet) (eebt f₁ tet))
        (, (≗ (⊻ f 𝕋) 0 ⊤) (≗ (⊻ f 𝕋) 1 ⊥)))))

;;;;;;;;;;;;;;;;;;;;;;
;; Binary synthesis ;;
;;;;;;;;;;;;;;;;;;;;;;

;; NEXT
