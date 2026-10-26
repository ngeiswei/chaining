;; Tests for anf-map.metta.

;; Load the code under test
!(import! &self ./anf-map.metta)

;; Import and enable tabling library (2x faster)
!(import! &self (library lib_tabling))
!(tabled (bc $ab $rb $budget $query))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;; ;;
;; ;; Backward chainer tests ;; ;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;; ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Output to input Processing ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test co2i1
!(test
  (co2i1 Nil)
  Nil)
!(test
  (co2i1 (Cons ⊤ (Cons $x Nil)))
  (Cons ⊤ (Cons $y Nil)))
!(test
  (co2i1 (Cons ⊥ Nil))
  (Cons $y Nil))

;; Test co2i2
!(test
  (co2i2 Nil Nil)
  Nil)
!(test
  (co2i2 (Cons ⊤ (Cons ⊥ Nil)) (Cons ⊥ (Cons ⊤ Nil)))
  (Cons ⊤ (Cons ⊥ Nil)))
!(test
  (co2i2 (Cons $x Nil) (Cons ⊤ Nil))
  (Cons $y Nil))
!(test
  (co2i2 (Cons ⊥ Nil) (Cons ⊥ Nil))
  (Cons $y Nil))

;; Test eo2i1
!(test
  (eo2i1 Nil)
  Nil)
!(test
  (eo2i1 (Cons ⊤ (Cons ⊥ (Cons $x Nil))))
  (Cons $y1 (Cons $y2 (Cons $y3 Nil))))

;; Test eo2i2
!(test
  (eo2i2 Nil Nil)
  Nil)
!(test
  (eo2i2 (Cons ⊤ (Cons ⊥ Nil)) (Cons ⊤ (Cons ⊤ Nil)))
  (Cons ⊥ (Cons ⊤ Nil)))
!(test
  (eo2i2 (Cons $x Nil) (Cons ⊤ Nil))
  (Cons $y Nil))

;;;;;;;;;;;;;;;;;;;;;;;
;; Nullary synthesis ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; Define empty axiom and rule base
!(bind! &ab0 (new-space))
!(add-atom &ab0 (: tet (≗ map 𝕋 (Cons 0 Nil) (Cons ⊤ Nil))))
!(add-atom &ab0 (: feb (≗ map 𝔽 (Cons 0 Nil) (Cons ⊥ Nil))))

;; Test constant synthesis of 𝕋 given one data point
!(test
  (bc &ab0 (MkBudget 1 1) (: $prf (≗ map $pred (Cons 0 Nil) (Cons ⊤ Nil))))
  (, (MkBudget 0 0) (: tet (≗ map 𝕋 (Cons 0 Nil) (Cons ⊤ Nil)))))

;; Test constant synthesis of 𝔽 given one data point
!(test
  (bc &ab0 (MkBudget 1 1) (: $prf (≗ map $pred (Cons 0 Nil) (Cons ⊥ Nil))))
  (, (MkBudget 0 0) (: feb (≗ map 𝔽 (Cons 0 Nil) (Cons ⊥ Nil)))))

;;;;;;;;;;;;;;;;;;;;;
;; Unary synthesis ;;
;;;;;;;;;;;;;;;;;;;;;

;; Define axiom base
!(bind! &ab1 (new-space))
!(add-atom &ab1 (: tet (≗ map 𝕋 (Cons 0 (Cons 1 Nil)) (Cons ⊤ (Cons ⊤ Nil)))))
!(add-atom &ab1 (: feb (≗ map 𝔽 (Cons 0 (Cons 1 Nil)) (Cons ⊥ (Cons ⊥ Nil)))))
!(add-atom &ab1 (: fᵢₒ (≗ map f (Cons 0 (Cons 1 Nil)) (Cons ⊥ (Cons ⊤ Nil)))))

;; Test unary synthesis of f given two data points
!(test
  (bc &ab1 (MkBudget 1 1) (: $prf (≗ map $pred
                                     (Cons 0 (Cons 1 Nil))
                                     (Cons ⊥ (Cons ⊤ Nil)))))
  (, (MkBudget 0 0) (: fᵢₒ (≗ map f
                              (Cons 0 (Cons 1 Nil))
                              (Cons ⊥ (Cons ⊤ Nil))))))

;; Test unary synthesis of (¬ f) given two data points
!(test
  (bc &ab1 (MkBudget 3 2) (: $prf (≗ map $pred
                                     (Cons 0 (Cons 1 Nil))
                                     (Cons ⊤ (Cons ⊥ Nil)))))
  (, (MkBudget 0 0)
     (: (ee fᵢₒ tet) (≗ map (⊻ f 𝕋)
                        (Cons 0 (Cons 1 Nil))
                        (Cons ⊤ (Cons ⊥ Nil))))))
