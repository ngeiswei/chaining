;; Tests for anf-prod.metta

;; Load the code under test
!(import! &self ./anf-prod-prebuild.metta)

;; ;; Import memoization library (2x slower)
;; !(import! &self (library lib_memo))
;; ;; Enable memoization for bc
;; !(memoize bc)
;; !(config-memoize (unique-limit 10000) (strategy wtinylfu) (size-limit 5))

;; Import and enable tabling library (2x faster)
!(import! &self (library lib_tabling))
!(tabled (bc $ab $rb $budget $query))

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

;; Test that 𝕋 is in ANF
!(test
  (bc &ab0 $rb0 (MkBudget 1 1) (: $prf (ANF 𝕋)))
  (, (MkBudget 0 0) (: tanf (ANF 𝕋))))

;; Test that 𝔽 is in ANF
!(test
  (bc &ab0 $rb0 (MkBudget 1 1) (: $prf (ANF 𝔽)))
  (, (MkBudget 0 0) (: fanf (ANF 𝔽))))

;; Test constant synthesis of 𝕋 given one data point
!(test
  (bc &ab0 &rb0 (MkBudget 3 2) (: $prf (, (ANF $pred) (≗ $pred 0 ⊤))))
  (, (MkBudget 0 0) (: (, tanf tet) (, (ANF 𝕋) (≗ 𝕋 0 ⊤)))))

;; Test constant synthesis of 𝔽 given one data point
!(test
  (bc &ab0 &rb0 (MkBudget 3 2) (: $prf (, (ANF $pred) (≗ $pred 0 ⊥))))
  (, (MkBudget 0 0) (: (, fanf feb) (, (ANF 𝔽) (≗ 𝔽 0 ⊥)))))

;;;;;;;;;;;;;;;;;;;;;
;; Unary synthesis ;;
;;;;;;;;;;;;;;;;;;;;;

;; Define axiom base
!(bind! &ab1 (new-space))
!(add-atom &ab1 (: fₐ (ANF f)))
!(add-atom &ab1 (: f₀ (≗ f 0 ⊥)))
!(add-atom &ab1 (: f₁ (≗ f 1 ⊤)))

;; Define rule base
!(bind! &rb1 (new-space))

;; Test unary synthesis of f given one data point
!(test
  (sort-atom
   (collapse
    (bc &ab1 &rb1 (MkBudget 3 2) (: $prf (, (ANF $pred)
                                            (≗ $pred 0 ⊥))))))
  (sort-atom
   ((, (MkBudget 0 0) (: (, fₐ f₀) (, (ANF f) (≗ f 0 ⊥))))
    (, (MkBudget 0 0) (: (, fanf feb) (, (ANF 𝔽) (≗ 𝔽 0 ⊥)))))))
!(test
  (sort-atom
   (collapse
    (bc &ab1 &rb1 (MkBudget 3 2) (: $prf (, (ANF $pred)
                                            (≗ $pred 1 ⊤))))))
  (sort-atom
   ((, (MkBudget 0 0) (: (, fₐ f₁) (, (ANF f) (≗ f 1 ⊤))))
    (, (MkBudget 0 0) (: (, tanf tet) (, (ANF 𝕋) (≗ 𝕋 1 ⊤)))))))

;; Test unary synthesis of f given two data points
!(test
  (bc &ab1 &rb1 (MkBudget 5 2) (: $prf (, (ANF $pred)
                                       (, (≗ $pred 0 ⊥)
                                          (≗ $pred 1 ⊤)))))
  (, (MkBudget 0 0) (: (, fₐ (, f₀ f₁))
                       (, (ANF f)
                       (, (≗ f 0 ⊥)
                          (≗ f 1 ⊤))))))

;; Test unary synthesis of (¬ f) given one data point
!(test
  (sort-atom
   (collapse
    (bc &ab1 &rb1 (MkBudget 7 3) (: $prf (, (ANF $pred)
                                            (≗ $pred 0 ⊤))))))
  (sort-atom
   ((, (MkBudget 0 0)
       (: (, (eanf fₐ tanf) (eetr f₀ tet))
          (, (ANF (⊻ f 𝕋)) (≗ (⊻ f 𝕋) 0 ⊤))))
    (, (MkBudget 4 1) (: (, tanf tet) (, (ANF 𝕋) (≗ 𝕋 0 ⊤)))))))
!(test
  (sort-atom
   (collapse
    (bc &ab1 &rb1 (MkBudget 7 3) (: $prf (, (ANF $pred)
                                            (≗ $pred 1 ⊥))))))
  (sort-atom
   ((, (MkBudget 0 0)
       (: (, (eanf fₐ tanf) (eebt f₁ tet))
          (, (ANF (⊻ f 𝕋)) (≗ (⊻ f 𝕋) 1 ⊥))))
    (, (MkBudget 4 1) (: (, fanf feb) (, (ANF 𝔽) (≗ 𝔽 1 ⊥)))))))

;; Test unary synthesis of (¬ f) given two data points
!(test
  (bc &ab1 &rb1 (MkBudget 11 3) (: $prf (, (ANF $pred)
                                        (, (≗ $pred 0 ⊤)
                                           (≗ $pred 1 ⊥)))))
  (, (MkBudget 0 0)
     (: (, (eanf fₐ tanf) (, (eetr f₀ tet) (eebt f₁ tet)))
        (, (ANF (⊻ f 𝕋))
        (, (≗ (⊻ f 𝕋) 0 ⊤)
           (≗ (⊻ f 𝕋) 1 ⊥))))))

;;;;;;;;;;;;;;;;;;;;;;
;; Binary synthesis ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Define axiom base
!(bind! &ab2 (new-space))
!(add-atom &ab2 (: fₐ (ANF f)))
!(add-atom &ab2 (: gₐ (ANF g)))
!(add-atom &ab2 (: f₀ (≗ f 0 ⊥)))
!(add-atom &ab2 (: f₁ (≗ f 1 ⊥)))
!(add-atom &ab2 (: f₂ (≗ f 2 ⊤)))
!(add-atom &ab2 (: f₃ (≗ f 3 ⊤)))
!(add-atom &ab2 (: g₀ (≗ g 0 ⊥)))
!(add-atom &ab2 (: g₁ (≗ g 1 ⊤)))
!(add-atom &ab2 (: g₂ (≗ g 2 ⊥)))
!(add-atom &ab2 (: g₃ (≗ g 3 ⊤)))

;; Define rule base
!(bind! &rb2 (new-space))

;; Test binary synthesis of (∧ f g) given one data point
!(test
  (sort-atom (collapse (bc &ab2 &rb2 (MkBudget 3 2)
                           (: $prf (, (ANF $pred) (≗ $pred 0 ⊥))))))
  (sort-atom
   ((, (MkBudget 0 0) (: (, fanf feb) (, (ANF 𝔽) (≗ 𝔽 0 ⊥))))
    (, (MkBudget 0 0) (: (, fₐ f₀) (, (ANF f) (≗ f 0 ⊥))))
    (, (MkBudget 0 0) (: (, gₐ g₀) (, (ANF g) (≗ g 0 ⊥)))))))
!(test
  (sort-atom (collapse (bc &ab2 &rb2 (MkBudget 3 2)
                           (: $prf (, (ANF $pred) (≗ $pred 3 ⊤))))))
  (sort-atom
   ((, (MkBudget 0 0) (: (, fₐ f₃) (, (ANF f) (≗ f 3 ⊤))))
    (, (MkBudget 0 0) (: (, gₐ g₃) (, (ANF g) (≗ g 3 ⊤))))
    (, (MkBudget 0 0) (: (, tanf tet) (, (ANF 𝕋) (≗ 𝕋 3 ⊤)))))))

;; Test binary synthesis of (∧ f g) given two data points
!(test
  (sort-atom (collapse (bc &ab2 &rb2 (MkBudget 5 2)
                           (: $prf (, (ANF $pred)
                                    (, (≗ $pred 0 ⊥)
                                       (≗ $pred 3 ⊤)))))))
  (sort-atom
   ((, (MkBudget 0 0) (: (, fₐ (, f₀ f₃)) (, (ANF f) (, (≗ f 0 ⊥) (≗ f 3 ⊤)))))
    (, (MkBudget 0 0) (: (, gₐ (, g₀ g₃)) (, (ANF g) (, (≗ g 0 ⊥) (≗ g 3 ⊤))))))))

;; Test binary synthesis of (∧ f g) given three data points
!(test
  (bc &ab2 &rb2 (MkBudget 7 2) (: $prf (, (ANF $pred)
                                       (, (≗ $pred 0 ⊥)
                                       (, (≗ $pred 1 ⊥)
                                          (≗ $pred 3 ⊤))))))
  (, (MkBudget 0 0) (: (, fₐ (, f₀ (, f₁ f₃)))
                       (, (ANF f)
                       (, (≗ f 0 ⊥)
                       (, (≗ f 1 ⊥)
                          (≗ f 3 ⊤)))))))

;; Test binary synthesis of (∧ f g) given four data points
!(test
  (sort-atom
   (collapse
    (bc &ab2 &rb2 (MkBudget 16 3) (: $prf (, (ANF $pred)
                                          (, (≗ $pred 0 ⊥)
                                          (, (≗ $pred 1 ⊥)
                                          (, (≗ $pred 2 ⊥)
                                             (≗ $pred 3 ⊤)))))))))
  (sort-atom
   ((, (MkBudget 0 0)
       (: (, (canf fₐ gₐ) (, (cebl f₀) (, (cebl f₁) (, (cebr g₂) (cet f₃ g₃)))))
          (, (ANF (∧ f g))
          (, (≗ (∧ f g) 0 ⊥)
          (, (≗ (∧ f g) 1 ⊥)
          (, (≗ (∧ f g) 2 ⊥)
             (≗ (∧ f g) 3 ⊤)))))))
    (, (MkBudget 0 0)
       (: (, (canf fₐ gₐ) (, (cebr g₀) (, (cebl f₁) (, (cebr g₂) (cet f₃ g₃)))))
          (, (ANF (∧ f g))
          (, (≗ (∧ f g) 0 ⊥)
          (, (≗ (∧ f g) 1 ⊥)
          (, (≗ (∧ f g) 2 ⊥)
             (≗ (∧ f g) 3 ⊤))))))))))

;; Test binary synthesis of (¬ (∧ f g)) given four data points
!(test
  (sort-atom
   (collapse
    (bc &ab2 &rb2 (MkBudget 26 4) (: $prf (, (ANF $pred)
                                          (, (≗ $pred 0 ⊤)
                                          (, (≗ $pred 1 ⊤)
                                          (, (≗ $pred 2 ⊤)
                                             (≗ $pred 3 ⊥)))))))))
  (sort-atom
   ((, (MkBudget 0 0)
       (: (, (eanf tanf (canf fₐ gₐ))
          (, (eetl tet (cebl f₀))
          (, (eetl tet (cebl f₁))
          (, (eetl tet (cebr g₂))
             (eebt tet (cet f₃ g₃))))))
          (, (ANF (⊻ 𝕋 (∧ f g)))
          (, (≗ (⊻ 𝕋 (∧ f g)) 0 ⊤)
          (, (≗ (⊻ 𝕋 (∧ f g)) 1 ⊤)
          (, (≗ (⊻ 𝕋 (∧ f g)) 2 ⊤)
             (≗ (⊻ 𝕋 (∧ f g)) 3 ⊥)))))))
    (, (MkBudget 0 0)
       (: (, (eanf tanf (canf fₐ gₐ))
          (, (eetl tet (cebr g₀))
          (, (eetl tet (cebl f₁))
          (, (eetl tet (cebr g₂))
             (eebt tet (cet f₃ g₃))))))
          (, (ANF (⊻ 𝕋 (∧ f g)))
          (, (≗ (⊻ 𝕋 (∧ f g)) 0 ⊤)
          (, (≗ (⊻ 𝕋 (∧ f g)) 1 ⊤)
          (, (≗ (⊻ 𝕋 (∧ f g)) 2 ⊤)
             (≗ (⊻ 𝕋 (∧ f g)) 3 ⊥))))))))))

;;;;;;;;;;;;;;;;;;;;;;;
;; Ternary synthesis ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; Define axiom base
!(bind! &ab3 (new-space))
!(add-atom &ab3 (: fₐ (ANF f)))
!(add-atom &ab3 (: gₐ (ANF g)))
!(add-atom &ab3 (: hₐ (ANF h)))
!(add-atom &ab3 (: f₀ (≗ f 0 ⊥)))
!(add-atom &ab3 (: f₁ (≗ f 1 ⊥)))
!(add-atom &ab3 (: f₂ (≗ f 2 ⊥)))
!(add-atom &ab3 (: f₃ (≗ f 3 ⊥)))
!(add-atom &ab3 (: f₄ (≗ f 4 ⊤)))
!(add-atom &ab3 (: f₅ (≗ f 5 ⊤)))
!(add-atom &ab3 (: f₆ (≗ f 6 ⊤)))
!(add-atom &ab3 (: f₇ (≗ f 7 ⊤)))
!(add-atom &ab3 (: g₀ (≗ g 0 ⊥)))
!(add-atom &ab3 (: g₁ (≗ g 1 ⊥)))
!(add-atom &ab3 (: g₂ (≗ g 2 ⊤)))
!(add-atom &ab3 (: g₃ (≗ g 3 ⊤)))
!(add-atom &ab3 (: g₄ (≗ g 4 ⊥)))
!(add-atom &ab3 (: g₅ (≗ g 5 ⊥)))
!(add-atom &ab3 (: g₆ (≗ g 6 ⊤)))
!(add-atom &ab3 (: g₇ (≗ g 7 ⊤)))
!(add-atom &ab3 (: h₀ (≗ h 0 ⊥)))
!(add-atom &ab3 (: h₁ (≗ h 1 ⊤)))
!(add-atom &ab3 (: h₂ (≗ h 2 ⊥)))
!(add-atom &ab3 (: h₃ (≗ h 3 ⊤)))
!(add-atom &ab3 (: h₄ (≗ h 4 ⊥)))
!(add-atom &ab3 (: h₅ (≗ h 5 ⊤)))
!(add-atom &ab3 (: h₆ (≗ h 6 ⊥)))
!(add-atom &ab3 (: h₇ (≗ h 7 ⊤)))

;; Define rule base
!(bind! &rb3 (new-space))

;; Test ternary synthesis of (⊻ f (∧ g h)) given eight data points
!(test
  (sort-atom
   (collapse
    (bc &ab3 &rb3 (MkBudget 47 4) (: $prf (, (ANF $pred)
                                          (, (≗ $pred 0 ⊥)
                                          (, (≗ $pred 1 ⊥)
                                          (, (≗ $pred 2 ⊥)
                                          (, (≗ $pred 3 ⊤)
                                          (, (≗ $pred 4 ⊤)
                                          (, (≗ $pred 5 ⊤)
                                          (, (≗ $pred 6 ⊤)
                                             (≗ $pred 7 ⊥)))))))))))))
  (sort-atom
   ((, (MkBudget 0 0)
       (: (, (eanf fₐ (canf gₐ hₐ))
             (, (eebb f₀ (cebl g₀))
             (, (eebb f₁ (cebl g₁))
             (, (eebb f₂ (cebr h₂))
             (, (eetr f₃ (cet g₃ h₃))
             (, (eetl f₄ (cebl g₄))
             (, (eetl f₅ (cebl g₅))
             (, (eetl f₆ (cebr h₆))
                (eebt f₇ (cet g₇ h₇))))))))))
          (, (ANF (⊻ f (∧ g h)))
          (, (≗ (⊻ f (∧ g h)) 0 ⊥)
          (, (≗ (⊻ f (∧ g h)) 1 ⊥)
          (, (≗ (⊻ f (∧ g h)) 2 ⊥)
          (, (≗ (⊻ f (∧ g h)) 3 ⊤)
          (, (≗ (⊻ f (∧ g h)) 4 ⊤)
          (, (≗ (⊻ f (∧ g h)) 5 ⊤)
          (, (≗ (⊻ f (∧ g h)) 6 ⊤)
             (≗ (⊻ f (∧ g h)) 7 ⊥)))))))))))
    (, (MkBudget 0 0)
       (: (, (eanf fₐ (canf gₐ hₐ))
             (, (eebb f₀ (cebl g₀))
             (, (eebb f₁ (cebl g₁))
             (, (eebb f₂ (cebr h₂))
             (, (eetr f₃ (cet g₃ h₃))
             (, (eetl f₄ (cebr h₄))
             (, (eetl f₅ (cebl g₅))
             (, (eetl f₆ (cebr h₆))
                (eebt f₇ (cet g₇ h₇))))))))))
          (, (ANF (⊻ f (∧ g h)))
          (, (≗ (⊻ f (∧ g h)) 0 ⊥)
          (, (≗ (⊻ f (∧ g h)) 1 ⊥)
          (, (≗ (⊻ f (∧ g h)) 2 ⊥)
          (, (≗ (⊻ f (∧ g h)) 3 ⊤)
          (, (≗ (⊻ f (∧ g h)) 4 ⊤)
          (, (≗ (⊻ f (∧ g h)) 5 ⊤)
          (, (≗ (⊻ f (∧ g h)) 6 ⊤)
             (≗ (⊻ f (∧ g h)) 7 ⊥)))))))))))
    (, (MkBudget 0 0)
       (: (, (eanf fₐ (canf gₐ hₐ))
             (, (eebb f₀ (cebr h₀))
             (, (eebb f₁ (cebl g₁))
             (, (eebb f₂ (cebr h₂))
             (, (eetr f₃ (cet g₃ h₃))
             (, (eetl f₄ (cebl g₄))
             (, (eetl f₅ (cebl g₅))
             (, (eetl f₆ (cebr h₆))
                (eebt f₇ (cet g₇ h₇))))))))))
          (, (ANF (⊻ f (∧ g h)))
          (, (≗ (⊻ f (∧ g h)) 0 ⊥)
          (, (≗ (⊻ f (∧ g h)) 1 ⊥)
          (, (≗ (⊻ f (∧ g h)) 2 ⊥)
          (, (≗ (⊻ f (∧ g h)) 3 ⊤)
          (, (≗ (⊻ f (∧ g h)) 4 ⊤)
          (, (≗ (⊻ f (∧ g h)) 5 ⊤)
          (, (≗ (⊻ f (∧ g h)) 6 ⊤)
             (≗ (⊻ f (∧ g h)) 7 ⊥)))))))))))
    (, (MkBudget 0 0)
       (: (, (eanf fₐ (canf gₐ hₐ))
             (, (eebb f₀ (cebr h₀))
             (, (eebb f₁ (cebl g₁))
             (, (eebb f₂ (cebr h₂))
             (, (eetr f₃ (cet g₃ h₃))
             (, (eetl f₄ (cebr h₄))
             (, (eetl f₅ (cebl g₅))
             (, (eetl f₆ (cebr h₆))
                (eebt f₇ (cet g₇ h₇))))))))))
          (, (ANF (⊻ f (∧ g h)))
          (, (≗ (⊻ f (∧ g h)) 0 ⊥)
          (, (≗ (⊻ f (∧ g h)) 1 ⊥)
          (, (≗ (⊻ f (∧ g h)) 2 ⊥)
          (, (≗ (⊻ f (∧ g h)) 3 ⊤)
          (, (≗ (⊻ f (∧ g h)) 4 ⊤)
          (, (≗ (⊻ f (∧ g h)) 5 ⊤)
          (, (≗ (⊻ f (∧ g h)) 6 ⊤)
             (≗ (⊻ f (∧ g h)) 7 ⊥))))))))))))))
