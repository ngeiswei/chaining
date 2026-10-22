;; Test anf.metta

;; Import anf.metta
!(import! &self ./anf.metta)

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
