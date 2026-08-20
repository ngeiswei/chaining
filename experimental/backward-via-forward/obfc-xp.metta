;; Backward via forward chaining.  It works by forwadly generating
;; hypothetical truths (and their associated proof abstractions)
;; instead of absolute truths (and their associated proofs), then,
;; still going forward, by applying these hypothetical truths to the
;; axioms to reach absolute truths.  The idea being that only
;; hypothetical truth proving given theorems are produced and nothing
;; else.
;;
;; Hypothetical truths are produced using dedicated combinators.
;;
;; By combining the bluebird and blackbird
;; [combinators](https://hackage.haskell.org/package/data-aviary-0.4.0/docs/src/Data-Aviary-Birds.html)
;; one can apply modus ponens backward while doing forward chaining.
;;
;; The blackbird operator, B₁, can be used to create a specialized
;; rule to expand modus ponens backward on the first argument of any
;; abstract proof:
;;
;; mpⁱ = (λ z ((B₁ z) mp))
;;
;; with type signature
;;
;; (-> (-> $b $c) (-> (→ $a $b) (-> $a $c)))
;;
;; or in Haskell
;;
;; (b -> c) -> ((→ a b) -> a -> c)
;;
;; meaning this rule can turn any abstract proof of type (b -> c) into
;; am abstract proof of type (→ a b) -> a -> c.  In other words b is
;; replaced by (→ a b) -> a, i.e. a monus ponens expansion on the
;; first argument.
;;
;; Then the bluebird can be used to move this specialized rule to
;; expand modus ponens backward to any argument of any abstract proof:
;;
;; (. mpⁱ) to expand the second argument, (. (. mpⁱ)) to expand the
;; third argument, etc.
;;
;; For more naming conventions of combinators, see
;; https://wiki.xxiivv.com/site/logic.html

;; Disable co-unification
!(translatePredicate (set_prolog_flag occurs_check True))

;;;;;;;;;;;;;;;;;;;;;
;; ;;;;;;;;;;;;;;; ;;
;; ;; Functions ;; ;;
;; ;;;;;;;;;;;;;;; ;;
;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;
;; Reduction ;;
;;;;;;;;;;;;;;;

;; Reduce proofs containing mpⁱ into proofs containing mp.  Comment
;; For instance
;;
;; ((((mpⁱ (mpⁱ I)) ax₂) ax₁) ax₁)
;;
;; reduces to
;;
;; (mp (mp ax₂ ax₁) ax₁)
;;
;; If MeTTa could automatically curry, such implementation would
;; merely look like
;;
;; (= (mpⁱ $f) (B₁ $f mp))
;; (= (B₁ $f $g $x $y) ($f ($g $x $y)))
;; (= (I $x) $x)
;;
;; which, by-passing B₁, simplifies to
;;
;; (= (mpⁱ $f $x $y) ($f (mp $x $y)))
;; (= (I $x) $x)
;;
;; How it does so we have to implement it as a separate function,
;; reduce-proof.

;; Reduce (I $x) to $x
;; (: reduce-I (-> $a (Maybe $a)))
(= (reduce-I $term)
   (case $term
     ((($i $x) (if (== $i I) (Just $x) Nothing))
      ($_ Nothing))))

;; Test reduce-I
!(test
  (reduce-I (I ax₁))
  (Just ax₁))

;; Reduce (((mpⁱ $f) $x) $y) to ($f (mp $x $y))
;; (: reduce-mpⁱ (-> $a (Maybe $a)))
(= (reduce-mpⁱ $term)
   (case $term
     ((((($m $f) $x) $y) (if (== $m mpⁱ) (Just ($f (mp $x $y))) Nothing))
      ($_ Nothing))))

;; Test reduce-mpⁱ
!(test
  (reduce-mpⁱ (((mpⁱ I) ax₂) ax₁))
  (Just (I (mp ax₂ ax₁))))
!(test
  (reduce-mpⁱ (((mpⁱ (mpⁱ I)) ax₂) ax₁))
  (Just ((mpⁱ I) (mp ax₂ ax₁))))
!(test
  (reduce-mpⁱ (((mpⁱ I) (mp ax₂ ax₁)) ax₁))
  (Just (I (mp (mp ax₂ ax₁) ax₁))))

;; Reduce proof
;; (: reduce-proof (-> $a $a))
(= (reduce-proof $term)
   (case (get-metatype $term)
     (;; Base cases
      (Symbol $term)
      (Grounded $term)
      (Variable $term)
      (Expression
       (if (== $term ())
           ()
           ;; Recusive steps
           (case $term
             ;; Unary application
             ((($f $g) (let* (($νf (reduce-proof $f))
                              ($νg (reduce-proof $g)))
                         (if (and (== $νf $f) (== $νg $g))
                             ;; $f and $g are already reduced,
                             ;; try to match them to an known reduction rule
                             (case (reduce-I $term)
                               (((Just $r) (reduce-proof $r))
                                (Nothing
                                 (case (reduce-mpⁱ $term)
                                   (((Just $r) (reduce-proof $r))
                                    ;; No known reduction rule,
                                    ;; Return as it is
                                    (Nothing ($f $g)))))))
                             (reduce-proof ($νf $νg)))))
              ($else $else))))))))

;; Test reduce-proof
!(test
  (reduce-proof (((mpⁱ I) ax₂) ax₁))
  (mp ax₂ ax₁))
!(test
  (reduce-proof ((((mpⁱ (mpⁱ I)) ax₂) ax₁) ax₁))
  (mp (mp ax₂ ax₁) ax₁))

;; Reduce typeof relationship
(= (reduce-typeof (: $x $a)) (: (reduce-proof $x) $a))

;; Test reduce-typeof
;; impid
!(test
  (reduce-typeof (: (((mpⁱ I) ax₂) ax₁) (→ (→ 𝜑 𝜓) (→ 𝜑 𝜑))))
  (: (mp ax₂ ax₁) (→ (→ 𝜑 𝜓) (→ 𝜑 𝜑))))
;; loowoz
!(test
  (reduce-typeof (: ((((mpⁱ (((mpⁱ (mpⁱ ((mpⁱ ((mpⁱ (mpⁱ (((mpⁱ ((mpⁱ (mpⁱ I)) ax₂)) ax₁) ax₂))) ax₂)) ax₁))) ax₂) ax₂)) ax₁) ax₁) ax₁) (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))
  (: (mp (mp ax₂ (mp ax₁ ax₂)) (mp (mp ax₂ (mp ax₁ (mp (mp ax₂ ax₂) (mp ax₁ ax₁)))) ax₁)) (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))
!(test
  (reduce-typeof (: (((mpⁱ ((((mpⁱ ((mpⁱ (mpⁱ ((mpⁱ (mpⁱ (((mpⁱ ((mpⁱ (mpⁱ I)) ax₂)) ax₁) ax₂))) ax₂))) ax₂)) ax₁) ax₂) ax₁)) ax₁) ax₁) (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))
  (: (mp (mp ax₂ (mp ax₁ ax₂)) (mp (mp ax₂ (mp (mp ax₂ (mp ax₁ ax₂)) ax₁)) (mp ax₁ ax₁))) (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))
!(test
  (reduce-typeof (: ((((mpⁱ (((mpⁱ (mpⁱ (((mpⁱ ((mpⁱ (mpⁱ ((mpⁱ ((mpⁱ (mpⁱ I)) ax₂)) ax₁))) ax₂)) ax₁) ax₂))) ax₂) ax₂)) ax₁) ax₁) ax₁) (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))
  (: (mp (mp ax₂ (mp ax₁ (mp (mp ax₂ (mp ax₁ ax₂)) (mp (mp ax₂ ax₂) (mp ax₁ ax₁))))) ax₁) (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Optimized Forward Chainer ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(bind! &ofc-sol (new-space))

;; Optimized forward chainer meant to emulate backward chaining.  It
;; is optimized in the senses that
;;
;; 1. It uses proof size instead of depth (although in this proof
;; representation they are one and the same).
;;
;; 2. It prunes the search by ignoring exploring branches that may not
;; lead to non hypotheses in the final result.
;;
;; 3. It uses Number instead of Nat.
;;
;; 4. It is specialized for propositional calculus.
;; (: ofc (-> Number                    ; Maximum depth
;;            Number                    ; Hypotheses count
;;            $b                        ; Target query
;;            $b                        ; Source query
;;            $b))
(= (ofc $depth $hypcnt $tgt (: $x $a))
   (if (< 0 $hypcnt)
       ;; Recursive steps
       (if (and (< 0 $depth) (<= $hypcnt $depth))
           (progn
            ;; (add-atom &ofc-sol (sol $depth $hypcnt (: $x $a)))
            (ofc-rec (- $depth 1) (- $hypcnt 1) $tgt (: $x $a)))
           (empty))
       ;; Base case
        (let (: $x $a) $tgt
             (progn
              ;; (add-atom &ofc-sol (sol $depth $hypcnt (: $x $a)))
              (: $x $a)))))

;; Recursive steps (note that depth and hypcnt have already been
;; decremented) Specialized application given abstraction
(= (ofc-rec $depth_dec $hypcnt_dec $tgt
            (: $f (-> (→ $𝜑 (→ $𝜓 $𝜑)) $b)))
   (ofc $depth_dec $hypcnt_dec $tgt (: ($f ax₁) $b)))
(= (ofc-rec $depth_dec $hypcnt_dec $tgt
            (: $f (-> (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒))) $b)))
   (ofc $depth_dec $hypcnt_dec $tgt (: ($f ax₂) $b)))
(= (ofc-rec $depth_dec $hypcnt_dec $tgt
            (: $f (-> (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑)) $b)))
   (ofc $depth_dec $hypcnt_dec $tgt (: ($f ax₃) $b)))
;; Specialized application given argument of mpⁱ
(= (ofc-rec $depth_dec $hypcnt_dec $tgt (: $f (-> $b $c)))
   (ofc $depth_dec (+ $hypcnt_dec 2) $tgt (: (mpⁱ $f) (-> (→ $a $b) (-> $a $c)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Optimized backward chainer via forward chaining ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Backward via forward chaining
(: (obfc (-> Number                     ; Maximum depth
             $b                         ; Query
             $b)))
(= (obfc $depth (: $x $a))
   (ofc $depth 1 (: $x $a) (: I (-> $a $a))))

;;;;;;;;;;;;;;;;
;; ;;;;;;;;;; ;;
;; ;; Main ;; ;;
;; ;;;;;;;;;; ;;
;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test optimized depth-first search backward chaining via forward chaining ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To enable trace (which is convenient to compare with the MORK
;; version), comment out (add-atom &ofc-sol ...)  in ofc.  Then
;; display it with !(get-atoms &ofc-sol).  When collecting resulting
;; times when indexing sol instances, results are tagged ws which
;; stands for *with sol*.

;; ;; Exhausively generate all proofs of certain sizes
;; !(obfc 1 (: $x $a))
;; !(obfc 3 (: $x $a))
;; !(obfc 5 (: $x $a))
;; !(obfc 7 (: $x $a))
;; !(obfc 9 (: $x $a))
;; !(obfc 11 (: $x $a)) ; 5523, 0.457s
;; !(obfc 13 (: $x $a)) ; 35064, 2.905s
;; !(obfc 15 (: $x $a)) ; 233681, 19.622s
;; !(obfc 17 (: $x $a)) ; 1591750, 196.30s

;; ;; impid (Implied Identity)
;; !(obfc 3 (: $x (→ (→ 𝜑 𝜓) (→ 𝜑 𝜑))))

;; ;; id (PeTTa=0.105s, PeTTa-ws=0.103s)
;; !(obfc 5 (: $x (→ 𝜑 𝜑)))

;; ;; pm2.43 (PeTTa=0.107s, PeTTa-ws=0.111s)
;; !(obfc 7 (: $x (→ (→ 𝜑 (→ 𝜑 𝜓)) (→ 𝜑 𝜓))))

;; ;; 2a1
;; !(obfc 7 (: $x (→ 𝜑 (→ 𝜓 (→ 𝜒 𝜑)))))

;; ;; imim2
;; !(obfc 7 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜑) (→ 𝜒 𝜓)))))

;; jarr (PeTTa=0.129s, PeTTa-ws=1.695s, MeTTaScript-ws=3.660s)
!(obfc 13 (: $x (→ (→ (→ 𝜑 𝜓) 𝜒) (→ 𝜓 𝜒))))

;; ;; pm2.27 (PeTTa=0.129s, PeTTa-ws=1.660s)
;; !(obfc 13 (: $x (→ 𝜑 (→ (→ 𝜑 𝜓) 𝜓))))

;; ;; imim1 (PeTTa=0.267s, PeTTa-ws=12.045s, MeTTaScript-ws=22.920s)
;; !(obfc 15 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜒)))))

;; ;; loowoz (PeTTa=9.230s, PeTTa-ws=?)
;; !(obfc 19 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))

;; ;; pm2.83 (PeTTa=59m13.337s)
;; !(obfc 25 (: $x (→ (→ 𝜑 (→ 𝜓 𝜒)) (→ (→ 𝜑 (→ 𝜒 𝜃)) (→ 𝜑 (→ 𝜓 𝜃))))))

;; ;; loolin (PeTTa=49m32.599s)
;; !(obfc 25 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜓 𝜑)) (→ 𝜓 𝜑))))

;; NEXT: determine depths

;; ;; imim12 (?)
;; !(obfc 25 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜃) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜃))))))

;; ;; peirceroll
;; !(obfc 26 (: $x (→ (→ (→ (→ 𝜑 𝜓) 𝜑) 𝜑) (→ (→ (→ 𝜑 𝜓) 𝜒) (→ (→ 𝜒 𝜑) 𝜑)))))

;; ;; pm2.86
;; !(obfc 26 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ 𝜑 (→ 𝜓 𝜒)))))

;; ;; Output the solution space
;; !(get-atoms &ofc-sol)
