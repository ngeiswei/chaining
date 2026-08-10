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
;; The blackbird operator can be used to create a specialized rule to
;; expand modus ponens backward on the first argument of any abstract
;; proof:
;;
;; mpⁱ = (λ z ((.: z) mp))
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

;; Reduce proofs with mpⁱ into equivalent proofs with mp
;; NEXT: implement

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
       ;; (: $x $a)))
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
;; display it with !(get-atoms &ofc-sol)

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

;; ;; id
;; !(obfc 5 (: $x (→ 𝜑 𝜑)))

;; ;; pm2.43
;; !(obfc 7 (: $x (→ (→ 𝜑 (→ 𝜑 𝜓)) (→ 𝜑 𝜓))))

;; ;; 2a1
;; !(obfc 7 (: $x (→ 𝜑 (→ 𝜓 (→ 𝜒 𝜑)))))

;; ;; imim2 (82ms)
;; !(obfc 7 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜑) (→ 𝜒 𝜓)))))

;; jarr (100ms)
!(obfc 13 (: $x (→ (→ (→ 𝜑 𝜓) 𝜒) (→ 𝜓 𝜒))))

;; ;; pm2.27
;; !(obfc 13 (: $x (→ 𝜑 (→ (→ 𝜑 𝜓) 𝜓))))

;; ;; imim1 (200ms)
;; !(obfc 15 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜒)))))

;; ;; loowoz (5.761s)
;; !(obfc 19 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))

;; ;; pm2.83 (37m40.783s)
;; !(obfc 25 (: $x (→ (→ 𝜑 (→ 𝜓 𝜒)) (→ (→ 𝜑 (→ 𝜒 𝜃)) (→ 𝜑 (→ 𝜓 𝜃))))))

;; ;; loolin (32m17.697s)
;; !(obfc 26 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜓 𝜑)) (→ 𝜓 𝜑))))

;; NEXT: determine depths

;; ;; imim12 (?)
;; !(obfc 25 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜃) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜃))))))

;; ;; peirceroll
;; !(obfc 26 (: $x (→ (→ (→ (→ 𝜑 𝜓) 𝜑) 𝜑) (→ (→ (→ 𝜑 𝜓) 𝜒) (→ (→ 𝜒 𝜑) 𝜑)))))

;; ;; pm2.86
;; !(obfc 26 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ 𝜑 (→ 𝜓 𝜒)))))
