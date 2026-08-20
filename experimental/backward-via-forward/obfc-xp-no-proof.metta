;; Backward via forward chaining ignoring proofs on the model of
;; [obfc-xp-no-proof.mm2](obfc-xp-no-proof.mm2).

;; Disable co-unification
!(translatePredicate (set_prolog_flag occurs_check True))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Optimized Forward Chainer without Proof ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
(= (ofc $depth $hypcnt $tgt $a)
   (if (< 0 $hypcnt)
       ;; Recursive steps
       (if (and (< 0 $depth) (<= $hypcnt $depth))
           (progn
            ;; (add-atom &ofc-sol (sol $depth $hypcnt $a))
            (unique
             (ofc-rec (- $depth 1) (- $hypcnt 1) $tgt $a))
            )
           (empty))
       ;; Base case
        (let $a $tgt
             (progn
              ;; (add-atom &ofc-sol (sol $depth $hypcnt $a))
              $a))))

;; Recursive steps (note that depth and hypcnt have already been
;; decremented) Specialized application given abstraction
(= (ofc-rec $depth_dec $hypcnt_dec $tgt
            (-> (→ $𝜑 (→ $𝜓 $𝜑)) $b))
   (ofc $depth_dec $hypcnt_dec $tgt $b))
(= (ofc-rec $depth_dec $hypcnt_dec $tgt
            (-> (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒))) $b))
   (ofc $depth_dec $hypcnt_dec $tgt $b))
(= (ofc-rec $depth_dec $hypcnt_dec $tgt
            (-> (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑)) $b))
   (ofc $depth_dec $hypcnt_dec $tgt $b))
;; Specialized application given argument of mpⁱ
(= (ofc-rec $depth_dec $hypcnt_dec $tgt (-> $b $c))
   (ofc $depth_dec (+ $hypcnt_dec 2) $tgt (-> (→ $a $b) (-> $a $c))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Optimized backward chainer via forward chaining ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Backward via forward chaining
(: (obfc (-> Number                     ; Maximum depth
             $b                         ; Query
             $b)))
(= (obfc $depth $a)
   (ofc $depth 1 $a (-> $a $a)))

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

;; ;; impid (Implied Identity)
;; !(obfc 3 (→ (→ 𝜑 𝜓) (→ 𝜑 𝜑)))

;; ;; id
;; !(obfc 5 (→ 𝜑 𝜑))

;; ;; pm2.43
;; !(obfc 7 (→ (→ 𝜑 (→ 𝜑 𝜓)) (→ 𝜑 𝜓)))

;; ;; 2a1
;; !(obfc 7 (→ 𝜑 (→ 𝜓 (→ 𝜒 𝜑))))

;; ;; imim2
;; !(obfc 7 (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜑) (→ 𝜒 𝜓))))

;; jarr
!(obfc 13 (→ (→ (→ 𝜑 𝜓) 𝜒) (→ 𝜓 𝜒)))

;; ;; pm2.27
;; !(obfc 13 (→ 𝜑 (→ (→ 𝜑 𝜓) 𝜓)))

;; ;; imim1
;; !(obfc 15 (→ (→ 𝜑 𝜓) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜒))))

;; ;; loowoz
;; !(obfc 19 (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒))))

;; ;; pm2.83
;; !(obfc 25 (→ (→ 𝜑 (→ 𝜓 𝜒)) (→ (→ 𝜑 (→ 𝜒 𝜃)) (→ 𝜑 (→ 𝜓 𝜃)))))

;; ;; loolin
;; !(obfc 25 (→ (→ (→ 𝜑 𝜓) (→ 𝜓 𝜑)) (→ 𝜓 𝜑)))

;; ;; Output the solution space
;; !(get-atoms &ofc-sol)
