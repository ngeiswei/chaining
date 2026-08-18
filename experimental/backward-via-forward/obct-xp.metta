;; Optimized Backward Chainer with Maximum Proof Size and Trace.
;;
;; Derived from [obc-xp.metta](obc-xp.metta) with the addition of
;; forward trace to compare obfc and obc.so.  Also, by that token, it
;; provides the inverse of reduce-proof from
;; [obfc-xp.metta](obfc-xp.metta).

;; Disable co-unification
!(translatePredicate (set_prolog_flag occurs_check True))

;;;;;;;;;;;;;;;;;;
;; Sized Object ;;
;;;;;;;;;;;;;;;;;;

;; Associate a size to a term
(: Sized (-> $a Type))
(: MkSized (-> $n                       ; Size
               $a                       ; Object
               (Sized $a)))             ; Sized object

;; Access functions
(= (Sized.size (MkSized $s $x)) $s)
(= (Sized.object (MkSized $s $x)) $x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Optimized backward chainer with maximum proof size and trace ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Like obc but keep track of the trace.  For that it takes a pair
;;
;; (, (: THRM PRF) (c: ITHRM IPRF))
;;
;; and outputs
;;
;; (MkSized REMAINING_BUDGET (, (: THRM PRF) (c: ITHRM IPRF)))
;;
;; instead of
;;
;; taking (: THRM PRF) and outputting (MkSized REMAINING_BUDGET (: THRM PRF))
;;
;; It also prints the trace according to the format defined in
;; [obfc-xp-fast.mm2](obfc-xp-fast.mm2):
;;
;; (sol BUDGET HYPCNT (c: ITHRM IPRF))
;;
;; where:
;;
;; - BUDGET is the remaining proof size budget
;;
;; - HYPCNT is the number of hypotheses in the current ITHRM
;;
;; Other arguments are:
;;
;; - $budget for the remaining budget
;;
;; - $depth for the depth of the forward tracing (corresponding to
;;   BUDGET in sol)
;;
;; - $hypcnt for the hypotheses count of the forward tracing
(= (obct-gtz $budget $depth $hypcnt
             (, (c: (-> (→ $𝜑 (→ $𝜓 $𝜑)) $b) $o)
                (: ax₁ (→ $𝜑 (→ $𝜓 $𝜑)))))
   (trace! (sol (- $depth 1) (- $hypcnt 1) (c: $b ($o ax₁)))
   (MkSized 1 (, (c: $b ($o ax₁)) (: ax₁ (→ $𝜑 (→ $𝜓 $𝜑)))))))
(= (obct-gtz $budget $depth $hypcnt
             (, (c: (-> (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒))) $b) $o)
                (: ax₂ (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒))))))
   (trace! (sol (- $depth 1) (- $hypcnt 1) (c: $b ($o ax₂)))
   (MkSized 1 (, (c: $b ($o ax₂))
                 (: ax₂ (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒))))))))
(= (obct-gtz $budget $depth $hypcnt
             (, (c: (-> (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑)) $b) $o)
                (: ax₃ (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑)))))
   (trace! (sol (- $depth 1) (- $hypcnt 1) (c: $b ($o ax₃)))
   (MkSized 1 (, (c: $b ($o ax₃))
                 (: ax₃ (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑)))))))
(= (obct-gtz $budget $depth $hypcnt
             (, (c: (-> $b $c) $o)
                (: (mp $f $x) $b)))
   (trace! (sol (- $depth 1) (+ $hypcnt 1) (c: (-> (→ $a $b) (-> $a $c)) (mpⁱ $o)))
   (if (< 2 $budget) ; The budget must be at least 3, 1 for mp and 1
                     ; per premise
       (let* (;; Recurse on first premise with proof $f
              ((MkSized $fs (, (c: (-> $a $c) $no) (: $f (→ $a $b))))
               (obct-rec (- $budget 2) ; Remove 1 for mp and 1 for $x
                         (- $depth 1) ; Remove 1 for mpⁱ
                         (+ $hypcnt 1) ; Add 1 for mpⁱ
                         (, (c: (-> (→ $a $b) (-> $a $c)) (mpⁱ $o))
                            (: $f (→ $a $b)))))
              ;; Recurse on second premise with proof $x
              ((MkSized $xs (, (c: $c $nno) (: $x $a)))
               (obct-rec (- (- $budget 1) $fs) ; Remove 1 for mp and $fs for $f
                         (- (- $depth 1) $fs)  ; Remove 1 for mp and $fs for $f
                         $hypcnt               ; mpⁱ and $f cancel out
                         (, (c: (-> $a $c) $no)
                            (: $x $a)))))
         (MkSized (+ (+ $fs $xs) 1) (, (c: $c $nno) (: (mp $f $x) $b))))
       (empty))))
(= (obct-rec $budget $depth $hypcnt (, (c: $h $o) (: $x $a)))
   (trace! (sol $depth $hypcnt (c: $h $o))
   (if (< 0 $budget)
       (obct-gtz $budget $depth $hypcnt (, (c: $h $o) (: $x $a)))
       (empty))))

;; Entry point
(= (obct $s (: $x $a))
   (obct-rec $s $s 1 (, (c: (-> $a $a) I) (: $x $a))))

;;;;;;;;;;;;;;;
;; Test obct ;;
;;;;;;;;;;;;;;;

;; Exhausively generate all proofs of certain sizes
;; !(obct 1 (: $x $a))
;; !(obct 3 (: $x $a))
;; !(obct 5 (: $x $a))
;; !(obct 7 (: $x $a))
;; !(obct 9 (: $x $a))
;; !(obct 11 (: $x $a)) ; 5523, 0.391s
;; !(obct 13 (: $x $a)) ; 35064, 2.458s
;; !(obct 15 (: $x $a)) ; 233681, 18.471s
;; !(obct 17 (: $x $a)) ; 1591750, 142.83s

;; ;; impid (Implied Identity)
;; !(obct 3 (: $x (→ (→ 𝜑 𝜓) (→ 𝜑 𝜑))))

;; ;; id
;; !(obct 5 (: $x (→ 𝜑 𝜑)))

;; pm2.43
!(obct 7 (: $x (→ (→ 𝜑 (→ 𝜑 𝜓)) (→ 𝜑 𝜓))))

;; ;; 2a1
;; !(obct 7 (: $x (→ 𝜑 (→ 𝜓 (→ 𝜒 𝜑)))))

;; ;; imim2 (81ms)
;; !(obct 7 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜑) (→ 𝜒 𝜓))))

;; ;; jarr (90ms)
;; !(obct 13 (: $x (→ (→ (→ 𝜑 𝜓) 𝜒) (→ 𝜓 𝜒))))

;; ;; pm2.27
;; !(obct 13 (: $x (→ 𝜑 (→ (→ 𝜑 𝜓) 𝜓))))

;; ;; imim1 (140ms)
;; !(test
;;   (obct 15 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜒)))))
;;   (MkSized 15 (: (mp (mp ax₂ (mp ax₁ (mp ax₂ (mp (mp ax₂ (mp ax₁ ax₂)) ax₁)))) ax₁) (→ (→ 𝜑 𝜓) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜒))))))

;; ;; loowoz (0.891s)
;; !(obct 19 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))

;; ;; pm2.83 (19m29.217s)
;; !(obct 25 (: $x (→ (→ 𝜑 (→ 𝜓 𝜒)) (→ (→ 𝜑 (→ 𝜒 𝜃)) (→ 𝜑 (→ 𝜓 𝜃))))))

;; ;; loolin (16m16.625s)
;; !(obct 26 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜓 𝜑)) (→ 𝜓 𝜑))))

;; NEXT: determine depths

;; ;; imim12 (?) (was 25 and supposedly worked)
;; !(obct 31 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜃) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜃))))))

;; ;; peirceroll
;; !(obct 32 (: $x (→ (→ (→ (→ 𝜑 𝜓) 𝜑) 𝜑) (→ (→ (→ 𝜑 𝜓) 𝜒) (→ (→ 𝜒 𝜑) 𝜑)))))

;; ;; pm2.86
;; !(obct 32 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ 𝜑 (→ 𝜓 𝜒)))))
