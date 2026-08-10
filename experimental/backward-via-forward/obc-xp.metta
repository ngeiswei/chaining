;; Optimized Backward Chainer with Maximum Proof Size.
;;
;; Extracted from bfc-xp.metta so that this implementation can be
;; loaded and benchmarked independently from the rest of the
;; backward-via-forward experiments.  Specialized for propositional
;; calculus (axioms ax₁, ax₂, ax₃ and inference rule mp only).
;;
;; Self-contained: the `Sized`/`MkSized` types that `obc` depends on
;; are defined locally (originally borrowed from
;; experimental/metamath/pc-xp.metta).

;;;;;;;;;;;;;;;
;; Sized ;;
;;;;;;;;;;;;;;;

;; Associate a size to a term
(: Sized (-> $a Type))
(: MkSized (-> $n                       ; Size
               $a                       ; Object
               (Sized $a)))             ; Sized object

;; Access functions
(= (Sized.size (MkSized $s $x)) $s)
(= (Sized.object (MkSized $s $x)) $x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Optimized backward chainer with maximum proof size ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Optimized backward chainer, in the sense that it uses maximum proof
;; size instead of depth, is specialized for propositional calculus
;; and uses Number instead of Nat.
(= (obc-gtz $s (: ax₁ (→ $𝜑 (→ $𝜓 $𝜑))))
   (MkSized 1 (: ax₁ (→ $𝜑 (→ $𝜓 $𝜑)))))
(= (obc-gtz $s (: ax₂ (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒)))))
   (MkSized 1 (: ax₂ (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒))))))
(= (obc-gtz $s (: ax₃ (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑))))
   (MkSized 1 (: ax₃ (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑)))))
(= (obc-gtz $s (: (mp $f $x) $b))
   (if (< 2 $s)
       (let* (((MkSized $fs (: $f (→ $a $b))) (obc (- $s 2) (: $f (→ $a $b))))
              ((MkSized $xs (: $x $a)) (obc (- (- $s 1) $fs) (: $x $a))))
         (MkSized (+ (+ $fs $xs) 1) (: (mp $f $x) $b)))
       (empty)))
(= (obc $s (: $x $a))
   (if (< 0 $s)
       (obc-gtz $s (: $x $a))
       (empty)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test proof-sized bound optimized backward chainer ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Exhausively generate all proofs of certain sizes
;; !(obc 1 (: $x $a))
;; !(obc 3 (: $x $a))
;; !(obc 5 (: $x $a))
;; !(obc 7 (: $x $a))
;; !(obc 9 (: $x $a))
;; !(obc 11 (: $x $a)) ; 5523, 0.391s
;; !(obc 13 (: $x $a)) ; 35064, 2.458s
;; !(obc 15 (: $x $a)) ; 233681, 18.471s
;; !(obc 17 (: $x $a)) ; 1591750, 142.83s

;; ;; id
;; !(obc 5 (: $x (→ 𝜑 𝜑)))

;; ;; pm2.43
;; !(obc 7 (: $x (→ (→ 𝜑 (→ 𝜑 𝜓)) (→ 𝜑 𝜓))))

;; ;; 2a1
;; !(obc 7 (: $x (→ 𝜑 (→ 𝜓 (→ 𝜒 𝜑)))))

;; ;; imim2 (81ms)
;; !(obc 7 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜑) (→ 𝜒 𝜓))))

;; jarr (90ms)
!(obc 13 (: $x (→ (→ (→ 𝜑 𝜓) 𝜒) (→ 𝜓 𝜒))))

;; ;; pm2.27
;; !(obc 13 (: $x (→ 𝜑 (→ (→ 𝜑 𝜓) 𝜓))))

;; ;; imim1 (140ms)
;; !(obc 15 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜒)))))

;; ;; loowoz (~3.309s)
;; !(obc 19 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒)))))

;; ;; pm2.83 (19m29.217s)
;; !(obc 25 (: $x (→ (→ 𝜑 (→ 𝜓 𝜒)) (→ (→ 𝜑 (→ 𝜒 𝜃)) (→ 𝜑 (→ 𝜓 𝜃))))))

;; ;; loolin (16m16.625s)
;; !(obc 26 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜓 𝜑)) (→ 𝜓 𝜑))))

;; NEXT: determine depths

;; ;; imim12 (?) (was 25 and supposedly worked)
;; !(obc 31 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜃) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜃))))))

;; ;; peirceroll
;; !(obc 32 (: $x (→ (→ (→ (→ 𝜑 𝜓) 𝜑) 𝜑) (→ (→ (→ 𝜑 𝜓) 𝜒) (→ (→ 𝜒 𝜑) 𝜑)))))

;; ;; pm2.86
;; !(obc 32 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ 𝜑 (→ 𝜓 𝜒)))))
