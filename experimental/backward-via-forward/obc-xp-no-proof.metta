;; Like [obc-xp.metta](obc-xp.metta) but proofs are not constructed as
;; the search takes place.

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
(= (obc-gtz $s (→ $𝜑 (→ $𝜓 $𝜑)))
   (MkSized 1 (→ $𝜑 (→ $𝜓 $𝜑))))
(= (obc-gtz $s (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒))))
   (MkSized 1 (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒)))))
(= (obc-gtz $s (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑)))
   (MkSized 1 (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑))))
(= (obc-gtz $s $b)
   (if (< 2 $s)
       (let* (((MkSized $fs (→ $a $b)) (obc (- $s 2) (→ $a $b)))
              ((MkSized $xs $a) (obc (- (- $s 1) $fs) $a)))
         (MkSized (+ (+ $fs $xs) 1) $b))
       (empty)))
(= (obc $s $a)
   (if (< 0 $s)
       (obc-gtz $s $a)
       (empty)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test proof-sized bound optimized backward chainer ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; id
;; !(obc 5 (→ 𝜑 𝜑))

;; ;; pm2.43
;; !(obc 7 (→ (→ 𝜑 (→ 𝜑 𝜓)) (→ 𝜑 𝜓)))

;; ;; 2a1
;; !(obc 7 (→ 𝜑 (→ 𝜓 (→ 𝜒 𝜑))))

;; ;; imim2
;; !(obc 7 (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜑) (→ 𝜒 𝜓))))

;; ;; jarr
;; !(obc 13 (→ (→ (→ 𝜑 𝜓) 𝜒) (→ 𝜓 𝜒)))

;; ;; pm2.27
;; !(obc 13 (→ 𝜑 (→ (→ 𝜑 𝜓) 𝜓)))

;; ;; imim1 (0.177s)
;; !(obc 15 (→ (→ 𝜑 𝜓) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜒))))

;; ;; loowoz (4.194s)
;; !(obc 19 (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ (→ 𝜓 𝜑) (→ 𝜓 𝜒))))

;; pm2.83 (?)
!(obc 25 (→ (→ 𝜑 (→ 𝜓 𝜒)) (→ (→ 𝜑 (→ 𝜒 𝜃)) (→ 𝜑 (→ 𝜓 𝜃)))))

;; ;; loolin (?)
;; !(obc 26 (→ (→ (→ 𝜑 𝜓) (→ 𝜓 𝜑)) (→ 𝜓 𝜑)))

;; NEXT: determine depths

;; ;; imim12 (?) (was 25 and supposedly worked)
;; !(obc 31 (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜃) (→ (→ 𝜓 𝜒) (→ 𝜑 𝜃))))))

;; ;; peirceroll
;; !(obc 32 (: $x (→ (→ (→ (→ 𝜑 𝜓) 𝜑) 𝜑) (→ (→ (→ 𝜑 𝜓) 𝜒) (→ (→ 𝜒 𝜑) 𝜑)))))

;; ;; pm2.86
;; !(obc 32 (: $x (→ (→ (→ 𝜑 𝜓) (→ 𝜑 𝜒)) (→ 𝜑 (→ 𝜓 𝜒)))))
