;; Simple backward chainer for creating graphical representations of
;; chaining with MeTTaGrapher

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define backward chainer ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Base cases
(= (bc $_ (: ax₁ (→ $𝜑 (→ $𝜓 $𝜑))))
   (: ax₁ (→ $𝜑 (→ $𝜓 $𝜑))))
(= (bc $_ (: ax₂ (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒)))))
   (: ax₂ (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒)))))
(= (bc $_ (: ax₃ (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑))))
   (: ax₃ (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑))))

;; Recursive steps
(= (bc (S $k) (: (mp $f $x) $b))
   (let* (((: $f (→ $a $b)) (bc $k (: $f (→ $a $b))))
          ((: $x $a) (bc $k (: $x $a))))
     (: (mp $f $x) $b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test backward chainer ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; impid
;; !(bc (S Z) (: $x (→ (→ 𝜑 𝜓) (→ 𝜑 𝜑))))

;; pm2.43
!(bc (S (S Z)) (: $x (→ (→ 𝜑 (→ 𝜑 𝜓)) (→ 𝜑 𝜓))))

;; ;; imim2
;; !(once (bc (S (S (S Z))) (: $x (→ (→ 𝜑 𝜓) (→ (→ 𝜒 𝜑) (→ 𝜒 𝜓))))))

;; ;; jarr
;; !(once (bc (S (S (S (S Z)))) (: $x (→ (→ (→ 𝜑 𝜓) 𝜒) (→ 𝜓 𝜒)))))
