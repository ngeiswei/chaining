;; Like anf-prod.metta but the idea is to recursively pass the map
;; around to prune the search space early.

;; Disable co-unification
!(translatePredicate (set_prolog_flag occurs_check True))

;; Import anf.metta
!(import! &self ./anf.metta)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;;;;;;;;;;;;;;;;;;;;;;; ;;
;; ;; Backward Chaining ;; ;;
;; ;;;;;;;;;;;;;;;;;;;;;;; ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;
;; Budget Structure ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Define budget type and constructors for inference control
;;
;; bc takes a budget structure in argument for instance control.  It
;; also returns, alongside the answer, the budget structure with the
;; *remaining* budgets after the answer:
;;
;; (, (MkBudget $size $depth) $answer)
;;
;; A proof consumes one unit of size per symbol, and one unit of depth
;; per inference step depth, except products (`,`) which consume no
;; depth so that conjunctions of queries keep a balanced depth budget.
(: Budget Type)
(: MkBudget (-> Number                 ; Size budget
                Number                 ; Depth budget
                Budget))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Output to input Processing ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Given a list $xs of elements in {⊤, ⊥, VARIABLE} calculate a list
;; $fys so that each element of $fys is:
;;
;; - ⊤ if the corresponding element of $xs is ⊤.
;;
;; - Undetermined (a fresh variable) otherwise.
;;
;; co2i1 stands for conjunction output to input of premise 1.
;;
;; TODO: the Cons/Nil encoding is an expression, not a runtime list,
;; so (List Boolean) is rejected by the type checker.  %Undefined%
;; is used until the representation is settled.
(: co2i1 (-> %Undefined%                ; $xs
             %Undefined%))              ; $fys
(= (co2i1 Nil) Nil)
(= (co2i1 (Cons $x $xs))
   (case (get-metatype $x)
     ((Variable (Cons $fy (co2i1 $xs)))
      (Symbol (Cons (if (== $x ⊤) ⊤ $fy) (co2i1 $xs)))
      ($else (trace! "Error: should not happen, it is probably a bug" Nil)))))

;; Given two lists $xs of elements in {⊤, ⊥, VARIABLE} and $fxs of
;; elements in {⊤, ⊥}, calculate a list $gys so that each element of
;; $gys is:
;;
;; - ⊤ if the corresponding element of $xs is ⊤.
;;
;; - ⊥ if the corresponding element of $xs is ⊥ and the corresponding
;;   element of $fys is ⊤.
;;
;; - Undetermined (a fresh variable) otherwise.
;;
;; co2i2 stands for conjunction output to input of premise 2.
;;
;; Both $xs and $fys are assumed to be of same length.
(: co2i2 (-> %Undefined%                ; $xs
             %Undefined%                ; $fys
             %Undefined%))              ; $gys
(= (co2i2 Nil Nil) Nil)
(= (co2i2 (Cons $x $xs) (Cons $fy $fys))
   (case (get-metatype $x)
     ((Variable (Cons $gy (co2i2 $xs $fys)))
      (Symbol (Cons (if (== $x ⊤)
                        ⊤
                        ;; In this case $x is ⊥
                        (if (== $fy ⊤) ⊥ $gy)) (co2i2 $xs $fys)))
      ($else (trace! "Error: should not happen, it is probably a bug" Nil)))))

;; Given a list $xs in {⊤, ⊥, VARIABLE} calculate a list of $gys so
;; that each element of $gys is a fresh variable.
;;
;; eo2i1 stands for exclusive output to input of premise 1.
(: eo2i1 (-> %Undefined%                ; $xs
             %Undefined%))              ; $fys
(= (eo2i1 Nil) Nil)
(= (eo2i1 (Cons $x $xs)) (Cons $fy (eo2i1 $xs)))

;; Given two lists $xs and $fys of elements in {⊤, ⊥, VARIABLE}
;; calculate a list $gys so that each element of $gys is:
;;
;; - the completement of the corresponding element of $fys if the
;;   corresponding element of $xs is ⊤.
;;
;; - the same as the corresponding element of $fys if the
;;   corresponding element of $xs is ⊥.
;;
;; eo2i2 stands for exclusive output to input of premise 2.
;;
;; Both $xs and $fys are assumed to be of same length.
(: eo2i2 (-> %Undefined%                ; $xs
             %Undefined%                ; $fys
             %Undefined%))              ; $gys
(= (eo2i2 Nil Nil) Nil)
(= (eo2i2 (Cons $x $xs) (Cons $fy $fys))
   (case (get-metatype $x)
     ((Variable (Cons $gy (eo2i2 $xs $fys)))
      (Symbol (Cons (if (== $x ⊤) (negate $fy) $fy) (eo2i2 $xs $fys)))
      ($else (trace! "Error: should not happen, it is probably a bug" Nil)))))

;;;;;;;;;;;;;;;;;;;;;;
;; Backward Chainer ;;
;;;;;;;;;;;;;;;;;;;;;;

;; ;; Type signature
;; (: bc (-> $a                     ; Axiom base
;;           $b                     ; Rule base
;;           Budget                 ; Budget
;;           $c                     ; Query
;;           (, Budget $c)))        ; Remaining budget and answer

;; Generic base case
(= (bc $ab (MkBudget $size $depth) (: $x $a))
   ;; (trace! (👁 bc [base] $ab (MkBudget $size $depth) (: $x $a))
   (if (and (<= 1 $size) (<= 1 $depth))
       ;; Look for $x within the axiom base
       (match $ab (: $x $a) (, (MkBudget (- $size 1) (- $depth 1)) (: $x $a)))
       (empty)))
   ;; )

;; Specialized recursive steps

;; Conjunction evaluation.  The query
;;
;; (≗ map (∧ $f $g) $xs $ys)
;;
;; means that (map (∧ $f $g) $xs) evaluates to $ys.  The premises are
;;
;; 1. (≗ map $f $xs $fys)
;; 2. (≗ map $g $xs $gys)
;;
;; However $fys is calculated to be ⊤ on all inputs where $ys is ⊤,
;; and left as a variable on inputs where $ys is ⊥.  Once $f has been
;; discovered and thus $fys is fully determined, then $gys is
;; calculated so that so that only inputs where both $ys and $fys is ⊥
;; then $gys is undetermined (takes a variable).
;;
;; All this map output manipulation is not counted into the budget.
;;
;; `ce` stands for conjunction evaluation.
;;
;; Additionally, Algebraic Normal Form checking is taking place "for
;; free", meaning that it is not accounted into the budget.
(= (bc $ab (MkBudget $size $depth)
       (: (ce $fprf $gprf) (≗ map (∧ $f $g) $xs $ys)))
   ;; (trace! (👁 bc [ce] $ab (MkBudget $size $depth)
   ;;            (: (ce $fprf $gprf) (≗ map (∧ $f $g) $xs $ys)))
   (if (and (<= 3 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Calculate $fys to be ⊤ where $ys is ⊤, and
              ;; undertermined otherwise.
              ($fys (co2i1 $ys))
              ;; Recurse on premise 1.  The budget only needs to be 1
              ;; (size and depth) since $f must be an atomic predicate
              ;; according to ANF.
              ((, (MkBudget 0 0) (: $fprf (≗ map $f $xs $fys)))
               (bc $ab (MkBudget 1 1) (: $fprf (≗ map $f $xs $fys))))
              ;; ANF checking: $f is an atomic predicate (except 𝔽 or 𝕋)
              (True (isContingentAtomicPredicate $f))
              ;; Calculate $gys to be ⊤ where $ys is ⊤, ⊥ where $fys
              ;; is ⊤ and $ys is ⊥, and undetermined otherwise.
              ($gys (co2i2 $ys $fys))
              ;; Recurse on premise 2 to discover $g.
              ((, (MkBudget $gsize $gdepth) (: $gprf (≗ map $g $xs $gys)))
               (bc $ab (MkBudget (- $size 2) (- $depth 1))
                   (: $gprf (≗ map $g $xs $gys))))
              ;; Make sure that (∧ $f $g) is in algebraic normal form,
              ;; a shallow test is used because $f and $g are assumed
              ;; to be already be in algebraic normal form.
              (True (isInductiveANF (∧ $f $g))))
         ;; Build conclusion
         (, (MkBudget $gsize $gdepth)
            (: (ce $fprf $gprf) (≗ map (∧ $f $g) $xs $ys))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Exclusive disjunction evaluation.  The query
;;
;; (≗ map (⊻ $f $g) $xs $ys)
;;
;; means that (map (⊻ $f $g) $xs) evaluates to $ys.  The premises are
;;
;; 1. (≗ map $f $xs $fys)
;; 2. (≗ map $g $xs $gys)
;;
;; First, $fys is left undetermined.  Second, once $f has been
;; discovered and thus $fys is fully determined, then $gys is
;; calculated so that it is the complement of $fys for inputs where
;; $ys is ⊤ and equal for inputs where $ys is ⊥.
;;
;; All this map output manipulation is not counted into the budget.
;;
;; `ee` stands for exclusive evaluation.
;;
;; Additionally, Algebraic Normal Form checking is taking place "for
;; free", meaning that it is not accounted into the budget.
(= (bc $ab (MkBudget $size $depth)
       (: (ee $fprf $gprf) (≗ map (⊻ $f $g) $xs $ys)))
   ;; (trace! (👁 bc $ab (MkBudget $size $depth)
   ;;            (: (ee $fprf $gprf) (≗ map (⊻ $f $g) $xs $ys)))
   (if (and (<= 3 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Calculate $fys to be filled with fresh variables
              ($fys (eo2i1 $ys))
              ;; Recurse on premise 1 to discover $f
              ((, (MkBudget $fsize $fdepth) (: $fprf (≗ map $f $xs $fys)))
               (bc $ab (MkBudget (- $size 2) $depth)
                   (: $fprf (≗ map $f $xs $fys))))
              ;; Make sure $f is in first level algebraic normal form
              (True (isFstLevelInductiveANF $f))
              ;; Calculate $gys so that it is a complement of $fys
              ;; when $ys is ⊤ or equal when $ys is ⊥.
              ($gys (eo2i2 $ys $fys))
              ;; Recurse on premise 2 to discover $g.
              ((, (MkBudget $gsize $gdepth) (: $gprf (≗ map $g $xs $gys)))
               (bc $ab (MkBudget (+ $fsize 1) (- $depth 1))
                   (: $gprf (≗ map $g $xs $gys))))
              ;; Make sure that (⊻ $f $g) is in algebraic normal form,
              (True (isInductiveANF (⊻ $f $g))))
         ;; Build conclusion
         (, (MkBudget $gsize $gdepth)
            (: (ee $fprf $gprf) (≗ map (⊻ $f $g) $xs $ys))))
       ;; Not enough budget
       (empty)))
   ;; )
