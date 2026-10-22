;; Like [ant-prod.metta] but prebuild the candidate space, then
;; confront them to the target truth table.

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

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PLN Backward Chainer ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Type signature
;; (: bc (-> $a                     ; Axiom base
;;           $b                     ; Rule base
;;           Budget                 ; Budget
;;           $c                     ; Query
;;           (, Budget $c)))        ; Remaining budget and answer

;; Generic base case
(= (bc $ab $rb (MkBudget $size $depth) (: $x $a))
   ;; (trace! (👁 bc [base] $ab $rb (MkBudget $size $depth) (: $x $a))
   (if (and (<= 1 $size) (<= 1 $depth))
       ;; Look for $x within the axiom base
       (match $ab (: $x $a) (, (MkBudget (- $size 1) (- $depth 1)) (: $x $a)))
       (empty)))
   ;; )

;; Specific base cases

;; 𝕋 is in Algebaic Normal Form.
;;
;; tanf stands for true is in algebraic normal form.
(= (bc $ab $rb (MkBudget $size $depth) (: tanf (ANF 𝕋)))
   ;; (trace! (👁 bc [tanf] $ab $rb (MkBudget $size $depth) (: tanf (ANF 𝕋)))
   (if (and (<= 1 $size) (<= 1 $depth))
       (, (MkBudget (- $size 1) (- $depth 1)) (: tanf (ANF 𝕋)))
       (empty)))
   ;; )

;; 𝔽 is in Algebaic Normal Form.
;;
;; fanf stands for false is in algebraic normal form.
(= (bc $ab $rb (MkBudget $size $depth) (: fanf (ANF 𝔽)))
   ;; (trace! (👁 bc [𝔽] $ab $rb (MkBudget $size $depth) (: fanf (ANF 𝔽)))
   (if (and (<= 1 $size) (<= 1 $depth))
       (, (MkBudget (- $size 1) (- $depth 1)) (: fanf (ANF 𝔽)))
       (empty)))
   ;; )

;; 𝕋 evaluates to ⊤.
;;
;; tet stands for true evaluates to top.
(= (bc $ab $rb (MkBudget $size $depth) (: tet (≗ 𝕋 $x ⊤)))
   ;; (trace! (👁 bc [𝕋] $ab $rb (MkBudget $size $depth) (: tet (≗ 𝕋 $x ⊤)))
   (if (and (<= 1 $size) (<= 1 $depth))
       (, (MkBudget (- $size 1) (- $depth 1)) (: tet (≗ 𝕋 $x ⊤)))
       (empty)))
   ;; )

;; 𝔽 evaluates to ⊥
;;
;; feb stands for false evaluates to bottom.
(= (bc $ab $rb (MkBudget $size $depth) (: feb (≗ 𝔽 $x ⊥)))
   ;; (trace! (👁 bc [𝔽] $ab $rb (MkBudget $size $depth) (: feb (≗ 𝔽 $x ⊥)))
   (if (and (<= 1 $size) (<= 1 $depth))
       (, (MkBudget (- $size 1) (- $depth 1)) (: feb (≗ 𝔽 $x ⊥)))
       (empty)))
   ;; )

;; Generic recursive steps

;; ;; Unary rule application
;; (= (bc $ab $rb (MkBudget $size $depth) (: ($f $x) $b))
;;    (if (and (<= 2 $size) (<= 2 $depth))
;;        ;; Enough budget
;;        (let* (;; Look for $f within the rule base
;;               ((: $f (-> $a $b)) (match $rb (: $f (-> $a $b)) (: $f (-> $a $b))))
;;               ;; Recursive call on $x
;;               ((, (MkBudget $xsize $xdepth) (: $x $a))
;;                (bc $ab $rb (MkBudget (- $size 1) (- $depth 1)) (: $x $a))))
;;          ;; Output remaining budget with answer
;;          (, (MkBudget $xsize $xdepth) (: ($f $x) $b)))
;;        ;; Not enough budget
;;        (empty)))

;; ;; Unary rule application
;; (= (bc $ab $rb (MkBudget $size $depth) (: ($f $x1 $x2) $b))
;;    (if (and (<= 3 $size) (<= 2 $depth))
;;        ;; Enough budget
;;        (let* (;; Look for $f within the rule base
;;               ((: $f (-> $a1 $a2 $b))
;;                (match $rb (: $f (-> $a1 $a2 $b)) (: $f (-> $a1 $a2 $b))))
;;               ;; Recursive call on $x1
;;               ((, (MkBudget $x1size $x1depth) (: $x1 $a1))
;;                (bc $ab $rb (MkBudget (- $size 2) (- $depth 1)) (: $x1 $a1)))
;;               ;; Recursive call on $x2
;;               ((, (MkBudget $x2size $x2depth) (: $x2 $a2))
;;                (bc $ab $rb (MkBudget (+ $x1size 1) (- $depth 1)) (: $x2 $a2))))
;;          ;; Output remaining budget with answer
;;          (, (MkBudget $x2size (min $x1depth $x1depth)) (: ($f $x1 $x2) $b)))
;;        ;; Not enough budget
;;        (empty)))

;; Specialized recursive steps

;; Check that a conjunction is in algebraic normal form.
;;
;; (∧ $f $g) is in algebraic normal form if $f is a contingent
;; predicate and $g is a conjunction or a contingent predicate.
;;
;; `canf` stands for conjunction is in algebraic normal form.
;;
;; Note that most of algebraic normal form checking is taking place
;; "for free", meaning that it is not accounted into the budget.  This
;; could be done entirely via reasoning, but since we already have
;; checking functions coded we use them for the sake of simplificity,
;; as this is not where the difficulty lies.
(= (bc $ab $rb (MkBudget $size $depth) (: (canf $fprf $gprf) (ANF (∧ $f $g))))
   ;; (trace! (👁 bc [canf] $ab $rb (MkBudget $size $depth)
   ;;            (: (canf $fprf $gprf) (ANF (∧ $f $g))))
   (if (and (<= 3 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Recurse on premise 1 to make sure that $f is in ANF.
              ;; The budget only needs to be 1 (size and depth) since
              ;; $f must be an atomic predicate according to ANF.
              ((, (MkBudget 0 0) (: $fprf (ANF $f)))
               (bc $ab $rb (MkBudget 1 1) (: $fprf (ANF $f))))
              ;; ANF checking: $f is an atomic predicate (except 𝔽 or 𝕋)
              (True (isContingentAtomicPredicate $f))
              ;; Recurse on premise 2 to make sure that $g is in ANF
              ((, (MkBudget $gsize $gdepth) (: $gprf (ANF $g)))
               (bc $ab $rb (MkBudget (- $size 2) (- $depth 1))
                   (: $gprf (ANF $g))))
              ;; Make sure that (∧ $f $g) is in algebraic normal form,
              ;; a shallow test is used because $f and $g are assumed
              ;; to be already be in algebraic normal form.
              (True (isInductiveANF (∧ $f $g))))
         ;; Build conclusion
         (, (MkBudget $gsize $gdepth) (: (canf $fprf $gprf) (ANF (∧ $f $g)))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Check that an exclusive disjunction is in algebraic normal form.
;;
;; (⊻ $f $g) is in algebraic normal form if $f and $g are contingent
;; predicates or conjunctions in ANF, or 𝕋.
;;
;; `eanf` stands for exclusive is in algebraic normal form.
;;
;; Note that most of algebraic normal form checking is taking place
;; "for free", meaning that it is not accounted into the budget.  This
;; could be done entirely via reasoning, but since we already have
;; checking functions coded we use them for the sake of simplificity,
;; as this is not where the difficulty lies.
(= (bc $ab $rb (MkBudget $size $depth) (: (eanf $fprf $gprf) (ANF (⊻ $f $g))))
   ;; (trace! (👁 bc [eanf] $ab $rb (MkBudget $size $depth)
   ;;            (: (eanf $fprf $gprf) (ANF (⊻ $f $g))))
   (if (and (<= 3 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Recurse on premise 1 to make sure that $f is in ANF
              ((, (MkBudget $fsize $fdepth) (: $fprf (ANF $f)))
               (bc $ab $rb (MkBudget (- $size 2) $depth) (: $fprf (ANF $f))))
              ;; Make sure $f is in first level algebraic normal form
              (True (isFstLevelInductiveANF $f))
              ;; Recurse on premise 2 to make sure that $g is in ANF
              ((, (MkBudget $gsize $gdepth) (: $gprf (ANF $g)))
               (bc $ab $rb (MkBudget (+ $fsize 1) (- $depth 1))
                   (: $gprf (ANF $g))))
              ;; Make sure that (⊻ $f $g) is in algebraic normal form
              (True (isInductiveANF (⊻ $f $g))))
         ;; Build conclusion
         (, (MkBudget $gsize (min $fdepth $gdepth))
            (: (eanf $fprf $gprf) (ANF (⊻ $f $g)))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Conjunction evaluation to ⊤.  The query
;;
;; (≗ (∧ $f $g) $x ⊤)
;;
;; means that ((∧ $f $g) $x) evaluates to ⊤ and requires the premises
;; that both ($f $x) and ($g $x) evaluate to ⊤.
;;
;; `cet` stands for conjunction evaluates to top.
(= (bc $ab $rb (MkBudget $size $depth) (: (cet $fprf $gprf) (≗ (∧ $f $g) $x ⊤)))
   ;; (trace! (👁 bc [cet] $ab $rb (MkBudget $size $depth)
   ;;            (: (cet $fprf $gprf) (≗ (∧ $f $g) $x ⊤)))
   (if (and (<= 3 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Recurse on premise 1 to make sure that $f evaluates
              ;; to true on $x.  The budget only needs to be 1 (size
              ;; and depth) since $f must be an atomic predicate
              ;; according to ANF.
              ((, (MkBudget 0 0) (: $fprf (≗ $f $x ⊤)))
               (bc $ab $rb (MkBudget 1 1) (: $fprf (≗ $f $x ⊤))))
              ;; Recurse on premise 2 to make sure that $g evaluates
              ;; to true on $x
              ((, (MkBudget $gsize $gdepth) (: $gprf (≗ $g $x ⊤)))
               (bc $ab $rb (MkBudget (- $size 2) (- $depth 1))
                   (: $gprf (≗ $g $x ⊤)))))
         ;; Build conclusion
         (, (MkBudget $gsize $gdepth) (: (cet $fprf $gprf) (≗ (∧ $f $g) $x ⊤))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Conjunction evaluation to ⊥ from left.  The query
;;
;; (≗ (∧ $f $g) $x ⊥)
;;
;; means that ((∧ $f $g) $x) evaluates to ⊥ and requires as premise
;; that ($f $x) evaluates to ⊥.
;;
;; `cebl` stands for conjunction evaluates to bottom from left.
(= (bc $ab $rb (MkBudget $size $depth) (: (cebl $fprf) (≗ (∧ $f $g) $x ⊥)))
   ;; (trace! (👁 bc [cebl] $ab $rb (MkBudget $size $depth)
   ;;            (: (cebl $fprf) (≗ (∧ $f $g) $x ⊥)))
   (if (and (<= 2 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Recurse on premise 1 to make sure that $f evaluates
              ;; to ⊥ on $x.  The budget only needs to be 1 (size and
              ;; depth) since $f must be an atomic predicate according
              ;; to ANF.
              ((, (MkBudget 0 0) (: $fprf (≗ $f $x ⊥)))
               (bc $ab $rb (MkBudget 1 1) (: $fprf (≗ $f $x ⊥)))))
         ;; Build conclusion
         (, (MkBudget (- $size 2) (- $depth 1)) (: (cebl $fprf) (≗ (∧ $f $g) $x ⊥))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Conjunction evaluation to ⊥ from right.  The query
;;
;; (≗ (∧ $f $g) $x ⊥)
;;
;; means that ((∧ $f $g) $x) evaluates to ⊥ and requires as premise
;; that ($g $x) evaluates to ⊥.
;;
;; `cebr` stands for conjunction evaluates to bottom from right.
(= (bc $ab $rb (MkBudget $size $depth) (: (cebr $gprf) (≗ (∧ $f $g) $x ⊥)))
   ;; (trace! (👁 bc [cebr] $ab $rb (MkBudget $size $depth)
   ;;            (: (cebr $gprf) (≗ (∧ $f $g) $x ⊥)))
   (if (and (<= 2 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Recurse on premise 1 to make sure that $g evaluates
              ;; to ⊥ on $x
              ((, (MkBudget $gsize $gdepth) (: $gprf (≗ $g $x ⊥)))
               (bc $ab $rb (MkBudget (- $size 1) (- $depth 1))
                   (: $gprf (≗ $g $x ⊥)))))
         ;; Build conclusion
         (, (MkBudget $gsize $gdepth) (: (cebr $gprf) (≗ (∧ $f $g) $x ⊥))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Exclusive disjunction evaluation to ⊤ from left.  The query
;;
;; (≗ (⊻ $f $g) $x ⊤)
;;
;; means that ((⊻ $f $g) $x) evaluates to ⊤ and requires as premises
;; that ($f $x) evaluates to ⊤ and ($g $x) evaluates to ⊥.
;;
;; `eetl` stands for exclusive evaluates to top from left.
(= (bc $ab $rb (MkBudget $size $depth) (: (eetl $fprf $gprf) (≗ (⊻ $f $g) $x ⊤)))
   ;; (trace! (👁 bc $ab $rb (MkBudget $size $depth)
   ;;            (: (eetl $fprf $gprf) (≗ (⊻ $f $g) $x ⊤)))
   (if (and (<= 3 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Recurse on premise 1 to make sure that $f evaluates
              ;; to true on $x.
              ((, (MkBudget $fsize $fdepth) (: $fprf (≗ $f $x ⊤)))
               (bc $ab $rb (MkBudget (- $size 2) $depth) (: $fprf (≗ $f $x ⊤))))
              ;; Recurse on premise 2 to make sure that $g evaluates
              ;; to false on $x
              ((, (MkBudget $gsize $gdepth) (: $gprf (≗ $g $x ⊥)))
               (bc $ab $rb (MkBudget (+ $fsize 1) (- $depth 1))
                   (: $gprf (≗ $g $x ⊥)))))
         ;; Build conclusion
         (, (MkBudget $gsize $gdepth) (: (eetl $fprf $gprf) (≗ (⊻ $f $g) $x ⊤))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Exclusive disjunction evaluation to ⊤ from right.  The query
;;
;; (≗ (⊻ $f $g) $x ⊤)
;;
;; means that ((⊻ $f $g) $x) evaluates to ⊤ and requires as premises
;; that ($f $x) evaluates to ⊥ and ($g $x) evaluates to ⊤.
;;
;; `eetr` stands for exclusive evaluates to top from right.
(= (bc $ab $rb (MkBudget $size $depth) (: (eetr $fprf $gprf) (≗ (⊻ $f $g) $x ⊤)))
   ;; (trace! (👁 bc [eetr] $ab $rb (MkBudget $size $depth)
   ;;            (: (eetr $fprf $gprf) (≗ (⊻ $f $g) $x ⊤)))
   (if (and (<= 3 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Recurse on premise 1 to make sure that $f evaluates
              ;; to false on $x.
              ((, (MkBudget $fsize $fdepth) (: $fprf (≗ $f $x ⊥)))
               (bc $ab $rb (MkBudget (- $size 2) $depth) (: $fprf (≗ $f $x ⊥))))
              ;; Recurse on premise 2 to make sure that $g evaluates
              ;; to true on $x
              ((, (MkBudget $gsize $gdepth) (: $gprf (≗ $g $x ⊤)))
               (bc $ab $rb (MkBudget (+ $fsize 1) (- $depth 1))
                   (: $gprf (≗ $g $x ⊤)))))
         ;; Build conclusion
         (, (MkBudget $gsize $gdepth) (: (eetr $fprf $gprf) (≗ (⊻ $f $g) $x ⊤))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Exclusive disjunction evaluation to ⊥ from top.  The query
;;
;; (≗ (⊻ $f $g) $x ⊥)
;;
;; means that ((⊻ $f $g) $x) evaluates to ⊥ and requires as premises
;; that both ($f $x) and ($g $x) evaluate to ⊤.
;;
;; `eebt` stands for exclusive evaluates to bottom from top.
(= (bc $ab $rb (MkBudget $size $depth) (: (eebt $fprf $gprf) (≗ (⊻ $f $g) $x ⊥)))
   ;; (trace! (👁 bc [eebt] $ab $rb (MkBudget $size $depth)
   ;;            (: (eebt $fprf $gprf) (≗ (⊻ $f $g) $x ⊥)))
   (if (and (<= 3 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Recurse on premise 1 to make sure that $f evaluates
              ;; to true on $x.
              ((, (MkBudget $fsize $fdepth) (: $fprf (≗ $f $x ⊤)))
               (bc $ab $rb (MkBudget (- $size 2) $depth) (: $fprf (≗ $f $x ⊤))))
              ;; Recurse on premise 2 to make sure that $g evaluates
              ;; to true on $x
              ((, (MkBudget $gsize $gdepth) (: $gprf (≗ $g $x ⊤)))
               (bc $ab $rb (MkBudget (+ $fsize 1) (- $depth 1))
                   (: $gprf (≗ $g $x ⊤)))))
         ;; Build conclusion
         (, (MkBudget $gsize $gdepth) (: (eebt $fprf $gprf) (≗ (⊻ $f $g) $x ⊥))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Exclusive disjunction evaluation to ⊥ from bottom.  The query
;;
;; (≗ (⊻ $f $g) $x ⊥)
;;
;; means that ((⊻ $f $g) $x) evaluates to ⊥ and requires as premises
;; that both ($f $x) and ($g $x) evaluate to ⊥.
;;
;; `eebb` stands for exclusive evaluates to bottom from bottom.
(= (bc $ab $rb (MkBudget $size $depth) (: (eebb $fprf $gprf) (≗ (⊻ $f $g) $x ⊥)))
   ;; (trace! (👁 bc [eebb] $ab $rb (MkBudget $size $depth)
   ;;            (: (eebb $fprf $gprf) (≗ (⊻ $f $g) $x ⊥)))
   (if (and (<= 3 $size) (<= 2 $depth))
       ;; Enough budget
       (let* (;; Recurse on premise 1 to make sure that $f evaluates
              ;; to false on $x.
              ((, (MkBudget $fsize $fdepth) (: $fprf (≗ $f $x ⊥)))
               (bc $ab $rb (MkBudget (- $size 2) $depth) (: $fprf (≗ $f $x ⊥))))
              ;; Recurse on premise 2 to make sure that $g evaluates
              ;; to false on $x
              ((, (MkBudget $gsize $gdepth) (: $gprf (≗ $g $x ⊥)))
               (bc $ab $rb (MkBudget (+ $fsize 1) (- $depth 1))
                   (: $gprf (≗ $g $x ⊥)))))
         ;; Build conclusion
         (, (MkBudget $gsize $gdepth) (: (eebb $fprf $gprf) (≗ (⊻ $f $g) $x ⊥))))
       ;; Not enough budget
       (empty)))
   ;; )

;; Product.  In the query
;;
;; (: (, $x $y) (, $a $b))
;;
;; $x must be a proof of $a and $y must be a proof of $b for (, $x $y)
;; to be a proof (, $a $b).
;;
;; Note that the product does not consume any depth.  This is done so
;; in order to view it as flattened and to avoid deeper queries buried
;; in the left associativity to require a higher depth.
(= (bc $ab $rb (MkBudget $size $depth) (: (, $x $y) (, $a $b)))
   ;; (trace! (👁 bc [prod] $ab $rb (MkBudget $size $depth) (: (, $x $y) (, $a $b)))
   (if (and (<= 3 $size) (<= 1 $depth))
       ;; Enough budget
       (let* (;; Recurse on $x
              ((, (MkBudget $xsize $xdepth) (: $x $a))
               (bc $ab $rb (MkBudget (- $size 2) (- $depth 1)) (: $x $a)))
              ;; Recurse on $y
              ((, (MkBudget $ysize $ydepth) (: $y $b))
               (bc $ab $rb (MkBudget (+ $xsize 1) $depth) (: $y $b))))
         ;; Output answer
         (, (MkBudget $ysize (min $xdepth $ydepth)) (: (, $x $y) (, $a $b))))
       ;; Not enough budget
       (empty)))
   ;; )
