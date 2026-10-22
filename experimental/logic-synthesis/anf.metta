;; Collection of functions to check ANF

;; Load the Prolog library and register @<? as a MeTTa function.
!(translatePredicate (consult "./lib_possibly_lt.pl"))
!(import_prolog_function @<?)

;; Return True iff $term is closed, that does not contain free
;; variable.
(: isClosed (-> Atom Bool))
(= (isClosed $term)
   (case (get-metatype $term)
     ((Variable False)
      (Symbol True)
      (Grounded True)
      (Expression (if (== $term ())
                      True
                      (let* (($head (car-atom $term))
                             ($tail (cdr-atom $term)))
                        (and (isClosed $head) (isClosed $tail))))))))

;; Get first argument of (f x1 ... xn)
(= (getFstArg ($f $x)) $x)
(= (getFstArg ($f $x1 $x2)) $x1)
(= (getFstArg ($f $x1 $x2 $x3)) $x1)

;; Get second argument of (f x1 ... xn)
(= (getSndArg ($f $x1 $x2)) $x2)
(= (getSndArg ($f $x1 $x2 $x3)) $x2)

;; Check if $x is a binary call with a given operator.  It works on
;; any term, including those containing free variables.
(= (isBinaryOp $op $term)
   (if (is-expr $term)
       (case $term
         ((($f $x $y) (== $op $f))
          ($else False)))
       False))

;; Check if $x is a conjunction, meaning its root operator is ∧.
(= (isConjunction $x)
   (isBinaryOp ∧ $x))

;; Check if $x is a an exclusive disjunction, meaning its root operator is ⊻.
(= (isExclusiveDisjunction $x)
   (isBinaryOp ⊻ $x))

;; check if $x is the true predicate
(= (isTruePredicate $x)
   (== $x 𝕋))

;; check if $x is the false predicate
(= (isFalsePredicate $x)
   (== $x 𝔽))

;; Check if $x is a constant predicate, i.e. 𝔽 or 𝕋.  Note that unlike
;; isInductiveANF it does not recognize variable as potentially
;; constant predicate.
(= (isConstantPredicate $x)
   (or (isFalsePredicate $x) (isTruePredicate $x)))

;; Check if $x is a contingent atomic predicate (different than 𝔽/𝕋).
;; If $x is a variable then check if it could potentially be a
;; contingent atomic predicate.
(= (isContingentAtomicPredicate $x)
   (case (get-metatype $x)
     ((Symbol (not (isConstantPredicate $x)))
      (Grounded (not (isConstantPredicate $x)))
      (Variable True)
      (Expression False))))

;; Check if $term, assumed to be a conjunction of subterms in
;; algebraic normal form, is in algebraic normal form.  If (∧ $x $y)
;; is open (i.e. contain free variables) then check if it could
;; potentially be in ANF.
(= (isConjunctionInductiveANF (∧ $x $y))
   (and
    ;; Make sure that $x is well formed (left associative)
    (isContingentAtomicPredicate $x)
    ;; Make sure that the rest is well formed
    (if (isConjunction $y)
        (@<? $x (getFstArg $y))
        (and (isContingentAtomicPredicate $y)
             (@<? $x $y)))))

;; Check if $term, assumed to be an exclusive disjunction of subterms
;; in ANF, is in algebraic normal form.
(= (isExclusiveDisjunctionInductiveANF (⊻ $x $y))
   (and
    ;; Check that $x is not an exclusive disjunction (left
    ;; associative) and is not 𝔽 either.
    (and (not (isExclusiveDisjunction $x)) (not (isFalsePredicate $x)))
    ;; Check that the rest if well formed (assuming $y in ANF)
    (and (not (isFalsePredicate $y))
         (if (isExclusiveDisjunction $y)
             (@< $x (getFstArg $y))
             (@< $x $y)))))

;; Check that $term, at the first level of an ANF, that is shallowly
;; well formed (assuming its subterms are also in ANF).  Note that 𝔽
;; is not considered to belong to the first level since it can only
;; exist by itself.
(= (isFstLevelInductiveANF $term)
   (if (isConjunction $term)
       ;; Conjunction
       (isConjunctionInductiveANF $term)
       ;; Not conjunction
       (or (isTruePredicate $term)
           (isContingentAtomicPredicate $term))))

;; Check that $term, at the second level of an ANF, that is shallowly
;; well formed (assuming its subterms are ANF).
(= (isSndLevelInductiveANF $term)
   (if (isExclusiveDisjunction $term)
       ;; Exclusive disjunction
       (isExclusiveDisjunctionInductiveANF $term)
       ;; Not exclusive disjunction, then must be in first level ANF
       (isFstLevelInductiveANF $term)))

;; Check if $term, assumed to be itself made of subterms in algebraic
;; norm form, is in algebraic normal form.  It partially supports
;; terms that are not closed, in this case the check outputs whether
;; it could potentially be in normal form.
(= (isInductiveANF $term)
   (case (get-metatype $term)
     ((Symbol True)
      (Grounded True)
      (Variable True)
      (Expression
       (case $term
         (;; Conjunction
          ((∧ $x $y) (isConjunctionInductiveANF (∧ $x $y)))
          ;; ExclusiveDisjunction
          ((⊻ $x $y) (isExclusiveDisjunctionInductiveANF (⊻ $x $y)))
          ;; Otherwise
          ($else False)))))))

;; Check $term is in algebraic normal form.
(= (isANF $term)
   (if (is-expr $term)
       ;; Expression
       (case $term
         (;; Binary application (the only possibility for ANF)
          (($f $x $y) (and (isANF $x)
                           (and (isANF $y)
                                (isInductiveANF $term))))
          ;; Otherwise
          ($else False)))
       ;; Not expression
       True))
