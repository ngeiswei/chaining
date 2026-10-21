;; Tests for lib_possibly_lt.pl, the @<? ("possibly less than") operator.
;;
;; Run from this directory:
;;   sh ~/Work/TrueAGI/PeTTa/run.sh -s ./test_lib_possibly_lt.metta

;; Load the Prolog library and register @<? as a MeTTa function.
!(translatePredicate (consult "./lib_possibly_lt.pl"))
!(import_prolog_function @<?)

;; ---- Stable (definite) comparisons ----------------------------------------

!(test (@<? a f) True)
!(test (@<? f a) False)
!(test (@<? (f a) (f b)) True)
!(test (@<? (f b) (f a)) False)
!(test (@<? 1 2) True)
!(test (@<? 2 1) False)

;; ---- Rigid functor / type differences cannot be overturned ----------------

!(test (@<? (f $x) (g $y)) True)
!(test (@<? (g $x) (f $y)) False)
!(test (@<? (h $x) f) False)
!(test (@<? f (h $x)) True)
!(test (@<? f (f a)) True)
!(test (@<? (f a) f) False)

;; ---- Variables make the comparison undecided => possibly less-than --------

!(test (@<? f $x) True)
!(test (@<? $x f) True)
!(test (@<? $x $y) True)
!(test (@<? (f $x) (f a)) True)
!(test (@<? (f a) (f $x)) True)
!(test (@<? (f $x $y) (f $x $z)) True)

;; ---- A variable is never less than itself ---------------------------------

!(test (@<? (f $x) (f $x)) False)
!(test (@<? (h $x a) (h $x a)) False)
!(test (@<? ($x) ($x)) False)

;; ---- Lists behave like compounds ------------------------------------------

!(test (@<? (a 1) (b 1)) True)
!(test (@<? (b 1) (a 1)) False)
