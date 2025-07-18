;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example of probabilistic backward chaining. ;;
;;                                             ;;
;; Inspired from problog.                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Import random module
!(import! &self random)

;;;;;;;;;
;; Nat ;;
;;;;;;;;;

;; Define Nat
(: Nat Type)
(: Z Nat)
(: S (-> Nat Nat))

;; Define cast functions between Nat and Number
(: fromNumber (-> Number Nat))
(= (fromNumber $n) (if (<= $n 0) Z (S (fromNumber (- $n 1)))))
(: fromNat (-> Nat Number))
(= (fromNat Z) 0)
(= (fromNat (S $k)) (+ 1 (fromNat $k)))

;;;;;;;;;;
;; When ;;
;;;;;;;;;;

;; Run the code if the condition is true, otherwise prune the branch
(: when (-> Bool Atom $a))
(= (when $c $x) (if $c $x (empty)))

;;;;;;;;;;;;;;;;;;;;
;; Knowledge base ;;
;;;;;;;;;;;;;;;;;;;;

!(bind! &kb (new-space))

;; https://dtai.cs.kuleuven.be/problog/tutorial/tutslides/01_basic.html

;; 0.8::stress(ann).
;; ;; % 0.4::stress(bob).
;; 0.6::influences(ann,bob).
;; 0.2::influences(bob,carl).

;; smokes(X) :- stress(X).
;; smokes(X) :- influences(Y,X), smokes(Y).

;; query(smokes(carl)).

;; !(add-atom &kb (: 0.8 sa (stress ann)))
;; !(add-atom &kb (: 0.6 iab (influences ann bob)))
;; !(add-atom &kb (: 0.5 iab (influences ann henry)))
;; !(add-atom &kb (: 0.4 iab (influences henry carl)))
;; !(add-atom &kb (: 0.2 ibc (influences bob carl)))
;; !(add-atom &kb (: 1 ss (-> (stress $x)
;;                            (smokes $x))))
;; !(add-atom &kb (: 1 iss (-> (influences $y $x) (smokes $y)
;;                             (smokes $x))))

;; throws(john).
!(add-atom &kb (: 1 tj (throws john)))
!(add-atom &kb (: 0.5 tm (throws mary)))
!(add-atom &kb (: 0.8 tmb (-> (: $x (throws mary)) (break $x))))
!(add-atom &kb (: 0.6 tjb (-> (throws john) break)))

P(break) = P(A) + P(B) - P(A and B)
P(break) = 0.4 + 0.6 - 0.4*0.6

;; query(break).
;; query(throws(_)).


;; !(add-atom &kb (: 0.9 a A))
;; !(add-atom &kb (: 0.8 ab (R A B)))
;; !(add-atom &kb (: 0.7 bc (R B C)))
;; !(add-atom &kb (: 0.6                 ; Probability
;;                   ModusPonens         ; Name
;;                   (-> (R $p $q)       ; Premise 1
;;                       $p              ; Premise 2
;;                       $q)))           ; Conclusion
;; !(add-atom &kb (: 0.7
;;                   .
;;                   (-> (-> $pbl1 $a $b)
;;                       (-> $pbl2 $b $c)
;;                       (-> $? $a $c))))

;; (: $proof $theorem)

;; []
;; (: P1 T2)
;; ...
;; (: Pn Tn)

;; (: 0.1 0 Nat)
;; (: 0.1*0.1 1 Nat)
;; ...

;; (: "" String)
;; ...

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Probabilistic Backward chainer ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Probabilistic Backward Chainer.  The arguments of the backward
;; chainer are:
;;
;; * Knowledge base: pointer to a space containing axioms and rules in
;;   the format (: <PROB> <NAME> <RULE>).  Where <PROB> is the
;;   probability of triggering the rule.
;;
;; * Query: a metta term of the form (: <PROOF> <THEOREM>) where
;;   <PROOF> and <THEOREM> may contain free variables that may be
;;   filled by the backward chainer.
;;
;; * Maximum depth: maximum depth of the generated proof tree.
;;
;; A result is the query with its variables grounded, fully or
;; partially.  If multiple results are possible, they are returned as
;; a superposition.
(: pbc (-> $a                            ; Knowledge base space
           Nat                           ; Maximum depth
           $b                            ; Query
           $b))                          ; Result
;; Base case
(= (pbc $kb $_ (: $pbl $prf $ccln))
   (trace! (👁 pbc-base $_ (: $pbl $prf $ccln))
   (match $kb (: $pbl $prf $ccln)
          (when (< (random-float &rng 0 1) $pbl)
            (: $pbl $prf $ccln)))))
;; Recursive step
;; Unary application
(= (pbc $kb (S $k) (: $pbl ($prfabs $prfarg) $ccln))
   (trace! (👁 pbc-rec1 (S $k) (: $pbl ($prfabs $prfarg) $ccln))
   (let* (;; Recurse on abstraction
          ((: $pblabs $prfabs (-> $prms $ccln))
           (pbc $kb $k (: $pblabs $prfabs (-> $prms $ccln))))
          ;; Recurse on argument
          ((: $pblarg $prfarg $prms)
           (pbc $kb $k (: $pblarg $prfarg $prms)))
          ;; Calculate probability of application
          ($pbl (* $pblabs $pblarg)))
     (: $pbl ($prfabs $prfarg) $ccln))))
;; Binary application
(= (pbc $kb (S $k) (: $pbl ($prfabs $prfarg1 $prfarg2) $ccln))
   (trace! (👁 pbc-rec2 (S $k) (: $pbl ($prfabs $prfarg1 $prfarg2) $ccln))
   (let* (;; Recurse on abstraction
          ((: $pblabs $prfabs (-> $prms1 $prms2 $ccln))
           (pbc $kb $k (: $pblabs $prfabs (-> $prms1 $prms2 $ccln))))
          ;; Recurse on first argument
          ((: $pblarg1 $prfarg1 $prms1)
           (pbc $kb $k (: $pblarg1 $prfarg1 $prms1)))
          ;; Recurse on second argument
          ((: $pblarg2 $prfarg2 $prms2)
           (pbc $kb $k (: $pblarg2 $prfarg2 $prms2)))
          ;; Calculate probability of application
          ($pbl (* $pblabs (* $pblarg1 $pblarg2))))
     (: $pbl ($prfabs $prfarg1 $prfarg2) $ccln))))

;;;;;;;;;;;
;; Tests ;;
;;;;;;;;;;;

!(set-random-seed &rng 6)

;; !(pbc &kb (fromNumber 0) (: $pbl $prf A))
;; !(pbc &kb (fromNumber 2) (: $pbl $prf B))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf C))


;; ;; !(pbc &kb (fromNumber 0) (: $pbl $prf $thrm))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf (smokes carl)))
;; !(pbc &kb (fromNumber 3) (: $pbl $prf $thrm))

!(pbc &kb (fromNumber 3) (: $pbl $prf break))
