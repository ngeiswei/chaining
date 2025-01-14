;; Attempt to represent MeTTa-calculus operational semantics in MeTTa

;;;;;;;;;;;;
;; Syntax ;;
;;;;;;;;;;;;

;;;;;;;;;;;;;
;; Process ;;
;;;;;;;;;;;;;

;; Empty process, 0
(: ε Process)

;; For comprehension, for(t<->x)P
(: for (-> Term (-> Name (-> Process Process))))

;; Acknowledgement, x?P
(: ? (-> Name (-> Process Process)))

;; Dereference, *x
(: ⋆ (-> Name Process))

;; Parallel composition, P|Q
(: | (-> Process (-> Process Process)))

;;;;;;;;;;
;; Name ;;
;;;;;;;;;;

;; Quotation, @P
(: @ (-> Process Name))

;;;;;;;;;;
;; Term ;;
;;;;;;;;;;

;; Atom is a subtype of Term
(<: Atom Term)

;; ???, ([t])
(: ([]) (-> Term Term))

;;;;;;;;;;
;; Atom ;;
;;;;;;;;;;

;; Name is a subtype of Atom
(<: Name Atom)

;; Process is a subtype of Atom
(<: Process Atom)

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operational Semantics ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

NEXT
