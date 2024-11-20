#lang racket
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define problem1 "
put your answer here
you can use multiple lines if you want==
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct rnum (n) #:transparent
  #:guard (struct-guard/c number?))
(struct radd (e1 e2) #:transparent
  #:guard (struct-guard/c (recursive-contract rexpr/c) (recursive-contract rexpr/c)))
(struct rret (e) #:transparent
  #:guard (struct-guard/c (recursive-contract rexpr/c)))
(struct rlam (id body) #:transparent
  #:guard (struct-guard/c string? (recursive-contract rexpr/c)))
(struct rapp (e1 e2) #:transparent
  #:guard (struct-guard/c (recursive-contract rexpr/c) (recursive-contract rexpr/c)))
(struct rident (id) #:transparent
  #:guard (struct-guard/c string?))

(define rexpr/c (or/c rnum? radd? rret? rlam? rapp? rident?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; retlang interpreter

; subst: expr -> expr
; substitutes an expression in for a given identifier
(define (subst expr id repl)
  (match expr
    [(rnum n) (rnum n)]
    [(radd e1 e2) (radd (subst e1 id repl) (subst e2 id repl))]
    [(rret e) (rret (subst e id repl))]
    [(rlam id2 body)
     (if (equal? id id2)
         (rlam id2 body) ; shadow
         (rlam id2 (subst body id repl)))]
    [(rapp e1 e2) (rapp (subst e1 id repl) (subst e2 id repl))]
    [(rident id2) (if (equal? id id2) repl (rident id2))]))

; rinterp: expr -> rvalue(rnum or rlam)
; Runs a givne retlang expresion to a value
(define/contract (rinterp e)
  (-> rexpr/c rexpr/c)
  (rinterp-k e (lambda (r) r)))

;; rinerp-k : expr -> rvalue
; runs a given retlang expression using a continutation
(define (rinterp-k e cont)
  (match e
    [(rnum n)
     (cont (rnum n))]
    [(radd e1 e2) (rinterp-k e2
                             (lambda (r2) (rinterp-k e1  (lambda (r1)
                                                          
                                                           (cont (rnum (+ r1 r2)))))))]
    [(rret e) (rinterp-k e (lambda (k) k))]
    ))

  

(check-equal? (rinterp (rret (rnum 1))) (rnum 1))
(check-equal? (rinterp (radd (rnum 12) (rret (rnum 1)))) (rnum 1))
(check-equal? (rinterp (radd (rret (rnum 1)) (rret (rnum 2)))) (rnum 2))
(check-equal? (rinterp (radd (radd (radd (rnum 1) (rret (rnum 2000000))) (rnum 1)) (rnum 1))) (rnum 2000000))
(check-equal? (rinterp (radd (radd (radd (rnum 1) (rret (rnum 1))) (rret (rnum 12000000000))) (rnum 1))) (rnum 12000000000))


;(check-equal? (rinterp (rapp (rlam "x" (eident "x")) (enum 1))) (enum 1))
;(check-equal? (rinterp (rapp (rlam "x" (eident "x")) (rret (enum 12)))) (enum 12))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; λ-calculus interpreter

(struct lident (s) #:transparent
  #:guard (struct-guard/c string?))
(struct llam (id body) #:transparent
  #:guard (struct-guard/c string? (recursive-contract lexpr/c)))
(struct lnum (n) #:transparent
  #:guard (struct-guard/c number?))
(struct ladd (e1 e2) #:transparent
  #:guard (struct-guard/c (recursive-contract lexpr/c) (recursive-contract lexpr/c)))
(struct lapp (e1 e2) #:transparent
  #:guard (struct-guard/c (recursive-contract lexpr/c) (recursive-contract lexpr/c)))
(struct lerror () #:transparent)
(define lexpr/c (or/c lident? llam? lnum? ladd? lapp? lerror?))

;;; subst : expr -> string -> expr -> expr
;;; performs the substitution e1[x |-> e2] with lexical scope
;;; assumes e1 has no free variables
(define (l-subst e1 id e2)
  (match e1
    [(lident x)
     (if (equal? x id) e2 (lident x))]
    [(llam x body)
     (if (equal? x id)
         (llam x body) ; shadowing case; do nothing
         (llam x (l-subst body id e2)) ; non-shadowing case
         )]
    [(lapp f arg)
     (lapp (l-subst f id e2) (l-subst arg id e2))]
    [(lnum n) (lnum n)]
    [(lerror) (lerror)]
    [(ladd l r)
     (ladd (l-subst l id e2) (l-subst r id e2))]))

;;; evaluates an expression to an expression
(define/contract (interp-l e)
  (-> lexpr/c lexpr/c)
  (match e
    [(lident x) (error "unbound ident")]
    [(lnum n) (lnum n)]
    [(lerror) (error 'runtime)]
    [(llam id x) (llam id x)]
    [(ladd e1 e2)
     (lnum (+ (lnum-n (interp-l e1))
              (lnum-n (interp-l e2))))]
    [(lapp e1 e2)
     (match (interp-l e1)
       [(llam id body)
        (let* [(arg-v (interp-l e2))
               (l-subst-body (l-subst body id arg-v))]
          (interp-l l-subst-body))])]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; compiling retlang to lambda calculus

(define counter (box 0))
(define (fresh s)
  (set-box! counter (+ 1 (unbox counter)))
  (string-append s (number->string (unbox counter))))

(define/contract (compile e)
  (-> rexpr/c lexpr/c)
  (error 'implementme))

(define/contract (compile-and-run e)
  (-> rexpr/c lexpr/c)
  (interp-l (compile e)))
