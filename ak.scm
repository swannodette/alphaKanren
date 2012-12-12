#lang r5rs

(define-syntax pmatch
  (syntax-rules (else guard)
    ((_ (op arg ...) cs ...)
     (let ((v (op arg ...)))
       (pmatch v cs ...)))
    ((_ v) (if #f #f))
    ((_ v (else e0 e ...)) (begin e0 e ...))
    ((_ v (pat (guard g ...) e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch v cs ...))))
       (ppat v pat
         (if (and g ...) (begin e0 e ...) (fk))
         (fk))))
    ((_ v (pat e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch v cs ...))))
       (ppat v pat (begin e0 e ...) (fk))))))

(define-syntax ppat
  (syntax-rules (_ quote unquote)
    ((_ v _ kt kf) kt)
    ((_ v () kt kf) (if (null? v) kt kf))
    ((_ v (quote lit) kt kf)
     (if (equal? v (quote lit)) kt kf))
    ((_ v (unquote var) kt kf) (let ((var v)) kt))
    ((_ v (x . y) kt kf)
     (if (pair? v)
       (let ((vx (car v)) (vy (cdr v)))
         (ppat vx x (ppat vy y kt kf) kf))
       kf))
    ((_ v lit kt kf) (if (equal? v (quote lit)) kt kf))))

;(define h
;  (lambda (x y)
;    (pmatch `(,x . ,y)
;      ((,a . ,b) (guard (number? a) (number? b)) (+ a b))
;      ((_ . ,c) (guard (number? c)) (* c c))
;      (else (* x x)))))

(define-syntax mv-let
  (syntax-rules ()
    ((_ ((x ...) e) b0 b ...)
     (pmatch e ((x ...) b0 b ...)))))

;(mv-let ((,x ,y ,z) (list 1 2 3)) (+ x y z))

(define var
  (lambda (ignore)
    (letrec ((s (list 'susp '() (lambda () s))))
      s)))

;; epsilon - set of equations
;; rho     - substitution
;; delta   - set of constraints
;; udelta  - a delta in which all terms are unbound variables

;(define unify
;  (lambda (epsilon rho udelta fk)
;    (let ((epsilon (apply-subst rho epsilon)))
;      (mv-let ((rho^ delta) (apply-rho-rules epsilon fk))
;        (unify# delta (compose-subst rho rho^) udelta fk)))))
;
;(define unify#
;  (lambda (delta rho udelta fk)
;    (let ((delta (apply-subst rho delta))
;          (udelta (apply-subst rho udelta)))
;      (let ((delta (delta-union udelta delta)))
;        (list rho (apply-udelta-rules delta fk))))))
      
