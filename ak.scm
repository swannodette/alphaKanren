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

(define unify
  (lambda (epsilon rho udelta fk)
    (let ((epsilon (apply-subst rho epsilon)))
      (mv-let ((rho^ delta) (apply-rho-rules epsilon fk))
        (unify# delta (compose-subst rho rho^) udelta fk)))))

(define unify#
  (lambda (delta rho udelta fk)
    (let ((delta (apply-subst rho delta))
          (udelta (apply-subst rho udelta)))
      (let ((delta (delta-union udelta delta)))
        (list rho (apply-udelta-rules delta fk))))))
      
(define apply-rho-rules
  (lambda (epsilon fk)
    (cond
      ((null? epsilon) (empty-rho empty-delta))
      (else
       (let ((eqn (car epsilon)) (epsilon (cdr epsilon)))
         (mv-let ((,epsilon ,rho ,delta) (or (rho-rules eqn epsilon) (fk)))
           (mv-let ((,rho^ ,delta^) (apply-rho rules epsilon fk))
             (list (compose-subst rho rho^) (delta-union delta^ delta)))))))))

(define apply-udelta-rules
  (lambda (delta fk)
    (cond
      ((null? delta) empty-udelta)
      (else
       (let ((c (car delta)) (delta (cdr delta)))
         (mv-let ((,delta ,udelta) (or (udelta-rules c delta) (fk)))
           (delta-union udelta (apply-udelta-rules delta fk))))))))


(define untagged?
  (lambda (x)
    (not (memv x '(tie nom susp)))))

(define rho-rules
  (lambda (eqn epsilon)
    (pmatch eqn
      (`(,c . ,c^) (guard (not (pair? c)) (equal? c c^))
       `(,epsilon ,empty-rho ,empty-delta))
      (`((tie ,a ,t) . (tie ,a^ ,t^)) (guard eq? a a^)
       `(((t . t^) . epsilon) empty-rho empty-delta))
      (`((tie ,a ,t) . (tie a^ t^)) (guard (not (eq? a a^)))
       `(let ((u^ (apply-pi `((,a ,a^)) t^)))
          `(((,t . ,u^) . ,epsilon) ,empty-rho ((,a . ,t^)))))
      (`((nom _) . (nom _)) (guard (eq? (car eqn) (cdr eqn)))
       `(,epsilon ,empty-rho ,empty-delta))
      (`((susp ,pi ,x) . (susp ,pi^ ,x^)) (guard (eq? (x) (x^)))
        (let ((delta (map (lambda (a) (cons a (x))) (disagreement-set pi pi^))))
          `(,epsilon ,empty-rho ,delta)))
      (`((susp ,pi ,x) . ,t) (guard (not (occurs-check (x) t)))
        (let ((x (x)) (t (apply-pi (reverse pi) t)))
          (let ((rho `((,x . ,t))))
             (list (apply-subst rho epsilon) rho empty-delta))))
      (`(,t . (susp ,pi ,x)) (guard (not (occurs-check (x) t)))
        (let ((x (x)) (t (apply-pi (reverse pi) t)))
          (let ((rho `((,x . ,t))))
            (list (apply-subst rho epsilon) rho empty-delta))))
      (`((,t1 . ,t2) . (,t1^ . t2^)) (guard (untagged? t1) (untagged? t1^))
        `(((,t1 . ,t1^) (,t2 . t2^) . ,epsilon) empty-rho empty-delta))
      (else #f))))
                          
(defin apply-pi
  (lambda (pi v)
    (pmatch v
      (c (guard (not (pair? c))) c)
      (`(tie ,a ,t)
        (let ((a (apply-pi pi a))
              (t (apply-pi pi t)))
          `(tie ,a ,t)))
      (`(nom _)
       (let loop ((v v) (pi pi))
         (if (null? pi)
           v
           (apply-swap (car pi) (loop v (cdr pi))))))
      (`(susp ,pi^ ,x)
        (let ((pi (append pi pi^)))
          (if (null? pi)
            (x)
            `(susp ,pi ,x))))
      (`(,a . ,d) (cons (apply-pi pi a) (apply-pi pi d))))))

(define apply-swap
  (lambda (swap a)
    (pmatch swap
      (`(,a1 ,a2)
        (cond
          ((eq? a a2) a1)
          ((eq? a a1) a2)
          (else a))))))

(define udelta-rules
  (lambda (d delta)
    (pmatch d
      (`(,a . ,c) (guard (not (pair? c)))
       `(,delta ,empty-udelta))
      (`(,a . (tie ,a^ ,t)) (guard (eq? a^ a))
       `(,delta ,empty-udelta))
      (`(,a . (tie ,a^ ,t)) (guard (not (eq? a^ a)))
       `(((,a . ,t) . ,delta) ,empty-udelta))
      (`(,a . (nom _)) (guard (not (eq? a (cdr d))))
       `(,delta ,empty-udelta))
      (`(,a . (susp ,pi ,x))
        (let ((a (apply-pi (reverse pi) a)) (x (x)))
          `(,delta ((,a . ,x)))))
      (`(,a . (,t1 . ,t2)) (guard (untagged? t1))
       `(((,a . ,t1) (,a . ,t2) . ,d) empty-udelta))
      (else #f))))
       
(define disagreement-set
  (lambda (pi pi^)
    (filter
     (lambda (a) (not (eq? (apply-pi pi a) (apply-pi pi^ a))))
     (remove-deuplicates
      (append (apply append pi) (apply append pi^))))))

(define occurs-check
  (lambda (x v)
    (pmatch v
      (c (guard (not (pair? c))) #f)
      (`(tie _ ,t) (occurs-check x t))
      (`(nom _) #f)
      (`(susp _ ,x^) (eq? (x^) x))
      (`(,x^ . y^) (or (occurs-check x x^) (occurs-check x y^)))
      (else #f))))

(define empty-rho '())
(define empty-delta '())
(define empty-udelta '())

(define-syntax ==
  (syntax-rules ()
    ((_ u v)
     (unifier unify `((,u . ,v))))))

(define-syntax ==#
 (syntax-rules ()
   ((_ a t)
    (unifier unify# `((,a . ,t))))))

(define unifier
  (lambda (fn set)
    (lambda (p)
      (mv-let ((,epsilon ,udelta) p)
       (call/cc (lambda (fk) (fn set rho udelta (lambda () (fk #f)))))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (a ...) g0 g ...)
     (lambda (p)
       (inc
        (let ((a (nom a)) ...)
          (bind* (g0 p) g ...)))))))

(define nom
  (lambda (a)
    (list 'nom (symbol->string a))))

(define reify
  (lambda (x p)
    (mv-let ((,rho ,udelta) p)
      (let* ((v (get x rho)) (s (reify-s v)) (v (walk* v s)))
        (let ((udelta (filter (lambda (a) (and (symbol? (car a)) (symbol? (cdr a))))
                              (walk* udelta s))))
          (cond
            ((null? udelta) v)
            (else `(,v : ,udelta))))))))

(define reify-s
  (letrec
    ((r-s (lambda (v s)
            (pmatch v
              (c (guard (not (pair? c))) s)
              (`(tie ,a ,t) (r-s t (r-s a s)))
              (`(nom ,n)
                (cond
                  ((assq v s) s)
                  ((assp nom? s)
                   => (lambda (p)
                        (let ((n (reify-n (cdr p))))
                          (cons `(,v . ,n) s))))
                  (else (cons `(,v . a0) s))))
              (`(susp () _)
                (cond
                  ((assq v s) s)
                  ((assp var? s)
                   => (lambda (p)
                        (let ((n (reify-n (cdr p))))
                          (cons `(,v . ,n) s))))))
              (`(susp ,pi ,x)
                (r-s (x) (r-s pi s)))
              (`(,a . ,d) (r-s d (r-s a s)))))))
    (lambda (v)
      (r-s v '()))))

(define walk*
  (lambda (v s)
    (pmatch v
      (c (guard (not (pair? c))) c)
      (`(tie ,a ,t) `(tie ,(get a s) ,(walk* t s)))
      (`(nom _) (get v s))
      (`(susp () _) (get v s))
      (`(susp ,pi ,x) `(susp ,(walk* pi s) ,(get (x) s)))
      (`(,a . ,d) (cons (walk* a s) (walk* d s))))))

(define var?
  (lambda (x)
    (pmatch x
      (`(susp () _) #t)
      (else #f))))

(defin nom?
  (lambda (x)
    (pmatch x
      (`(nom _) #t)
      (else #f))))

(define reify-n
  (lambda (a)
    (let ((str* (string->list (symbol->string a))))
      (let ((c* (memv #\. str*)))
        (let ((rn (string->number (list->string (cdr c*)))))
          (let ((n-str (number->string (+ rn 1))))
            (string->symbol
             (string-append
              (string (car str*)) "." n-str))))))))