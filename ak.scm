#lang r5rs

(define filter 
  (lambda (pred l)
    (cond 
      ((null? l) '())
      ((pred (car l)) (cons (car l) (filter pred (cdr l))))
      (else (filter pred (cdr l))))))

(define reduce
  (lambda (f l acc)
    (cond
      ((null? l) acc)
      (else
       (reduce f (cdr l) (f acc (car l)))))))

(define remv
  (lambda (x l)
    (cond
      ((null? l) '())
      ((equal? x (car l)) (remv x (cdr l)))
      (else (cons (car l) (remv x (cdr l)))))))

(define remove-duplicates
  (lambda (l)
    (reduce (lambda (acc x) (remv x acc)) l l)))

(define assp
  (lambda (pred l)
    (cond
      ((null? l) #f)
      ((pred (caar l)) (caar l))
      (else (assp pred (cdr l))))))      

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

(define empty-s '())

(define ext-s-no-check
  (lambda (x v s)
    (cons `(,x . ,v) s)))

(define ext-s
  (lambda (x v s)
    (cond
      ((occurs-check x v s) #f)
      (else (ext-s-no-check x v s)))))

(define-syntax mzero
  (syntax-rules ()
    ((_) #f)))

(define-syntax unit
  (syntax-rules ()
    ((_ a) a)))

(define-syntax choice
  (syntax-rules ()
    ((_ a f) (cons a f))))

(define-syntax inc
  (syntax-rules ()
    ((_ e) (lambda () e))))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e 
        (() e0)     ; mzero
        ((f^) e1)   ; inc
        ((a^) e2)   ; unit
        ((a f) e3)) ; choice
     (let ((a-inf e))
       (cond
         ((not a-inf) e0)
         ((procedure? a-inf) (let ((f^ a-inf)) e1))
         ((and (pair? a-inf) (procedure? (cdr a-inf)))
          (let ((a (car a-inf))
                (f (cdr a-inf)))
            e3))
         (else (let ((a^ a-inf)) e2)))))))

(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

(define bind
  (lambda (a-inf g)
    (case-inf a-inf
      (()    (mzero))
      ((f)   (inc (bind (f) g)))
      ((a)   (g a))
      ((a f) (mplus (g a) (lambda () (bind (f) g)))))))

(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0 (lambda () (mplus* e ...))))))

(define mplus
  (lambda (a-inf f)
    (case-inf a-inf
      (()     (f))
      ((f^)   (inc (mplus (f) f^)))
      ((a)    (choice a f))
      ((a f^) (choice a (lambda () (mplus (f) f^)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g ...)
     (take n
       (lambda ()
         ((fresh (x) g0 g ...
            (lambda (a)
              (cons (reify x a) '())))
          empty-s))))))

(define take
  (lambda (n f)
    (if (and n (zero? n))
      '()
      (case-inf (f)
        (()    '())
        ((f)   (take n f))
        ((a)   a)
        ((a f) (cons (car a) (take (and n (- n 1)) f)))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambda (a)
       (inc
         (mplus* (bind* (g0 a) g ...)
                 (bind* (g1 a) g^ ...)
                 ...))))))

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
    (mv-let ((,rho^ ,delta) (apply-rho-rules epsilon rho fk))
      (unify# delta rho^ udelta fk))))
  
(define unify#
  (lambda (delta rho udelta fk)
    (let ((delta (delta-union udelta delta)))
      (list rho (apply-udelta-rules delta rho fk)))))
      
(define apply-rho-rules
  (lambda (epsilon fk)
    (cond
      ((null? epsilon) (empty-rho empty-delta))
      (else
       (let ((eqn (car epsilon)) (epsilon (cdr epsilon)))
         (mv-let ((,epsilon ,rho ,delta) (or (rho-rules eqn epsilon) (fk)))
           (mv-let ((,rho^ ,delta^) (apply-rho-rules epsilon fk))
             (list rho^ (delta-union delta^ delta)))))))))

(define apply-udelta-rules
  (lambda (delta rho fk)
    (cond
      ((null? delta) empty-udelta)
      (else
       (let ((c (car delta)) (delta (cdr delta)))
         (mv-let ((,delta ,udelta) (or (udelta-rules c rho delta) (fk)))
           (delta-union udelta (apply-udelta-rules rho delta fk))))))))


(define untagged?
  (lambda (x)
    (not (memv x '(tie nom susp)))))

(define rho-rules
  (lambda (eqn rho epsilon)
    (let ((eqn (cons (walk (car eqn) rho) (walk (cdr eqn) rho))))
      (pmatch eqn
        (`(,c . ,c^) (guard (not (pair? c)) (equal? c c^))
         `(,epsilon ,rho ,empty-delta))
        (`((tie ,a ,t) . (tie ,a^ ,t^)) (guard eq? a a^)
         `(((t . t^) . epsilon) ,rho ,empty-delta))
        (`((tie ,a ,t) . (tie ,a^ ,t^)) (guard (not (eq? a a^)))
         `(let ((u^ (apply-pi `((,a ,a^)) t^)))
            `(((,t . ,u^) . ,epsilon) ,rho ((,a . ,t^)))))
        (`((nom _) . (nom _)) (guard (eq? (car eqn) (cdr eqn)))
         `(,epsilon ,rho ,empty-delta))
        (`((susp ,pi ,x) . (susp ,pi^ ,x^)) (guard (eq? (x) (x^)))
         (let ((delta (map (lambda (a) (cons a (x))) (disagreement-set pi pi^))))
           `(,epsilon ,rho ,delta)))
        (`((susp ,pi ,x) . ,t) (guard (not (occurs-check (x) t)))
         (let ((rho (ext-s (x) (apply-pi (reverse pi) t) rho)))
           `(,epsilon ,rho ,empty-delta)))
        (`(,t . (susp ,pi ,x)) (guard (not (occurs-check (x) t)))
         (let ((rho (ext-s (x) (apply-pi (reverse pi) t) rho)))
           `(,epsilon ,rho ,empty-delta)))
        (`((,t1 . ,t2) . (,t1^ . t2^)) (guard (untagged? t1) (untagged? t1^))
         `(((,t1 . ,t1^) (,t2 . t2^) . ,epsilon) rho empty-delta))
        (else #f)))))
                          
(define apply-pi
  (lambda (pi v)
    (pmatch v
      (,c (guard (not (pair? c))) c)
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
  (lambda (d rho delta)
    (let ((d (cons (walk (car d) rho) (walk (cdr d) rho))))
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
       (else #f)))))
       
(define disagreement-set
  (lambda (pi pi^)
    (filter
      (lambda (a) (not (eq? (apply-pi pi a) (apply-pi pi^ a))))
      (remove-duplicates
       (append (apply append pi) (apply append pi^))))))

(define occurs-check
  (lambda (x v)
    (pmatch v
      (,c (guard (not (pair? c))) #f)
      (`(tie _ ,t) (occurs-check x t))
      (`(nom _) #f)
      (`(susp _ ,x^) (eq? (x^) x))
      (`(,x^ . ,y^) (or (occurs-check x x^) (occurs-check x y^)))
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
      (mv-let ((,rho ,udelta) p)
       (call-with-current-continuation (lambda (fk) (fn set rho udelta (lambda () (fk #f)))))))))

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
      (let* ((v (walk* x rho)) (s (reify-s v)) (v (apply-reify-s v s)))
        (let ((udelta (filter (lambda (a) (and (symbol? (car a)) (symbol? (cdr a))))
                              (apply-reify-s udelta s))))
          (cond
            ((null? udelta) v)
            (else `(,v : ,udelta))))))))

(define reify-s
  (letrec
    ((r-s (lambda (v s)
            (pmatch v
              (,c (guard (not (pair? c))) s)
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

(define apply-reify-s
  (lambda (v s)
    (pmatch v
      (,c (guard (not (pair? c))) c)
      (`(tie ,a ,t) `(tie ,(assq a s) ,(apply-reify-s t s)))
      (`(nom _) (assq v s))
      (`(susp () _) (assq v s))
      (`(susp ,pi ,x)
        (list 'susp
          (map (lambda (swap)
                 (pmatch swap
                   (`(,a ,b) (list (assq a s) (assq b s)))))
               pi)
          (assq (x) s)))
      (`(,a . ,d) (cons (apply-reify-s a s) (apply-reify-s d s))))))

(define var?
  (lambda (x)
    (pmatch x
      (`(susp () _) #t)
      (else #f))))

(define nom?
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

(define walk
  (lambda (x s)
    (let loop ((x x) (pi '()))
      (pmatch x
        (`(susp ,pi^ ,v)
          (let ((v (assq (v) s)))
            (cond
              (v (loop (cdr v) (append pi^ pi)))
              (else (apply-pi pi x)))))
        (else (apply-pi pi x))))))

(define walk*
  (lambda (v s)
    (let ((v (walk v s)))
      (pmatch v
        (`(tie ,a ,t) `(tie ,a ,(walk* t s)))
        (`(,a . ,d) (guard (untagged? a))
          (cons (walk* a s) (walk* d s)))
        (else v)))))

(define delta-union
  (lambda (delta delta^)
    (pmatch delta
      (() delta^)
      (`(,d . ,delta)
        (if (term-member? d delta^)
          (delta-union delta delta^)
          (cons d (delta-union delta delta^)))))))

(define term-member?
  (lambda (v v*)
    (pmatch v*
      (() #f)
      (`(,v^ . ,v*)
        (or (term-equal? v^ v) (term-member? v v*))))))

(define term-equal?
  (lambda (u v)
    (pmatch `(,u ,v)
      (`(,c ,c^) (guard (not (pair? c)) (not (pair? c^)))
        (equal? c c^))
      (`((tie ,a ,t) (tie ,a^ ,t^))
        (and (eq? a a^) (term-equal? t t^)))
      (`((nom _) (nom _)) (eq? u v))
      (`((susp ,pi ,x) (susp ,pi^ ,x^))
        (and (eq? (x) (x^)) (null? (disagreement-set pi pi^))))
      (`((,x . ,y) (,x^ . ,y^))
        (and (term-equal? x x^) (term-equal? y y^)))
      (else #f))))
