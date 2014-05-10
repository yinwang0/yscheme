;;; An optimizing compiler from Scheme to X86_64.
;;; author: Yin Wang (yw21@cs.indiana.edu)
;;; As final submission for P523 (Spring 2009)


;; Here is my final submission of the complete compiler. I had lots of fun
;; in writing it learned many invaluable experiences from the course how to
;; build a robust compiler by ensuring each pass (transformation) to be
;; correct. I owe many thanks to Prof. Dybvig and Andy for their immense
;; help!



;;;;;;;;;;;;;;;
;; Additions ;;
;;;;;;;;;;;;;;;

;; A15 has parse-scheme with the whole compiler, including all passes in
;; Challenge assignments A, B and some additions just for fun:

; - pre-optimize. an additional optimization pass which does some constant
; propagation. It is inserted after purify-letrec. It can help eliminate
; some closures and free variables.

; - boxes. primitives box, unbox and set-box! and changed
; convert-assignments to use these primitive instead of pairs. This can
; save some heap space.


;;;;;;;;;;;;;;;;;;;;
;; Removed Passes ;;
;;;;;;;;;;;;;;;;;;;;

;; Several passes in the original set are removed but their functionalities
;; are all contained naturally in other passes:

; - uncover-free, uncover-well-known, optimize-free, optimize-known-call,
;   optimize-self-reference:
;;     subsumed by convert-closures.

; - flatten-set!:
;;     subsumed by remove-complex-opera*


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Experimental Results ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here is some experimental results from running (test-all-analyze) defined
; at the end of this file, which can output statistics of closure number,
; free variable number, and code size etc. The experiments are done with
; the final test set of A15 with 163 programs.


;;; ** all optimizations

; I have identified four non-trivial optimizations. They are
; enabled/disabled by the following four global parameters.

;; *enable-forward-locations*
;; *enable-pre-optimize*
;; *enable-optimize-jumps*
;; *enable-closure-optimization*

; With all optimizations enabled, the total code size is reduced by about
; 37%. When in effect separately, they have different reduction factors:

; closure optimization: 22%
; forward-locations: 16%
; pre-optimize: 2%
; optimize-jumps: 1%

; Closure optimization has the most contribution to the code size,
; location forwarding second.

;; +-------------+------------+------------+------------+------------+------------+
;; |all disabled |all enabled |  opt.jump  | forw.loc.  |  pre.opt   |  clos.opt  |
;; +-------------+------------+------------+------------+------------+------------+
;; |    9584     |    6050    |  9474(1%)  | 8042(16%)  |  9354(2%)  | 7483(22%)  |
;; +-------------+------------+------------+------------+------------+------------+



;;; **  pre-optimize vs. forward-locations

; These two passes are similar because they both do sort-of partial
; evaluation. It would make sense to see how they compare in their
; effectiveness on the code size. The following table is the total code
; size under the combinations of pre-optimize and forward-locations. All
; other optimizations are disabled in order to see their pure effects.

; From the table we can see that foward-locations has much more effect on
; the code size than pre-optimize, while both have their own benefits.
; forward-locations has reduced the total code size by 14%, while
; pre-optimize 2%. Their effects are not additive. When they combined, the
; code size is reduced only a few lines more than forward-locations working
; alone. So forward-locations pretty much subsumes pre-optimize w.r.t code
; length, but we will see the pre-optimization has its own benefits when it
; comes to closure size.

;; +--------------+----------+---------------------+
;; |  code size   |          |  forward-locations  |
;; +--------------+----------+----------+----------+
;; |              |          |  enable  | disable  |
;; |              +----------+----------+----------+
;; | pre-optimize |  enable  |   8158   |   9354   |
;; |              +----------+----------+----------+
;; |              | disable  |   8173   |   9558   |
;; +--------------+----------+----------+----------+




;;; ** pre-optimize vs. closure optimization

; The two optimizations pre-optimize and closure optimization (contained in
; convert-closures) interact to reduce the closure number and sizes. The
; following table shows the closure number and total number of free
; variable under different settings.

; We can see that closure optimization effectively cut down 57% of the
; closures. While the effect of pre-optimize is small compared to closure
; optimization, it eliminated 5 closures which cannot be removed by closure
; optimization alone, and reduced the number of free variables.

;; +---------------+----------+----------------------+
;; |  clo# / fv#   |          |     closure opt.     |
;; +---------------+----------+----------+-----------+
;; |               |          |  enable  |  disable  |
;; |               +----------+----------+-----------+
;; | pre-optimize  |  enable  |  74/73   |  186/183  |
;; |               +----------+----------+-----------+
;; |               | disable  |  79/85   |  186/190  |
;; +---------------+----------+----------+-----------+


;; End of Documentation



;-------------------------------------------------------------
;                    load framework
;-------------------------------------------------------------

(optimize-level 3)
(case-sensitive #t)
(load "match.ss")
(load "helpers.ss")
(load "driver.ss")
(load "fmts.pretty")
(load "wrapper.ss")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; optimization switches
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; global variable automatically set by test-all-analyze,
; don't change by hand!
(define *enable-analyze* #f)

(define *enable-forward-locations* #t)
(define *enable-pre-optimize* #t)
(define *enable-optimize-jumps* #t)
(define *enable-closure-optimization* #t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; new primitive tags
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mask-box #b111)
(define tag-box  #b100)
(define size-box 8)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; utilities for the whole compiler
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax letv*
  (syntax-rules ()
    [(_ () body ...) (begin body ...)]
    [(_ ([(x0 ...) v0] [x1 v1] ...) body ...)
     (let-values ([(x0 ...) v0])
       (letv* ([x1 v1] ...) body ...))]
    [(_ ([x0 v0] [x1 v1] ...) body ...)
     (letv* ([(x0) v0] [x1 v1] ...) body ...)]))

(define-syntax peek
  (syntax-rules ()
    [(_ x) (printf "~a = ~a\n\n" 'x x)]
    [(_ x y ...)
     (begin (printf "~a = ~a\n" 'x x)
            (peek y ...))]))


(define id (lambda (v) v))

(define orall
  (lambda (ls)
    (cond
     [(null? ls) #f]
     [(car ls) #t]
     [else (orall (cdr ls))])))

(define location?
  (lambda (x)
    (or (register? x) (frame-var? x) (uvar? x))))

(define prim?
  (lambda (x)
    (memq x '(+ - * logand logor sra = < <= >= >
                boolean? eq? fixnum? null? pair? box? vector? procedure?
                cons car cdr set-car! set-cdr!
                box unbox set-box!
                make-vector vector-length vector-ref vector-set!
                void))))

(define binop?
  (lambda (x)
    (memq x '(+ - * logand logor sra))))

(define relop?
  (lambda (x)
    (memq x '(= < <= >= >))))

(define mref?
  (lambda (x)
    (match x
      [(mref ,base ,off) #t]
      [,x #f])))

; get conflicting vars/regs of a variable
(define get-conflicts
  (lambda (x ct)
    (cdr (assq x ct))))

; remove a node from a conflict graph (non-destructive)
(define ct-remove-node
  (lambda (x ct)
    (let ([p (assq x ct)])
      (map (lambda (y) (cons (car y) (remq x (cdr y)))) (remq p ct)))))

; find the minimum from a list using key as the weight function
(define find-min
  (lambda (key ls)
    (let loop ([min (car ls)] [rest (cdr ls)])
      (cond
       [(null? rest) min]
       [(< (key (car rest)) (key min)) (loop (car rest) (cdr rest))]
       [else (loop min (cdr rest))]))))

; ((a . b) (c .d)) -> ((a b) (c d))
(define alist->list
  (lambda (assoc-ls)
    (map (lambda (x) (list (car x) (cdr x))) assoc-ls)))

; ((a b) (c d)) -> ((a . b) (c .d))
(define list->alist
  (lambda (ls)
    (map (lambda (x) (cons (car x) (cadr x))) ls)))

; make-begin takes a sequence or a begin form
(define make-begin
  (lambda (x)
    (define flatten
      (lambda (x)
        (match x
          [(begin ,[e*] ...)
           `(,e* ... ...)]
          [,x `(,x)])))
    (match x
      [(begin ,e* ...) `(begin ,@(flatten x))]
      [(,e) e]
      [(,e* ...) `(begin ,@(flatten `(begin ,e* ...)))])))



; A15

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; parse-scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-scheme parses normal Scheme input and does some normal checks.

(define parse-scheme
  (lambda (x)
    (define env0
      '([+              .  (+              2)]
        [-              .  (-              2)]
        [*              .  (*              2)]
        [logand         .  (logand         2)]
        [logor          .  (logor          2)]
        [sra            .  (sra            2)]

        [=              .  (=              2)]
        [<              .  (<              2)]
        [>              .  (>              2)]
        [<=             .  (<=             2)]
        [>=             .  (>=             2)]

        [boolean?       .  (boolean?       1)]
        [eq?            .  (eq?            2)]
        [fixnum?        .  (fixnum?        1)]
        [null?          .  (null?          1)]
        [pair?          .  (pair?          1)]
        [box?           .  (box?           1)]
        [vector?        .  (vector?        1)]
        [procedure?     .  (procedure?     1)]

        [cons           .  (cons           2)]
        [car            .  (car            1)]
        [cdr            .  (cdr            1)]
        [set-car!       .  (set-car!       2)]
        [set-cdr!       .  (set-cdr!       2)]

        [box            .  (box            1)]
        [unbox          .  (unbox          1)]
        [set-box!       .  (set-box!       2)]

        [make-vector    .  (make-vector    1)]
        [vector-length  .  (vector-length  1)]
        [vector-ref     .  (vector-ref     2)]
        [vector-set!    .  (vector-set!    3)]
        [void           .  (void           0)]))

    (define get-name cadr)
    (define get-argn caddr)
    (define unique-check
      (lambda (ls)
        (cond
         [(null? ls) '()]
         [(not (symbol? (car ls)))
          (error 'parse-scheme "parameter must be a symbol, but got ~a" (car ls))]
         [(memq (car ls) (cdr ls))
          (error 'parse-scheme "duplicated parameter ~a" (car ls))]
         [else (cons (car ls) (unique-check (cdr ls)))])))
    (define parse
      (lambda (env)
        (lambda (x)
          (match x
            [,x (guard (number? x))
             (if (and (exact? x) (fixnum-range? x))
                 `(quote ,x)
                 (error 'parse-scheme "not an exact number or out of range ~a" x))]
            [,x (guard (or (boolean? x) (null? x)))
             `(quote ,x)]
            [,x (guard (symbol? x))
             (cond
              [(assq x env) => cadr]
              [else (error 'parse-scheme "unbound variable ~a" x)])]
            [#(,[x*] ...)
             `(quote #(,x* ...))]
            [(,f ,x* ...) (guard (assq f env))
             (let ([p (assq f env)])
               (if (and (get-argn p) (not (= (length x*) (get-argn p))))
                   (error 'parse-scheme
                          "procedure ~a expects ~a arguments, but got ~a"
                          f (get-argn p) (length x*))
                   (map (parse env) `(,f ,x* ...))))]
            [(if ,[t] ,[c])
             `(if ,t ,c (void))]
            [(if ,[t] ,[c] ,[a])
             `(if ,t ,c ,a)]
            [(and ,x* ...)
             (cond
              [(null? x*) #t]
              [(null? (cdr x*)) ((parse env) (car x*))]
              [else `(if ,((parse env) (car x*))
                         ,((parse env) `(and ,@(cdr x*)))
                         '#f)])]
            [(or ,x* ...)
             (cond
              [(null? x*) #f]
              [(null? (cdr x*)) ((parse env) (car x*))]
              [else
               (let ([tmp (unique-name 'tmp)])
                 `(let ([,tmp ,((parse env) (car x*))])
                    (if ,tmp ,tmp ,((parse env) `(or ,@(cdr x*))))))])]
            [(not ,[x])
             `(if ,x '#f '#t)]
            [(begin ,[ef*] ...)
             (cond
              [(null? ef*)
               (error 'parse-scheme "body of begin cannot be empty")]
              [else `(begin ,ef* ...)])]
            [(lambda (,u* ...) ,e1 ,e2* ...)
             (let* ([w* (map unique-name (unique-check u*))]
                    [new-bd* (map (lambda (x y) `(,x . (,y #f))) u* w*)]
                    [body (if (null? e2*) e1 `(begin ,e1 ,e2* ...))]
                    [e^ ((parse (append new-bd* env)) body)])
               `(lambda (,w* ...) ,e^))]
            [(,let/rec ([,u* ,e*] ...) ,e1 ,e2* ...)
             (guard (memq let/rec '(letrec let)))
             (let* ([w* (map unique-name (unique-check u*))]
                    [new-bd* (map (lambda (x y z)
                                    (match z
                                      [(lambda (,x* ...) ,e1 ,e2 ...)
                                       `(,x . (,y ,(length x*)))]
                                      [,z `(,x . (,y #f))]))
                                  u* w* e*)]
                    [new-env* (append new-bd* env)]
                    [body (if (null? e2*) e1 `(begin ,e1 ,e2* ...))]
                    [e*^ (if (eq? let/rec 'let)
                             (map (parse env) e*)
                             (map (parse new-env*) e*))]
                    [body^ ((parse new-env*) body)])
               `(,let/rec ([,w* ,e*^] ...) ,body^))]
            [(set! ,x ,[v])
             (cond
              [(not (symbol? x))
               (error 'parse-scheme "can only assign to variables, but got ~a" x)]
              [(assq x env) => (lambda (p) `(set! ,(cadr p) ,v))]
              [else (error 'parse-scheme "unbound variable ~a" x)])]
            [(quote ,imm) `(quote ,imm)]
            [(,[f] ,[x*] ...)
             `(,f ,x* ...)]
            [,x (error 'parse-scheme "illegal program ~a" x)]))))
    ((parse env0) x)))




;; A14

;;;;;;;;;;;;;;;;;;;;;;;;; convert-complex-datum ;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This pass converts vector and pair constants and lift them out to the top
; of the program, making them global variables. The heart of the pass is
; convert-const, it converts a single quoted form into a binding which is
; then pushed onto the mutable list constants. It then outputs the
; temporary which represents the constant to its original context. Finally
; after all constants are converted, the bindings are wrapped around the
; whole program, making them global.

(define convert-complex-datum
  (lambda (x)
    (define constants '())
    (define convert-const
      (lambda (x)
        (match x
          [() (quote '())]
          [(,[a] . ,[d]) `(cons ,a ,d)]
          [#(,[x*] ...)
           (let* ([tmp (unique-name 'tmp)]
                  [len (length `(,x* ...))]
                  [sets (let loop ([ls `(,x* ...)] [n 0])
                          (cond
                           [(null? ls) '()]
                           [else (cons `(vector-set! ,tmp (quote ,n) ,(car ls))
                                       (loop (cdr ls) (add1 n)))]))])
             `(let ([,tmp (make-vector (quote ,len))])
                (begin ,@sets ,tmp)))]
          [,x `(quote ,x)])))
    (define convert
      (lambda (x)
        (match x
          [(,let/rec ([,u* ,[v*]] ...) ,[expr])
           (guard (memq let/rec '(letrec let)))
           `(,let/rec ([,u* ,v*] ...) ,expr)]
          [(lambda (,uvar* ...) ,[body])
           `(lambda (,uvar* ...) ,body)]
          [(begin ,[ef*] ...)
           `(begin ,ef* ...)]
          [(if ,[t] ,[c] ,[a])
           `(if ,t ,c ,a)]
          [(set! ,x ,[v])
           `(set! ,x ,v)]
          [(quote ,imm) (guard (or (number? imm) (boolean? imm) (null? imm)))
           `(quote ,imm)]
          [(quote ,imm)
           (let ([tmp (unique-name 'tmp)]
                 [const (convert-const imm)])
             (set! constants (cons `(,tmp ,const) constants))
             tmp)]
          [(,[f] ,[x*] ...)
           `(,f ,x* ...)]
          [,x x])))
    (let ([x* (convert x)])
      (if (null? constants) x* `(let ,constants ,x*)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;; uncover-assigned ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This pass collects assigned variables and list them inside the binding
; constructs that bind them. It works bottom-up and passes on a list of
; assigned variables. It only list assigned variables when it is also bound
; by the construct. Care must be taken for letrec and let bindings.

(define uncover-assigned
  (lambda (x)
    (define uncover
      (lambda (x)
        (match x
          [(letrec ([,uvar* ,[uncover -> expr* as*]] ...) ,[uncover -> expr as])
           (let* ([as-all (union (apply union as*) as)]
                  [u* (intersection uvar* as-all)])
             (values `(letrec ([,uvar* ,expr*] ...) (assigned ,u* ,expr))
                     (difference as-all uvar*)))]
          [(let ([,uvar* ,[uncover -> expr* as*]] ...) ,[uncover -> expr as])
           (let ([u* (intersection uvar* as)])
             (values `(let ([,uvar* ,expr*] ...) (assigned ,u* ,expr))
                     (union (apply union as*) (difference as uvar*))))]
          [(lambda (,uvar* ...) ,[uncover -> body as])
           (let ([u* (intersection uvar* as)])
             (values `(lambda (,uvar* ...) (assigned ,u* ,body)) as))]
          [(begin ,[uncover -> ef* as*] ...)
           (values `(begin ,ef* ...) (apply union as*))]
          [(if ,[uncover -> t at*] ,[uncover -> c ac*] ,[uncover -> a aa*])
           (values `(if ,t ,c ,a) (union at* ac* aa*))]
          [(set! ,x ,[uncover -> v av*])
           (values `(set! ,x ,v) (set-cons x av*))]
          [(,[uncover -> f af*] ,[uncover -> x* ax*] ...)
           (values `(,f ,x* ...) (union af* (apply union ax*)))]
          [,x (values x '())])))
    (let-values ([(x* as*) (uncover x)]) x*)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;; purify-letrec ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This pass uses a transformation in between the simpler transformation and
; the more sophisticated transformation. It classify only two kinds of
; letrec bindings: those bind lambdas and those bind other expressions. It
; doesn't separate "simple" and "complex" expressions in order to simplify
; the pass. Unnecessary assignments for simple expressions will be removed
; by my optimization pass forward-locations, but neither forward-locations
; nor optimize-known-call can optimize code produced by mixing lambdas with
; other expressions in letrec, so I decided to separate lambdas and other
; expressions.


; the naive version
(define purify-letrec-naive
  (lambda (x)
    (match x
      [(letrec ([,x* ,[e*]] ...) (assigned (,as* ...) ,[body]))
       (if (null? x*)
           body
           (let ([tmp* (map (lambda (x) (unique-name 'tmp)) x*)])
             `(let ([,x* (void)] ...)
                (assigned (,x* ...)
                  (begin
                    (let ([,tmp* ,e*] ...)
                      (assigned ()
                        (begin (set! ,x* ,tmp*) ...)))
                    ,body)))))]
      [(let ([,uvar* ,[expr*]] ...) (assigned (,as* ...) ,[expr]))
       `(let ([,uvar* ,expr*] ...) (assigned (,as* ...) ,expr))]
      [(lambda (,uvar* ...) (assigned (,as* ...) ,[body]))
       `(lambda (,uvar* ...) (assigned (,as* ...) ,body))]
      [(begin ,[ef*] ...)
       `(begin ,ef* ...)]
      [(if ,[t] ,[c] ,[a])
       `(if ,t ,c ,a)]
      [(set! ,x ,[v])
       `(set! ,x ,v)]
      [(,[f] ,[x*] ...)
       `(,f ,x* ...)]
      [,x x])))


; the sophisticated version
(define purify-letrec
  (lambda (x)
    (define orall
      (lambda (ls)
        (cond
         [(null? ls) #f]
         [(car ls) #t]
         [else (orall (cdr ls))])))
    (define not-simple?
      (lambda (x* e in-lam?)
        (match e
          [(letrec ([,uvar* ,[expr*]] ...) ,[expr])
           (and (null? (intersection x* uvar*)) (or (orall expr*) expr))]
          [(let ([,uvar* ,[expr*]] ...) ,[expr])
           (or (orall expr*) (and (null? (intersection x* uvar*)) expr))]
          [(lambda (,uvar* ...) ,body)
           (and (null? (intersection x* uvar*)) (not-simple? x* body #t))]
          [(assigned (,as* ...) ,[body]) body]
          [(begin ,[ef*] ...)
           (orall ef*)]
          [(if ,[t] ,[c] ,[a])
           (or t c a)]
          [(set! ,[x] ,[v])
           (or x v)]
          [(quote ,imm) #f]
          [(,f ,[x*] ...) (guard (prim? f))
           (orall x*)]
          [(,[fx*] ...) (or (not in-lam?) (orall fx*))]
          [,e (memq e x*)])))
    (define classify
      (lambda (df* as*)
        (let ([lhs* (map car df*)])
          (let loop ([df* df*] [simple* '()] [lambda* '()] [complex* '()])
            (cond
             [(null? df*) (values simple* lambda* complex*)]
             [else
              (let ([new-bd (cons (caar df*) (purify-letrec (cdar df*)))])
                (match new-bd
                  [(,lab (lambda (,u* ...) ,body)) (guard (memq lab as*))
                   (loop (cdr df*) simple* lambda* (cons new-bd complex*))]
                  [(,lab (lambda (,u* ...) ,body))
                   (loop (cdr df*) simple* (cons new-bd lambda*) complex*)]
                  [(,lab ,e)
                   (guard (not (not-simple? lhs* e #f)))
                   (loop (cdr df*) (cons new-bd simple*) lambda* complex*)]
                  [,new-bd
                   (loop (cdr df*) simple* lambda* (cons new-bd complex*))]))])))))
    (match x
      [(letrec ,df* (assigned (,as* ...) ,[body]))
       (letv* ([(simple* lambda* complex*) (classify df* as*)])
         (match complex*
           [([,x* ,e*] ...)
            (let* ([tmp* (map (lambda (x) (unique-name 'tmp)) x*)]
                   [body1 (if (null? complex*)
                              body
                              `(begin
                                 (let ([,tmp* ,e*] ...)
                                   (assigned () (begin (set! ,x* ,tmp*) ...)))
                                 ,body))]
                   [body2 (if (null? lambda*)
                              body1
                              `(letrec ,lambda* ,body1))]
                   [body3 (if (null? complex*)
                              body2
                              `(let ([,x* (void)] ...)
                                 (assigned (,x* ...) ,body2)))])
              (if (null? simple*)
                  body3
                  (let ([as^ (intersection as* (map car simple*))])
                    `(let ,simple* (assigned ,as^ ,body3)))))]))]
      [(let ([,uvar* ,[expr*]] ...) (assigned (,as* ...) ,[expr]))
       `(let ([,uvar* ,expr*] ...) (assigned (,as* ...) ,expr))]
      [(lambda (,uvar* ...) (assigned (,as* ...) ,[body]))
       `(lambda (,uvar* ...) (assigned (,as* ...) ,body))]
      [(begin ,[ef*] ...)
       `(begin ,ef* ...)]
      [(if ,[t] ,[c] ,[a])
       `(if ,t ,c ,a)]
      [(set! ,x ,[v])
       `(set! ,x ,v)]
      [(,[f] ,[x*] ...)
       `(,f ,x* ...)]
      [,x x])))



;;;;;;;;;;;;;;;;;;;;;;;;; convert-assignments ;;;;;;;;;;;;;;;;;;;;;;;;;

; To save space, this pass converts assigned variables into boxes, set!
; into set-box! and references to the assigned variables into unbox. It
; uses a helper make-bindings to produce two binding forms for the original
; bindings and the new bindings.

; pair version
(define convert-assignments-pair
  (lambda (x)
    (define make-bindings
      (lambda (as* bd*)
        (let loop ([bd* bd*] [bdo* '()] [env* '()])
          (cond
           [(null? bd*) (values (reverse bdo*) (reverse env*))]
           [(and (not (pair? (car bd*))) (memq (car bd*) as*))
            (let ([new (unique-name (car bd*))])
              (loop (cdr bd*)
                    (cons new bdo*)
                    (cons `(,(car bd*) (cons ,new (void))) env*)))]
           [(and (pair? (car bd*)) (memq (caar bd*) as*))
            (let ([new (unique-name (caar bd*))])
              (loop (cdr bd*)
                    (cons `[,new ,(cadar bd*)] bdo*)
                    (cons `[,(caar bd*) (cons ,new (void))] env*)))]
           [else
            (loop (cdr bd*) (cons (car bd*) bdo*) env*)]))))
    (define convert
      (lambda (x env)
        (match x
          [(letrec ([,uvar* ,[expr*]] ...) ,[body])
           `(letrec ([,uvar* ,expr*] ...) ,body)]
          [(let ([,uvar* ,[expr*]] ...) (assigned (,as* ...) ,expr))
           (let-values ([(bd* env*) (make-bindings as* `([,uvar* ,expr*] ...))])
             (let ([body (if (null? env*)
                             (convert expr (append as* env))
                             `(let ,env* ,(convert expr (append as* env))))])
               (if (null? bd*) body `(let ,bd* ,body))))]
          [(lambda (,uvar* ...) (assigned (,as* ...) ,body))
           (let-values ([(bd* env*) (make-bindings as* `(,uvar* ...))])
             `(lambda ,bd*
                ,(if (null? env*)
                     (convert body (append as* env))
                     `(let ,env* ,(convert body (append as* env))))))]
          [(begin ,[ef*] ...)
           `(begin ,ef* ...)]
          [(if ,[t] ,[c] ,[a])
           `(if ,t ,c ,a)]
          [(set! ,x ,[v])
           (if (memq x env) `(set-car! ,x ,v) `(set! ,x ,v))]
          [(,[f] ,[x*] ...)
           `(,f ,x* ...)]
          [,x (if (memq x env) `(car ,x) x)])))
    (convert x '())))


; box version
(define convert-assignments
  (lambda (x)
    (define make-bindings
      (lambda (as* bd*)
        (let loop ([bd* bd*] [bdo* '()] [env* '()])
          (cond
           [(null? bd*) (values (reverse bdo*) (reverse env*))]
           [(and (not (pair? (car bd*))) (memq (car bd*) as*))
            (let ([new (unique-name (car bd*))])
              (loop (cdr bd*)
                    (cons new bdo*)
                    (cons `(,(car bd*) (box ,new)) env*)))]
           [(and (pair? (car bd*)) (memq (caar bd*) as*))
            (let ([new (unique-name (caar bd*))])
              (loop (cdr bd*)
                    (cons `[,new ,(cadar bd*)] bdo*)
                    (cons `[,(caar bd*) (box ,new)] env*)))]
           [else
            (loop (cdr bd*) (cons (car bd*) bdo*) env*)]))))
    (define convert
      (lambda (x env)
        (match x
          [(letrec ([,uvar* ,[expr*]] ...) ,[body])
           `(letrec ([,uvar* ,expr*] ...) ,body)]
          [(let ([,uvar* ,[expr*]] ...) (assigned (,as* ...) ,expr))
           (let-values ([(bd* env*) (make-bindings as* `([,uvar* ,expr*] ...))])
             (let ([body (if (null? env*)
                             (convert expr (append as* env))
                             `(let ,env* ,(convert expr (append as* env))))])
               (if (null? bd*) body `(let ,bd* ,body))))]
          [(lambda (,uvar* ...) (assigned (,as* ...) ,body))
           (let-values ([(bd* env*) (make-bindings as* `(,uvar* ...))])
             `(lambda ,bd*
                ,(if (null? env*)
                     (convert body (append as* env))
                     `(let ,env* ,(convert body (append as* env))))))]
          [(begin ,[ef*] ...)
           `(begin ,ef* ...)]
          [(if ,[t] ,[c] ,[a])
           `(if ,t ,c ,a)]
          [(set! ,x ,[v])
           (if (memq x env) `(set-box! ,x ,v) `(set! ,x ,v))]
          [(,[f] ,[x*] ...)
           `(,f ,x* ...)]
          [,x (if (memq x env) `(unbox ,x) x)])))
    (convert x '())))



;; A13


;;;;;;;;;;;;;;;;;;;;; remove-anonymous-lambda ;;;;;;;;;;;;;;;;;;;;;;;;;;

;; transform lambdas which are not on the RHS of let and letrec into
;; letrec's.

(define remove-anonymous-lambda
  (lambda (x)
    (define rem-bd
      (lambda (bd*)
        (let loop ([bd* bd*] [bd^ '()])
          (cond
           [(null? bd*) (reverse bd^)]
           [else
            (match (car bd*)
              [(,lab (lambda (,fml* ...) ,body))
               (loop (cdr bd*) (cons `(,lab (lambda (,fml* ...) ,(rem body))) bd^))]
              [,x (loop (cdr bd*) (cons (rem x) bd^))])]))))
    (define rem
      (lambda (x)
        (match x
          [(let ,bd* ,[e])
           `(let ,(rem-bd bd*) ,e)]
          [(letrec ([,uvar* (lambda (,fml** ...) ,[x*])] ...) ,[e])
           `(letrec ([,uvar* (lambda (,fml** ...) ,x*)] ...) ,e)]
          [(lambda (,fml* ...) ,[body])
           (let ([lab (unique-name 'anon)])
             `(letrec ([,lab (lambda (,fml* ...) ,body)]) ,lab))]
          [(if ,[t] ,[c] ,[a])
           `(if ,t ,c ,a)]
          [(begin ,[ef*] ...)
           `(begin ,ef* ...)]
          [(quote ,imm)
           `(quote ,imm)]
          [(,[f] ,[x*] ...)
           `(,f ,x* ...)]
          [,x x])))
    (rem x)))




;;;;;;;;;;;;;;;;;;;;;; sanitize-binding-forms ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; separate bindings in lets. make the lambdas be bound by a letrec and
;; others by a let.

(define sanitize-binding-forms
  (lambda (x)
    (define sanitize
      (lambda (bd* body)
        (let loop ([bd* bd*] [letrec^ '()] [let^ '()])
          (cond
           [(null? bd*)
            (let ([lets (if (null? let^) body `(let ,let^ ,body))])
              (if (null? letrec^) lets `(letrec ,letrec^ ,lets)))]
           [else
            (match (car bd*)
              [(,lab (lambda (,x* ...) ,e))
               (loop (cdr bd*) (cons `(,lab (lambda (,x* ...) ,e)) letrec^) let^)]
              [,bd
               (loop (cdr bd*) letrec^ (cons bd let^))])]))))
    (match x
      [(quote ,imm)
       `(quote ,imm)]
      [(if ,[t] ,[c] ,[a])
       `(if ,t ,c ,a)]
      [(begin ,[ef*] ...)
       `(begin ,ef* ...)]
      [(let ([,x* ,[v*]] ...) ,[e])
       (sanitize `([,x* ,v*] ...) e)]
      [(letrec ([,uvar* (lambda (,fml** ...) ,[x*])] ...) ,[e])
       `(letrec ([,uvar* (lambda (,fml** ...) ,x*)] ...) ,e)]
      [(,[f] ,[x*] ...)
       `(,f ,x* ...)]
      [,x x])))





;; A12

;;;;;;;;;;;;;;;;;;;;; uncover-free-nopt ;;;;;;;;;;;;;;;;;;;;;
; This is the old uncover-free For the one that does closure optimization,
; see below.

; function: find free variables inside lambdas and list them in free forms.

(define uncover-free-nopt
  (lambda (x)
    (define uncover
      (lambda (x)
        (match x
          [(letrec ((,uvar* ,[uncover -> free* lam*]) ...) ,[uncover -> free2* expr])
           (values (difference (union (apply union free*) free2*) uvar*)
                   `(letrec ([,uvar* ,lam*] ...) ,expr))]
          [(lambda (,uvar* ...) ,expr)
           (let-values ([(free* expr^) (uncover expr)])
             (let ([free^ (difference free* uvar*)])
               (values free^ `(lambda (,uvar* ...) (free ,free^ ,expr^)))))]
          [(begin ,[uncover -> free* expr*] ...)
           (values (apply union free*) `(begin ,expr* ...))]
          [(if ,[uncover -> tf te]
               ,[uncover -> cf ce]
               ,[uncover -> af ae])
           (values (union tf cf af) `(if ,te ,ce ,ae))]
          [(let ([,uvar* ,[uncover -> free1* expr*]] ...) ,[uncover -> free2* expr])
           (values (union (apply union free1*) (difference free2* uvar*))
                   `(let ([,uvar* ,expr*] ...) ,expr))]
          [(quote ,imm)
           (values '() `(quote ,imm))]
          [(,prim ,[uncover -> free* a*] ...) (guard (prim? prim))
           (values (apply union free*) `(,prim ,a* ...))]
          [(,[uncover -> ff f] ,[uncover -> free* a*] ...)
           (values (apply union `(,ff ,free* ...)) `(,f ,a* ...))]
          [,x (values `(,x) x)])))
    (let-values ([(free* x*) (uncover x)]) x*)))




;;;;;;;;;;;;;;;;;;;;; convert-closures-nopt ;;;;;;;;;;;;;;;;;;;;;
; This is the old convert-closures. For the one that does closure
; optimization, see below.

; convert free forms into bind-free forms and introduce 'cp' arguments to
; procedures.

(define convert-closures-nopt
  (lambda (x)
    (define make-lab
      (lambda (x)
        (values x (unique-label x))))
    (define make-cp
      (lambda (x)
        (values (unique-name 'cp) x)))
    (define convert
      (lambda (x)
        (match x
          [(letrec ((,[make-lab -> uvar* label*]
                     (lambda (,x* ...)
                       (free ,[make-cp -> cp* free*] ,[expr*]))) ...) ,[expr])
           `(letrec ([,label* (lambda (,cp* ,x* ...)
                               (bind-free (,cp* ,free* ...) ,expr*))] ...)
              (closures ([,uvar* ,label* ,free* ...] ...) ,expr))]
          [(let ([,uvar* ,[expr*]] ...) ,[expr])
           `(let ([,uvar* ,expr*] ...) ,expr)]
          [(begin ,[e*] ...) `(begin ,e* ...)]
          [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
          [(quote ,imm) `(quote ,imm)]
          [(,prim ,[x*] ...) (guard (prim? prim))
           `(,prim ,x* ...)]
          [(,f ,[x*] ...) (guard (uvar? f))
           `(,f ,f ,x* ...)]
          [(,[f] ,[x*] ...)
           (let ([tmp (unique-name 't)])
             `(let ([,tmp ,f])
               (,tmp ,tmp ,x* ...)))]
          [,x x])))
    (convert (uncover-free-nopt x))))




;;;;;;;;;;;;;;;;;;;;; introduce-procedure-primitives ;;;;;;;;;;;;;;;;;;;;;
; modified slightly to deal with (bind-free (dummy) ...) forms
; function: convert bind-free and closures form into procedure primitives.

(define introduce-procedure-primitives
  (lambda (x)
    (define locate
      (lambda (x ls)
        (cond
         [(null? ls) #f]
         [(eq? x (car ls)) 0]
         [(locate x (cdr ls)) => add1]
         [else #f])))
    (define locate-fv
      (lambda (cpv)
        (lambda (x)
          (cond
           [(locate x (cdr cpv)) =>
            (lambda (i) `(procedure-ref ,(car cpv) ',i))]
           [else x]))))
    (define make-set!
      (lambda (x)
        (define make
          (lambda (x n)
            (match x
              [(,uvar ,label) '()]
              [(,uvar ,label ,x ,x* ...)
               (cons `(procedure-set! ,uvar ',n ,x)
                     (make `(,uvar ,label ,x* ...) (add1 n)))])))
        (make x 0)))
    (define intro
      (lambda (bd)
        (lambda (x)
          (match x
            [(letrec ((,label* ,[(intro '(dummy)) -> lam*]) ...) ,[expr])
             `(letrec ([,label* ,lam*] ...) ,expr)]
            [(lambda (,x* ...)
               (bind-free (dummy) ,[(intro bd) -> expr]))
             `(lambda (,x* ...) ,expr)]
            [(lambda (,cp ,x* ...)
               (bind-free (,cp ,fv* ...) ,[(intro `(,cp ,@fv*)) -> expr]))
             `(lambda (,cp ,x* ...) ,expr)]
            [(let ([,uvar* ,[expr*]] ...) ,[expr])
             `(let ([,uvar* ,expr*] ...) ,expr)]
            [(begin ,[e*] ...) `(begin ,e* ...)]
            [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
            [(quote ,imm) `(quote ,imm)]
            [(closures ([,uvar* ,label* ,[fv*] ...] ...) ,[expr])
             (let ([length* (map length fv*)])
               `(let ([,uvar* (make-procedure ,label* ',length*)] ...)
                  (begin
                    ,(map make-set! `([,uvar* ,label* ,fv* ...] ...)) ... ...
                    ,expr)))]
            [(,f ,[x*] ...) (guard (or (prim? f) (label? f)))
             `(,f ,x* ...)]
            [(,[f] ,[f],[x*] ...)
             `((procedure-code ,f) ,f ,x* ...)]
            [,x ((locate-fv bd) x)]))))
    ((intro '(dummy)) x)))





;;;;;;;;;;;;;;;;;;;;; normalize-context ;;;;;;;;;;;;;;;;;;;;;
;; box, unbox, set-box! added

(define normalize-context
  (lambda (x)
    (define make-nopless-begin
      (lambda (x*)
        (let ([x* (remove '(nop) x*)])
          (if (null? x*)
              '(nop)
              (make-begin x*)))))
    (define norm
      (lambda (ct)
        (lambda (x)
          (match x
            [(letrec ([,label (lambda (,uvar* ...) ,[(norm 'v) -> expr*])] ...)
               ,[(norm 'v) -> expr])
             `(letrec ([,label (lambda (,uvar* ...) ,expr*)] ...) ,expr)]
            [(begin ,[(norm 'e) -> e*] ... ,[(norm ct) -> t])
             `(begin ,e* ... ,t)]
            [(if ,[(norm 'p) -> t] ,[(norm ct) -> c] ,[(norm ct) -> a])
             `(if ,t ,c ,a)]
            [(let ([,uvar ,[(norm 'v) -> e*]] ...) ,[(norm ct) -> e])
             `(let ([,uvar ,e*] ...) ,e)]

            [(quote ,x)
             (case ct
               [e `(nop)]
               [p (if (eq? x #f) `(false) `(true))]
               [v `(quote ,x)])]
            [(,f! ,[(norm 'v) ->  x*] ...)
             (guard (memq f! '(set-car! set-cdr! set-box!
                                        vector-set! procedure-set!)))
             (case ct
               [e `(,f! ,x* ...)]
               [p `(begin (,f! ,x* ...) (true))]
               [v `(begin (,f! ,x* ...) (void))])]
            [(,f? ,x* ...)
             (guard (memq f? '(eq? pair? box? null? boolean?
                                   fixnum? vector? procedure?
                               < <= >= > =)))
             (case ct
               [e (make-nopless-begin `(,@(map (norm 'e) `(,x* ...)) (nop)))]
               [p `(,f? ,@(map (norm 'v) `(,x* ...)))]
               [v `(if (,f? ,@(map (norm 'v) `(,x* ...))) '#t '#f)])]
            [(,f ,x* ...)
             (guard (memq f '(+ - * logand logor sra cons car cdr void
                                make-vector vector-ref vector-length
                                make-procedure procedure-ref procedure-code
                                box unbox)))
             (case ct
               [e (make-nopless-begin `(,@(map (norm 'e) `(,x* ...)) (nop)))]
               [p `(if (eq? (,f ,@(map (norm 'v) `(,x* ...))) '#f) (false) (true))]
               [v `(,f ,@(map (norm 'v) `(,x* ...)))])]
            [,x (guard (uvar? x))
             (case ct
               [e `(nop)]
               [p `(if (eq? ,x '#f) (false) (true))]
               [v x])]
            [(,[(norm 'v) -> f] ,[(norm 'v) -> x*] ...)
             (case ct
               [e `(,f ,x* ...)]
               [p `(if (eq? (,f ,x* ...) '#f) (false) (true))]
               [v `(,f ,x* ...)])]
            [,x x]))))
    ((norm 'v) x)))



;; A10

;;;;;;;;;;;;;;;;;;;;; specify-representation ;;;;;;;;;;;;;;;;;;;;;

;; box, unbox and set-box! added

(define specify-representation
  (lambda (x)
    (define trivial?
      (lambda (x)
        (or (number? x) (memq x (list $false $true $nil $void)))))
    (match x
      ; basic grammar structures
      [(letrec ([,label (lambda (,uvar* ...) ,[body*])] ...) ,[body])
       `(letrec ([,label (lambda (,uvar* ...) ,body*)] ...) ,body)]
      [(if ,[test] ,[conseq] ,[alt])
       `(if ,test ,conseq ,alt)]
      [(begin ,[ef*] ...)
       `(begin ,ef* ...)]
      [(let ([,x* ,[v*]] ...) ,[body])
       `(let ([,x* ,v*] ...) ,body)]

      ; type and equivalence predicates
      [(eq? ,[x] ,[y]) `(= ,x ,y)]
      [(null? ,[e])
       (specify-representation `(eq? ,e '()))]
      [(pair? ,[e])
       `(= (logand ,e ,mask-pair) ,tag-pair)]
      [(box? ,[e])
       `(= (logand ,e ,mask-box) ,tag-box)]
      [(boolean? ,[e])
       `(= (logand ,e ,mask-boolean) ,tag-boolean)]
      [(fixnum? ,[e])
       `(= (logand ,e ,mask-fixnum) ,tag-fixnum)]
      [(vector? ,[e])
       `(= (logand ,e ,mask-vector) ,tag-vector)]
      [(procedure? ,[e])
       `(= (logand ,e ,mask-procedure) ,tag-procedure)]

      ; numbers
      [(,op ,[m] ,[n]) (guard (memq op '(+ - < <= >= > =)))
       `(,op ,m ,n)]
      [(* ,[m] ,[n])
       (cond
        [(number? m) `(* ,(sra m shift-fixnum) ,n)]
        [(number? n) `(* ,(sra n shift-fixnum) ,m)]
        [else `(* (sra ,m ,shift-fixnum) ,n)])]

      ; pairs
      [(cons ,[e1] ,[e2])
       (let* ([offset-car (- disp-car tag-pair)]
              [offset-cdr (- disp-cdr tag-pair)]
              [tmp (unique-name 't)]
              [tmp-car (if (trivial? e1) e1 (unique-name 't))]
              [tmp-cdr (if (trivial? e2) e2 (unique-name 't))]
              [bd-car (if (trivial? e1) `() `((,tmp-car ,e1)))]
              [bd-cdr (if (trivial? e2) `() `((,tmp-cdr ,e2)))]
              [body1 `(let ([,tmp (+ (alloc ,size-pair) ,tag-pair)])
                        (begin
                          (mset! ,tmp ,offset-car ,tmp-car)
                          (mset! ,tmp ,offset-cdr ,tmp-cdr)
                          ,tmp))])
         (if (or (not (null? bd-car)) (not (null? bd-cdr)))
             `(let (,@bd-car ,@bd-cdr) ,body1)
             body1))]
      [(set-car! ,[e1] ,[e2])
       (let ([offset-car (- disp-car tag-pair)])
         `(mset! ,e1 ,offset-car ,e2))]
      [(set-cdr! ,[e1] ,[e2])
       (let ([offset-cdr (- disp-cdr tag-pair)])
         `(mset! ,e1 ,offset-cdr ,e2))]
      [(car ,[e])
       (let ([offset-car (- disp-car tag-pair)])
         `(mref ,e ,offset-car))]
      [(cdr ,[e])
       (let ([offset-cdr (- disp-cdr tag-pair)])
         `(mref ,e ,offset-cdr))]

      ; boxes
      [(box ,[e])
       (let* ([offset-box (- tag-box)]
              [tmp (unique-name 't)]
              [tmp-e (if (trivial? e) e (unique-name 't))]
              [bd-e (if (trivial? e) `() `((,tmp-e ,e)))]
              [body1 `(let ([,tmp (+ (alloc ,size-box) ,tag-box)])
                        (begin
                          (mset! ,tmp ,offset-box ,tmp-e)
                          ,tmp))])
         (if (null? bd-e) body1 `(let (,@bd-e) ,body1)))]
      [(set-box! ,[e1] ,[e2])
       (let ([offset-box (- tag-box)])
         `(mset! ,e1 ,offset-box ,e2))]
      [(unbox ,[e])
       (let ([offset-box (- tag-box)])
         `(mref ,e ,offset-box))]

      ; vectors
      [(make-vector ,[k])
       (let ([offset-vector-length (- disp-vector-length tag-vector)]
             [tmp (unique-name 't)])
         (cond
          [(number? k)
           `(let ([,tmp (+ (alloc ,(+ disp-vector-data k)) ,tag-vector)])
              (begin
                (mset! ,tmp ,offset-vector-length ,k)
                ,tmp))]
          [else
           (let ([tmp1 (unique-name 't)]
                 [tmp2 (unique-name 't)])
             `(let ([,tmp1 ,k])
                (let ([,tmp2 (+ (alloc (+ ,disp-vector-data ,tmp1)) ,tag-vector)])
                  (begin
                    (mset! ,tmp2 ,offset-vector-length ,tmp1)
                    ,tmp2))))]))]
      [(vector-set! ,[e1] ,[e2] ,[e3])
       (let ([offset-vector-data (- disp-vector-data tag-vector)])
         (cond
          [(number? e2)
           `(mset! ,e1 ,(+ offset-vector-data e2) ,e3)]
          [else
           `(mset! ,e1 (+ ,offset-vector-data ,e2) ,e3)]))]
      [(vector-ref ,[e1] ,[e2])
       (let ([offset-vector-data (- disp-vector-data tag-vector)])
         (cond
          [(number? e2)
           `(mref ,e1 ,(+ offset-vector-data e2))]
          [else
           `(mref ,e1 (+ ,offset-vector-data ,e2))]))]
      [(vector-length ,[e1])
       (let ([offset-vector-length (- disp-vector-length tag-vector)])
         `(mref ,e1 ,offset-vector-length))]

      ; procedre
      [(make-procedure ,label ,[n])
       (let ([offset-procedure-code (- disp-procedure-code tag-procedure)]
             [tmp (unique-name 't)])
         `(let ([,tmp (+ (alloc ,(+ disp-procedure-data n)) ,tag-procedure)])
            (begin
              (mset! ,tmp ,offset-procedure-code ,label)
              ,tmp)))]
      [(procedure-set! ,[e1] ,[e2] ,[e3])
       (let ([offset-procedure-data (- disp-procedure-data tag-procedure)])
         `(mset! ,e1 ,(+ offset-procedure-data e2) ,e3))]
      [(procedure-code ,[e])
       (let ([offset-procedure-code (- disp-procedure-code tag-procedure)])
         `(mref ,e ,offset-procedure-code))]
      [(procedure-ref ,[e1] ,[e2])
       (let ([offset-procedure-data (- disp-procedure-data tag-procedure)])
         `(mref ,e1 ,(+ offset-procedure-data e2)))]

      ; immediates
      [(quote ,n) (guard (number? n))
       (ash n shift-fixnum)]
      [(quote #f) $false]
      [(quote #t) $true]
      [(quote ()) $nil]
      [(void) $void]

      ; procedure calls goes last because it could match other cases
      [(,[f] ,[x*] ...) `(,f ,x* ...)]
      [,x x])))



;; A11

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lift-letrec
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function: lift letrec to the top
; input: A11 grammar in which letrec can appear anywhere
; output: similar grammar but letrec only appears at top of program

(define lift-letrec
  (lambda (x)
    (define defs '())
    (define add-defs!
      (lambda (xs)
        (set! defs (append xs defs))))
    (define lift
      (lambda (x)
        (match x
          [(letrec ([,label (lambda (,uvar* ...) ,[expr*])] ...) ,[expr])
           (add-defs! `([,label (lambda (,uvar* ...) ,expr*)] ...))
           expr]
          [(begin ,[e*] ...) `(begin ,e* ...)]
          [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
          [(let ([,uvar ,[e*]] ...) ,[e]) `(let ([,uvar ,e*] ...) ,e)]
          [(quote ,[imm]) `(quote ,imm)]
          [(,[f] ,[x*] ...) `(,f ,x* ...)]
          [,x x])))
    (let ([x* (lift x)]) `(letrec ,defs ,x*))))




;; A9

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uncover-locals
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This pass just collect all the local variable names in a definition and
; put the list inside newly created locals forms.

(define uncover-locals
  (lambda (x)
    (define locals* '())
    (define add-local (lambda (x) (set! locals* (cons x locals*))))
    (define uncover1
      (lambda (x)
        (set! locals* '())
        (let ((x^ (uncover x)))
          (values locals* x^))))
    (define uncover
      (lambda (x)
        (match x
          [(letrec ((,label* (lambda (,uvar* ...)
                               ,[uncover1 -> new* body*])) ...)
             ,[uncover1 -> new body])
           `(letrec ((,label* (lambda (,uvar* ...)
                                (locals ,new* ,body*))) ...)
              (locals ,new ,body))]
          [(begin ,[s*] ...) `(begin ,s* ...)]
          [(let ((,x* ,[v*]) ...) ,[body])
           (for-each add-local x*)
           `(let ((,x* ,v*) ...) ,body)]
          [(if ,[test] ,[conseq] ,[alt])
           `(if ,test ,conseq ,alt)]
          [(alloc ,[n]) `(alloc ,n)]
          [(mset! ,[base] ,[off] ,[val]) `(mset! ,base ,off ,val)]
          [(mref ,[base] ,[off]) `(mref ,base ,off)]
          [(set! ,x ,[y]) `(set! ,x ,y)]
          [(,[f] ,[a*] ...) `(,f ,a* ...)]
          [,other other])))
    (uncover x)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; remove-let
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This pass converts let expressions into assignments.

(define remove-let
  (lambda (x)
    (define rem1
      (lambda (x)
        (make-begin (rem x))))
    (define rem
      (lambda (x)
        (match x
          [(letrec ((,label* (lambda (,uvar* ...)
                               (locals (,local* ...) ,[rem1 -> body*]))) ...)
             (locals (,local ...) ,[rem1 -> body]))
           `(letrec ((,label* (lambda (,uvar* ...)
                                (locals (,local* ...) ,body*))) ...)
              (locals (,local ...) ,body))]
          [(begin ,[s*] ...) `((begin ,s* ... ...))]
          [(let ((,x* ,[v*]) ...) ,[body])
           (let ([set* `((set! ,x* ,@v*) ...)])
             `(,(make-begin `(,@set* ,@body))))]
          [(if ,[test] ,[conseq] ,[alt])
           `((if ,@test ,@conseq ,@alt))]
          [(alloc ,[n]) `((alloc ,@n))]
          [(mset! ,[base] ,[off] ,[val]) `((mset! ,@base ,@off ,@val))]
          [(set! ,x ,[y]) `((set! ,x ,@y))]
          [(,[f] ,[a*] ...) `((,@f ,a* ... ...))]
          [,other `(,other)])))
    (rem x)))



; A8

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; verify-uil
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; verify-uil accept a single value and verifies that the value is a valid
;;; program in the UIL grammar. There are just a few trivial changed to add
;;; mref, alloc, and mset!

(define-who verify-uil
  (define verify-x-list
    (lambda (x* x? what)
      (let loop ([x* x*] [idx* '()])
        (unless (null? x*)
          (let ([x (car x*)] [x* (cdr x*)])
            (unless (x? x)
              (error who "invalid ~s ~s found" what x))
            (let ([idx (extract-suffix x)])
              (when (member idx idx*)
                (error who "non-unique ~s suffix ~s found" what idx))
              (loop x* (cons idx idx*))))))))
  (define Triv
    (lambda (label* uvar*)
      (lambda (t)
        (unless (or (label? t) (uvar? t) (and (integer? t) (exact? t)))
          (error who "invalid Triv ~s" t))
        (when (and (integer? t) (exact? t))
          (unless (int64? t)
            (error who "integer out of 64-bit range ~s" t)))
        (when (uvar? t)
          (unless (memq t uvar*)
            (error who "reference to unbound uvar ~s" t)))
        (when (label? t)
          (unless (memq t label*)
            (error who "unbound label ~s" t)))
        t)))
  (define Value
    (lambda (label* uvar*)
      (lambda (val)
        (match val
          [(alloc ,[(Value label* uvar*) -> n]) (void)]
          [(mref ,[(Value label* uvar*) -> base] ,[(Value label* uvar*) -> off]) (void)]
          [(if ,[(Pred label* uvar*) -> test] ,[conseq] ,[altern]) (void)]
          [(begin ,[(Effect label* uvar*) -> ef*] ... ,[val]) (void)]
          [(sra ,[x] ,y)
           (unless (uint6? y)
             (error who "invalid sra operand ~s" y))]
          [(,binop ,[x] ,[y])
           (guard (memq binop '(+ - * logand logor sra)))
           (void)]
          [(,[rator] ,[rand*] ...) (void)]
          [,[(Triv label* uvar*) -> tr] (void)]))))
  (define Effect
    (lambda (label* uvar*)
      (lambda (ef)
        (match ef
          [(nop) (void)]
          [(if ,[(Pred label* uvar*) -> test] ,[conseq] ,[altern]) (void)]
          [(begin ,[ef*] ... ,[ef]) (void)]
          [(set! ,var ,[(Value label* uvar*) -> val])
           (unless (memq var uvar*)
             (error who "assignment to unbound var ~s" var))]
          [(mset! ,[(Value label* uvar*) -> base]
                  ,[(Value label* uvar*) -> off]
                  ,[(Value label* uvar*) -> val])
           (void)]
          [(,[(Value label* uvar*) -> rator]
             ,[(Value label* uvar*) -> rand*] ...)
           (void)]
          [,ef (error who "invalid Effect ~s" ef)]))))
  (define Pred
    (lambda (label* uvar*)
      (lambda (pr)
        (match pr
          [(true) (void)]
          [(false) (void)]
          [(if ,[test] ,[conseq] ,[altern]) (void)]
          [(begin ,[(Effect label* uvar*) -> ef*] ... ,[pr]) (void)]
          [(,predop ,[(Value label* uvar*) -> x] ,[(Value label* uvar*) -> y])
           (unless (memq predop '(< > <= >= =))
             (error who "invalid predicate operator ~s" predop))]
          [,pr (error who "invalid Pred ~s" pr)]))))
  (define Tail
    (lambda (tail label* uvar*)
      (match tail
        [(alloc ,[(Value label* uvar*) -> n]) (void)]
        [(mref ,[(Value label* uvar*) -> base] ,[(Value label* uvar*) -> off]) (void)]
        [(if ,[(Pred label* uvar*) -> test] ,[conseq] ,[altern]) (void)]
        [(begin ,[(Effect label* uvar*) -> ef*] ... ,[tail]) (void)]
        [(sra ,[(Value label* uvar*) -> x] ,y)
         (unless (uint6? y)
           (error who "invalid sra operand ~s" y))]
        [(,binop ,[(Value label* uvar*) -> x] ,[(Value label* uvar*) -> y])
         (guard (memq binop '(+ - * logand logor sra)))
         (void)]
        [(,[(Value label* uvar*) -> rator]
           ,[(Value label* uvar*) -> rand*] ...)
         (void)]
        [,[(Triv label* uvar*) -> triv] (void)])))
  (define Body
    (lambda (label*)
      (lambda (bd fml*)
        (match bd
          [(locals (,local* ...) ,tail)
           (let ([uvar* `(,fml* ... ,local* ...)])
             (verify-x-list uvar* uvar? 'uvar)
             (Tail tail label* uvar*))]
          [,bd (error who "invalid Body ~s" bd)]))))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)
       (verify-x-list label* label? 'label)
       (map (lambda (fml*) (verify-x-list fml* uvar? 'formal)) fml**)
       (for-each (Body label*) bd* fml**)
       ((Body label*) bd '())]
      [,x (error who "invalid Program ~s" x)])
    x))





;; A6

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; remove-complex-opera*
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; "alloc" is removed completely from non-tail positions and turned into
; assignments, but left intact on tail positions. "mref" and "mset!" are
; treated much like a call, but have a new type of context 'mref, mref only
; gets out of 'mref contexts and remain inside others so that we can have
; (set! x.1 (+ (mref a.1 8) 1)). mset! is treated exactly like calls.

(define remove-complex-opera*
  (lambda (exp)
    (define temp* #f)
    (define new-t
      (lambda ()
        (let ([t (unique-name 't)])
          (set-box! temp* (cons t (unbox temp*)))
          t)))
    (define rem1
      (lambda (exp)
        (set! temp* (box '()))
        (let ([exp* (make-begin (rem `(,exp) 'id id))])
          (values (unbox temp*) exp*))))
    (define rem
      (lambda (exp ct C)
        (match exp
          [(letrec ([,label* (lambda (,fml** ...)
                               (locals (,local1* ...)
                                 ,[rem1 -> new* tail*]))] ...)
             (locals (,local2* ...) ,[rem1 -> new tail]))
           `(letrec ([,label* (lambda (,fml** ...)
                                (locals (,local1* ... ,new* ...) ,tail*))] ...)
              (locals (,local2* ... ,new ...) ,tail))]
          [((begin ,e* ... ,t))
           (let ([vt* (rem `(,t) ct
                           (lambda (vt*)
                             (case ct
                               [(fun arg mref)
                                (let ([t@ (new-t)])
                                  `((set! ,t@ ,@vt*) ,@(C `(,t@))))]
                               [else (C vt*)])))])
             (rem `(,e* ...) 'seq
                  (lambda (ve*) `(,@ve* ,@vt*))))]
          [(,a ,a* ...) (guard (eq? ct 'arg*))
           (rem `(,a) 'arg
                (lambda (v1*)
                  (rem `(,a* ...) 'arg*
                       (lambda (v2*) (C `(,@v1* ,@v2*))))))]
          [(,h ,t ,t* ...)
           (let ([vt* (rem `(,t ,t* ...) ct C)])
             (rem `(,h) 'seq
                  (lambda (vh*) `(,@vh* ,@vt*))))]
          [((if ,test ,conseq ,alt))
           (case ct
             [(fun arg mref)
              (let* ([t@ (new-t)]
                     [ctx (lambda (v*) `((set! ,t@ ,@v*)))]
                     [ec (make-begin (rem `(,conseq) 'rhs ctx))]
                     [ea (make-begin (rem `(,alt) 'rhs ctx))])
                (rem `(,test) 'test
                     (lambda (vt*) `((if ,@vt* ,ec ,ea) ,@(C `(,t@))))))]
             [rhs
              (let ([ec (make-begin (rem `(,conseq) ct C))]
                    [ea (make-begin (rem `(,alt) ct C))])
                (rem `(,test) 'test
                     (lambda (vt*) `((if ,@vt* ,ec ,ea)))))]
             [else
              (let ([ec (make-begin (rem `(,conseq) 'id id))]
                    [ea (make-begin (rem `(,alt) 'id id))])
                (rem `(,test) 'test
                     (lambda (vt*) (C `((if ,@vt* ,ec ,ea))))))])]
          [((set! ,x ,y))
           (C (rem `(,x) 'lhs
                   (lambda (vx*)
                     (rem `(,y) 'rhs
                          (lambda (vy*) `((set! ,@vx* ,@vy*)))))))]
          [((,a)) (guard (memq a '(nop true false))) (C `((,a)))]
          [((alloc ,n))
           (rem `(,n) 'arg
                (lambda (vn*)
                  (let ([addr (new-t)])
                    `((set! ,addr ,allocation-pointer-register)
                      (set! ,allocation-pointer-register
                            (+ ,allocation-pointer-register ,@vn*))
                      ,@(C `(,addr))))))]

          [((mset! ,base ,off ,val))
           (C (rem `(,base) 'mref
                   (lambda (vb*)
                     (rem `(,off) 'mref
                          (lambda (vo*)
                            (rem `(,val) 'rhs
                                 (lambda (vv*)
                                   `((mset! ,@vb* ,@vo* ,@vv*)))))))))]
          [((mref ,base ,off))
           (rem `(,base) 'mref
                (lambda (vb*)
                  (rem `(,off) 'mref
                       (lambda (vo*)
                         (case ct
                           [(fun mref)
                            (let ([t@ (new-t)])
                              `((set! ,t@ (mref ,@vb* ,@vo*)) ,@(C `(,t@))))]
                           [else (C `((mref ,@vb* ,@vo*)))])))))]
          [((,f ,a* ...))
           (rem `(,f) 'fun
                (lambda (vf*)
                  (rem `(,a* ...) 'arg*
                       (lambda (va*)
                         (case ct
                           [(fun arg mref)
                            (let ([t@ (new-t)])
                              `((set! ,t@ (,@vf* ,@va*)) ,@(C `(,t@))))]
                           [else (C `((,@vf* ,@va*)))])))))]
          [,exp (C exp)])))
    (rem exp 'id id)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass: impose-calling-conventions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; - alloc's at tail positions are handled.
; - mset! goes through unchanged.
; - mref is added to the return handling part (by excluding it from the cases of calls)
; - allocation-pointer-register is listed in call-live list.

(define-who impose-calling-conventions
  (define nfv
    (lambda (n)
      (unique-name 'nfv)))
  (define load-params
    (lambda (fml* regs fv-fun fv-n seq)
      (cond
       [(null? fml*) (reverse seq)]
       [(null? regs)
        (load-params (cdr fml*) '() fv-fun (add1 fv-n)
                     (cons `(set! ,(car fml*) ,(fv-fun fv-n)) seq))]
       [else
        (load-params (cdr fml*) (cdr regs) fv-fun fv-n
                     (cons `(set! ,(car fml*) ,(car regs)) seq))])))
  (define rev-load
    (lambda (loads regs fvs)
      (cond
       [(null? loads) (reverse (append regs fvs))]
       [else
        (match (car loads)
          [(set! ,dst ,src) (guard (register? src))
           (rev-load (cdr loads) (cons `(set! ,src ,dst) regs) fvs)]
          [(set! ,dst ,src)
           (rev-load (cdr loads) regs (cons `(set! ,src ,dst) fvs))])])))
  (define get-nfv
    (lambda (loads)
;      (filter (lambda (x) (not register?)) (map caddr loads))
      (cond
       [(null? loads) '()]
       [else
        (match (car loads)
          [(set! ,dst ,src) (guard (register? src))
           (get-nfv (cdr loads))]
          [(set! ,dst ,src)
           (cons src (get-nfv (cdr loads)))])])))
  (define impose
    (lambda (rp ct new-fv*)
      (lambda (x)
        (match x
          [(if ,[test] ,[conseq] ,[alt])
           `(if ,test ,conseq ,alt)]
          [(begin ,[(impose rp 'seq new-fv*) -> e*] ... ,[tail])
           `(begin ,e* ... ,tail)]
          [(,m/set! ,x ... (,op ,y ,z)) (guard (memq m/set! '(set! mset!))
                                               (or (binop? op) (eq? op 'mref)))
           `(,m/set! ,x ... (,op ,y ,z))]
          [(,m/set! ,var ... (,f ,x* ...)) (guard (memq m/set! '(set! mset!)))
           (make-begin `(,((impose rp 'rhs new-fv*) `(,f ,x* ...))
                         (,m/set! ,var ... ,return-value-register)))]
          [(,m/set! ,var ... ,val) (guard (memq m/set! '(set! mset!)))
           `(,m/set! ,var ... ,val)]
          [(,x) (guard (member x '(nop true false))) `(,x)]
          [(,relop ,a ,b) (guard (relop? relop))
           `(,relop ,a ,b)]
          [(,triv ,loc* ...) (guard (not (binop? triv))
                                    (not (eq? triv 'mref))
                                    (eq? ct 'tail))
           (let* ([l* (load-params loc* parameter-registers index->frame-var 0 '())]
                  [rl* (rev-load l* '() '())])
             `(begin
                ,@rl*
                (set! ,return-address-register ,rp) ; tail-call optimization
                (,triv ,frame-pointer-register
                       ,return-address-register
                       ,allocation-pointer-register
                       ,@(map cadr rl*))))]
          [(,triv ,loc* ...) (guard (not (binop? triv))
                                    (not (eq? triv 'mref))
                                    (not (eq? ct 'tail)))
           (let* ([l* (load-params loc* parameter-registers nfv 0 '())]
                  [rl* (rev-load l* '() '())]
                  [label (unique-label 'ret)])
             (set-box! new-fv* (cons (get-nfv l*) (unbox new-fv*)))
             `(return-point ,label      ;;; difference
               (begin
                 ,@rl*
                 (set! ,return-address-register ,label) ;;; difference
                 (,triv ,frame-pointer-register
                        ,return-address-register
                        ,allocation-pointer-register
                        ,@(map cadr rl*)))))]
          [,x `(begin (set! ,return-value-register ,x)
                      (,rp ,frame-pointer-register
                           ,return-value-register
                           ,allocation-pointer-register))]))))
  (define Body
    (lambda (bd fml*)
      (match bd
        [(locals (,locals* ...) ,tail)
         (let* ([loads (load-params fml* parameter-registers index->frame-var 0 '())]
                [rp (unique-name 'rp)]
                [new-fv* (box '())]
                [tail ((impose rp 'tail new-fv*) tail)])
           `(locals (,locals* ... ,@fml* ,rp ,@(apply append (unbox new-fv*)))
              (new-frames ,(unbox new-fv*)
               ,(make-begin
                 `((set! ,rp ,return-address-register)
                   ,@loads
                   ,tail)))))])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)
       (let ([bd* (map Body bd* fml**)]
             [bd (Body bd '())])
         `(letrec ([,label* (lambda () ,bd*)] ...) ,bd))])))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Two Passes: uncover-frame-conflict and uncover-register-conflict
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uncover-conflict-helper
  (lambda (x ct rec? with?)
    (define spill* '())
    (define call-live* '())
    (define add-conflicts
      (lambda (x ls ct)
        (letrec ([add-conf1
                  (lambda (x ls ct)
                    (if (rec? x)
                        (let ([slot (assq x ct)])
                          (if slot
                              (set-cdr! slot (union (cdr slot)
                                                    (filter with? ls)))))))])
          (add-conf1 x ls ct)
          (if (with? x)
              (for-each (lambda (y) (add-conf1 y (list x) ct)) ls)))))
    (define uncover
      (lambda (seq live* f-live*)
        (match seq
          [((begin ,s ...)) (uncover `(,s ...) live* f-live*)]
          [((if ,test ,conseq ,alt))
           (let ([lc* (uncover `(,conseq) live* f-live*)]
                 [la* (uncover `(,alt) live* f-live*)])
             (uncover `(,test) lc* la*))]
          [((set! ,x (,binop/mref ,y ,z)))
           (add-conflicts x (difference live* `(,x)) ct)
           (union (difference live* `(,x))
                  (uncover `(,y) live* f-live*)
                  (uncover `(,z) live* f-live*))]
          [((set! ,x ,y))
           (let ([ly* (uncover `(,y) live* f-live*)])
             (add-conflicts x (difference (difference live* ly*) `(,x)) ct)
             (union (difference live* `(,x)) ly*))]
          [((mset! ,base ,off ,val))
           (union live*
                  (uncover `(,base) live* f-live*)
                  (uncover `(,off) live* f-live*)
                  (uncover `(,val) live* f-live*))]
          [((return-point ,label ,tail))
           (set! spill* (union spill* (filter uvar? live*)))
           (set! call-live*
                 (union call-live*
                        (filter (lambda (x)
                                  (or (uvar? x) (frame-var? x)))
                                live*)))
           (uncover `(,tail) live* f-live*)]
          [(,h ,t ,t* ...)
           (let ([lt* (uncover `(,t ,t* ...) live* f-live*)])
             (uncover `(,h) lt* f-live*))]
          [((mref ,base ,off))
           (union live*
                  (uncover `(,base) live* f-live*)
                  (uncover `(,off) live* f-live*))]
          [((true)) live*]
          [((false)) f-live*]
          [((,relop ,x ,y)) (guard (relop? relop))
           (union live* f-live*
                  (uncover `(,x) live* f-live*)
                  (uncover `(,y) live* f-live*))]
          [((,target ,c-live* ...))
           (union live* (uncover `(,target) live* f-live*) c-live*)]
          [(,x) (guard (with? x)) `(,x)]
          [,other '()])))
    (let ([x (uncover x '() '())])
      (values x spill* call-live*))))



;;;;;;;; uncover-frame-conflict and uncover-register-conflict ;;;;;;;;;

; forward-locations is used to process the "tail" before we do
; uncover-conflicts if *enable-forward-locations* is set to #t.

(define uncover-frame-conflict
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[body*])] ...) ,[body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [(locals (,uvar* ...)
         (new-frames (,frame** ...) ,tail))
       (let ([ct (map (lambda (x) (cons x '())) uvar*)]
             [tail^ (if *enable-forward-locations*
                        (forward-locations tail '())
                        tail)])
         (letv* ([(live* spill* call-live*)
                  (uncover-conflict-helper
                   tail^
                   ct uvar? (lambda (x) (or (uvar? x) (frame-var? x))))])
           `(locals (,@(difference uvar* spill*))
              (new-frames (,frame** ...)
                 (spills ,spill*
                     (frame-conflict ,ct
                         (call-live ,call-live* 
                             ,tail^)))))))])))



(define uncover-register-conflict
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[body*])] ...) ,[body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [(locals (,local* ...)
         (ulocals (,ulocal* ...)
                  (locate (,home* ...)
                    (frame-conflict ,fv-ct ,tail))))
       (let ([ct (map (lambda (x) (cons x '())) (union local* ulocal*))]
             [tail^ (if *enable-forward-locations*
                        (forward-locations tail ulocal*)
                        tail)])
         (let-values ([(live* spill* call-live*)
                       (uncover-conflict-helper
                        tail^
                        ct uvar? (lambda (x) (or (uvar? x) (register? x))))])
           `(locals (,local* ...)
              (ulocals (,ulocal* ...)
                       (locate (,home* ...)
                         (frame-conflict ,fv-ct
                                         (register-conflict ,ct ,tail^)))))))]
      [(locate (,home* ...) ,tail) `(locate (,home* ...) ,tail)])))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass: pre-assign-frame
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-who pre-assign-frame
  (define homes-of
    (lambda (vars* home*)
      (let ([m1 (map (lambda (x)
                       (if (frame-var? x) (cons x x) (assq x home*)))
                     vars*)])
        (map cdr (filter (lambda (x) x) m1)))))
  (define find-avail
    (lambda (used)
      (let loop ([idx 0])
        (let ((fv* (index->frame-var idx)))
          (cond
           [(memq fv* used) (loop (add1 idx))]
           [else fv*])))))
  (define find-homes
    (lambda (spill* ct home*)
      (let loop ([spill* spill*] [home* home*])
        (cond
         [(null? spill*) (reverse (alist->list home*))]
         [else
          (let ([avail (find-avail
                        (homes-of (get-conflicts (car spill*) ct) home*))])
            (loop (cdr spill*)
                  (cons (cons (car spill*) avail) home*)))]))))
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (new-frames (,nfv** ...)
             (spills (,spill* ...)
               (frame-conflict ,ct
                 (call-live (,call-live* ...) ,tail)))))
         (let ([home* (find-homes spill* ct '())])
           `(locals (,local* ...)
              (new-frames (,nfv** ...)
                          (locate (,home* ...)
                            (frame-conflict ,ct
                              (call-live (,call-live* ...) ,tail))))))]
        [,body (error who "invalid Body ~s" body)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass: assign-new-frame
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-who assign-new-frame
  (define frame-size
    (lambda (call-live* home*)
      (let ((home* (list->alist home*)))
        (let loop ([rest call-live*] [max -1])
          (cond
           [(null? rest) (add1 max)]
           [else
            (let ([idx (frame-var->index (cdr (assq (car rest) home*)))])
              (cond
               [(> idx max) (loop (cdr rest) idx)]
               [else (loop (cdr rest) max)]))])))))
  (define do-assign
    (lambda (fs)
      (lambda (nfv*)
        (let loop ([rest nfv*] [idx fs] [assigned '()])
          (cond
           [(null? rest) assigned]
           [else (loop (cdr rest) (add1 idx)
                       (cons `(,(car rest) ,(index->frame-var idx)) assigned))])))))
  (define assign
    (lambda (fs)
      (lambda (x)
        (match x
          [(if ,[test] ,[conseq] ,[alt])
           `(if ,test ,conseq ,alt)]
          [(begin ,[e*] ... ,[tail])
           `(begin ,e* ... ,tail)]
          [(return-point ,label ,tail)
           (let ([bn (fxsll fs align-shift)])
             `(begin (set! ,frame-pointer-register (+ ,frame-pointer-register ,bn))
                     (return-point ,label ,tail)
                     (set! ,frame-pointer-register (- ,frame-pointer-register ,bn))))]
          [,x x]))))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[body*])] ...) ,[body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [(locals (,local* ...)
         (new-frames (,nfv** ...)
            (locate (,home* ...)
              (frame-conflict ,ct
                (call-live (,call-live* ...) ,tail)))))
         (let ([fs (frame-size call-live* home*)])
           `(locals (,(difference local* `(,nfv** ... ...)) ...)
              (ulocals ()
                (locate (,home* ... ,(map (do-assign fs) nfv**) ... ...)
                  (frame-conflict ,ct ,((assign fs) tail))))))]
      [,x (error who "invalid Program ~s" x)])))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass: assign-frame
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-who assign-frame
  (define homes-of
    (lambda (vars* home*)
      (let ([m1 (map (lambda (x)
                       (if (frame-var? x) (cons x x) (assq x home*)))
                     vars*)])
        (map cdr (filter (lambda (x) x) m1)))))

  (define find-avail
    (lambda (used)
      (let loop ([idx 0])
        (let ((fv* (index->frame-var idx)))
          (cond
           [(memq fv* used) (loop (add1 idx))]
           [else fv*])))))

  (define find-homes
    (lambda (spill* ct home*)
      (let loop ([spill* spill*] [home* home*])
        (cond
         [(null? spill*) (reverse (alist->list home*))]
         [else
          (let ([avail (find-avail
                        (homes-of (get-conflicts (car spill*) ct) home*))])
            (loop (cdr spill*)
                  (cons (cons (car spill*) avail) home*)))]))))
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
                    (spills (,spill* ...)
                            (locate (,home* ...)
                              (frame-conflict ,ct ,tail)))))
         (let ([home* (find-homes spill* ct (reverse (list->alist home*)))])
           `(locals (,local* ...)
              (ulocals (,ulocal* ...)
                       (locate ,home*
                         (frame-conflict ,ct ,tail)))))]
        [(locate (,home* ...) ,body) `(locate (,home* ...) ,body)]
        [,body (error who "invalid Body ~s" body)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass: assign-registers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define assign-registers
  (lambda (x)
    (define homes-of
      (lambda (vars* homes*)
        (let ([m1 (map (lambda (x)
                         (if (register? x) (cons x x) (assq x homes*)))
                       vars*)])
          (map cdr (filter (lambda (x) x) m1)))))
    (define find-homes
      (lambda (ct regs)
        (let loop ([ct ct] [homes* '()])
          (cond
           [(null? ct) (reverse (alist->list homes*))]
           [else
            (let ([avails (difference regs
                            (homes-of (get-conflicts (caar ct) ct) homes*))])
              (cond
               [(null? avails) (loop (cdr ct) homes*)]
               [else (loop (cdr ct)
                           (cons (cons (caar ct) (car avails)) homes*))]))]))))
    (define sort-conflict-graph
      (lambda (ct ulocal*)
        (let ([ut (map (lambda (x) (assq x ct)) ulocal*)])
          (append ut (let loop ([ct (difference ct ut)] [out '()])
                       (cond
                        [(null? ct) out]
                        [else
                         (let ([x1 (find-min length ct)])
                           (loop (ct-remove-node (car x1) ct)
                                 (cons x1 out)))]))))))
    (match x
      [(letrec ([,label* (lambda () ,[body*])] ...) ,[body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [(locals (,local* ...)
         (ulocals (,ulocal* ...)
                  (locate (,frame-home* ...)
                    (frame-conflict ,fv-ct
                                    (register-conflict ,ct ,tail)))))
       (let ([uvar* (append local* ulocal*)])
         (let ([home* (find-homes (sort-conflict-graph ct ulocal*) registers)])
           (let ([spill* (difference uvar* (map car home*))])
             (cond
              [(null? spill*) `(locate (,frame-home* ... ,home* ...) ,tail)]
              [(null? (intersection ulocal* spill*))
               (let ([local* (difference local* spill*)])
                 `(locals (,local* ...)
                    (ulocals (,ulocal* ...)
                             (spills (,spill* ...)
                                     (locate (,frame-home* ...)
                                       (frame-conflict ,fv-ct ,tail))))))]
              [else
               (error 'assign-registers
                      "unspillable variables (~s) have been spilled"
                      (intersection ulocal* spill*))]))))]
      [(locate (,home* ...) ,tail) `(locate (,home* ...) ,tail)])))



(define-who everybody-home?
  (define all-home?
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (spills (,spill* ...)
               (locate (,home* ...)
                 (frame-conflict ,ct ,tail))))) #f]
        [(locate (,home* ...) ,tail) #t]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
       [(letrec ([,label* (lambda () ,body*)] ...) ,body)
        (andmap all-home? `(,body ,body* ...))]
       [,x (error who "invalid Program ~s" x)])))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass: select-instructions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This pass is changed to context-passing style in order to handle (mref
; ...) that are embedded in operator/function calls nicely. It is now a
; little weird because the argument "ct" can be either a LHS who is
; expecting the RHS (e.g. x.1) or a context type (e.g. 'mref). Most of the
; time it is #f which means "don't care".

; The output of select could be feed back into itself (via reselect) again
; because of the iterative way it handles constraints. For example (set!
; x.1 (* fv0 4000000000000)). First we load 4000000000000 into a uvar, but
; then we must recheck (set! x.1 (* fv0 u.1)) to satisfy other constraints.

; This pass is more compositional than before. For example, the case (set!
; x (binop y z)) no longer exists. It is decomposed into two subparts:
; (set! x w) and (binop y z) and they are no longer tied to each other. The
; benefit is that now (set! x w) can be combined with (mref base off) to
; handle cases like (set! x (mref y z)). More complex ways of composition
; are possible, like (set! x (+ fv0 (mref s t))).

(define select-instructions
  (lambda (exp)
    (define int64/label?
      (lambda (x)
        (or (and (int64? x) (not (int32? x)))
            (label? x))))
    (define ur?
      (lambda (x)
        (or (register? x) (uvar? x))))
    (define mem?
      (lambda (x)
        (or (frame-var? x) (mref? x))))
    (define commutative?
      (lambda (op)
        (or (memq op '(+ * logor logand))
            (relop? op))))
    (define flip-op
      (lambda (op)
        (cond
         [(relop? op)
          (cdr (assq op '((= . =) (<= . >=) (>= . <=) (< . >) (> . <))))]
         [(binop? op) op])))
    (define temp* #f)
    (define new-u
      (lambda ()
        (let ([u (unique-name 'u)])
          (set-box! temp* (cons u (unbox temp*)))
          u)))
    (define select1
      (lambda (exp)
        (set! temp* (box '()))
        (let ([exp* (make-begin (select `(,exp) #f id))])
          (values (unbox temp*) exp*))))
    (define reselect
      (lambda (exp)
        (select exp #f id)))
    (define select
      (lambda (exp ct C)
        (match exp
          [(letrec ([,label* (lambda () ,[body*])] ...) ,[body])
           `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
          [(locals (,local* ...)
             (ulocals (,ulocal* ...)
                (locate (,home* ...)
                   (frame-conflict ,ct ,[select1 -> new* tail]))))
           `(locals (,local* ...)
              (ulocals (,ulocal* ... ,new* ...)
                (locate (,home* ...)
                   (frame-conflict ,ct ,tail))))]
          [(locate (,home* ...) ,tail) `(locate (,home* ...) ,tail)]
          [((begin ,e* ...))
           (select `(,e* ...) #f C)]
          [(,h ,t ,t* ...)
           (select `(,h) #f
             (lambda (vh*) `(,@vh* ,@(select `(,t ,t* ...) #f C))))]
          [((if ,test ,conseq ,alt))
           (let ([ec (make-begin (select `(,conseq) #f id))]
                 [ea (make-begin (select `(,alt) #f id))])
             (select `(,test) #f
               (lambda (vt*) (C `((if ,@vt* ,ec ,ea))))))]
          [((return-point ,label ,tail))
           (C `((return-point ,label
                   ,(make-begin (reselect `(,tail))))))]
          [((set! ,x ,y))
           (C (select `(,x) #f
                (lambda (vx*)
                  (select `(,y) x
                    (lambda (vy*)
                      (let ([x (car vx*)] [y (car vy*)])
                        (cond
                         [(and (mem? x)
                               (or (mem? y) (int64/label? y)))
                          (let ((u (new-u)))
                            `((set! ,u ,y) (set! ,x ,u)))]
                         [else `((set! ,x ,y))])))))))]
          [((mref ,base ,off))
           (select `(,base) 'mref
             (lambda (vb*)
               (select `(,off) 'mref
                 (lambda (vo*)
                   (cond
                    [(and (number? (car vb*))
                          (number? (car vo*)))
                     (let ((u (new-u)))
                       `((set! ,u ,@vb*)
                         ,@(C `((mref ,u ,@vo*)))))]
                    [else (C `((mref ,@vb* ,@vo*)))])))))]
          [((mset! ,base ,off ,val))
           (select `(,base) 'mref
             (lambda (vb*)
               (select `(,off) 'mref
                 (lambda (vo*)
                   (select `(,val) `(mref ,@vb* ,@vo*)
                     (lambda (vv*)
                       (cond
                        [(mem? (car vv*))
                         (let ([u (new-u)])
                           `((set! ,u ,@vv*)
                             ,@(C `((mset! ,@vb* ,@vo* ,u)))))]
                        [else (C `((mset! ,@vb* ,@vo* ,@vv*)))])))))))]
          [((,binop ,x ,y)) (guard (binop? binop))
           (select `(,x) #f
             (lambda (vx*)
               (select `(,y) #f
                 (lambda (vy*)
                   (let ([x (car vx*)] [y (car vy*)])
                     (cond
                      [(int64/label? x)
                       (let ([u (new-u)])
                         (reselect `((set! ,u ,x) ,@(C `((,binop ,u ,y))))))]
                      [(int64/label? y)
                       (let ([u (new-u)])
                         (reselect `((set! ,u ,y) ,@(C `((,binop ,x ,u))))))]
                      [(equal? ct x)
                       (cond
                        [(and (eq? binop '*) (mem? x))
                         (let ([u (new-u)])
                           (reselect `((set! ,u ,x)
                                       (set! ,u (,binop ,u ,y))
                                       ,@(C `(,u)))))]
                        [(and (mem? x) (mem? y))
                         (let ([u (new-u)])
                           (reselect `((set! ,u ,y)
                                       ,@(C `((,binop ,x ,u))))))]
                        [else (C `((,binop ,x ,y)))])]
                      [(and (equal? ct y) (commutative? binop))
                       (reselect (C `((,binop ,y ,x))))]
                      [else
                       (let ([u (new-u)])
                         (reselect `((set! ,u ,x)
                                     (set! ,u (,binop ,u ,y))
                                     ,@(C `(,u)))))]))))))]
          [((,relop ,x ,y)) (guard (relop? relop))
           (select `(,x) #f
             (lambda (vx*)
               (select `(,y) #f
                 (lambda (vy*)
                   (let ([x (car vx*)] [y (car vy*)])
                     (cond
                      [(and (not (ur? x)) (ur? y))
                       (reselect (C `((,(flip-op relop) ,y ,x))))]
                      [(int64/label? y)
                       (let ([u (new-u)])
                         (reselect `((set! ,u ,y) ,@(C `((,relop ,x ,u))))))]
                      [(number? x)
                       (let ([u (new-u)])
                         (reselect `((set! ,u ,x) ,@(C `((,relop ,u ,y))))))]
                      [(and (mem? x) (mem? y))
                       (let ((u (new-u)))
                         (reselect `((set! ,u ,x) ,@(C `((,relop ,u ,y))))))]
                      [else (C `((,relop ,x ,y)))]))))))]
          [(,exp)
           (cond
            [(or (and (eq? ct 'mref)
                      (or (mem? exp) (label? exp)))
                 (and (mem? ct)
                      (or (mem? exp) (int64/label? exp))))
             (let ((u (new-u)))
               `((set! ,u ,exp) ,@(C `(,u))))]
            [else (C `(,exp))])])))
    (select exp #f id)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Combined Passes: finalize-frame-locations and finalize-locations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; mset! and mref are passed along.

; helper for both finalize-frame-locations and finalize-locations
(define finalize
  (lambda (x env final?)
    (define lookup
      (lambda (v env)
        (let ((slot (assq v env)))
          (if slot (cdr slot) v))))
    (match x
      [(letrec ([,label* (lambda () , [bd*])] ...) , [bd])
       `(letrec ([,label* (lambda () ,bd*)] ...) ,bd)]
      [(locals (,local* ...)
         (ulocals (,ulocal* ...)
                  (locate ([,uvar* ,loc*] ...)
                    (frame-conflict ,ct ,tail))))
       `(locals (,local* ...)
          (ulocals (,ulocal* ...)
            (locate ([,uvar* ,loc*] ...)
              (frame-conflict ,ct
                 ,(finalize tail `((,uvar* . ,loc*) ...) final?)))))]
      [(locate ([,uvar* ,loc*] ...) ,tail)
       (if final?
           (finalize tail `((,uvar* . ,loc*) ...) final?)
           `(locate ([,uvar* ,loc*] ...) ,tail))]
      [(begin , [ef*] ... , [tail])
       `(begin ,ef* ... ,tail)]
      [(if , [test] , [conseq] , [altern])
       `(if ,test ,conseq ,altern)]
      [(return-point ,label ,[tail])
       `(return-point ,label ,tail)]
      [(set! ,[x] (,binop ,[y] ,[z]))
       `(set! ,x (,binop ,y ,z))]
      [(set! ,[x] ,[y])
       (if (eq? x y) `(nop) `(set! ,x ,y))]
      [(mset! ,[base] ,[off] ,[val])
       `(mset! ,base ,off ,val)]
      [(mref ,[base] ,[off])
       `(mref ,base ,off)]
      [(,op ,[x] ,[y]) (guard (or (binop? op) (relop? op)))
       `(,op ,x ,y)]
      [(,[triv] ,[live*] ...)
       (if final? `(,triv) `(,triv ,live* ...))]
      [,v (guard (uvar? v)) (lookup v env)]
      [,x x])))

(define finalize-frame-locations (lambda (x) (finalize x '() #f)))
(define finalize-locations       (lambda (x) (finalize x '() #t)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass: expose-frame-var
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This pass turns fv0, fv1, ... into displacement forms. It also adjusts
; frame var numbers by tracking the changes to frame-pointer-register.

(define expose-frame-var
  (lambda (p)
    (define fp-offset 0)
    (define m@p
      (lambda (f ls)
        (cond
         [(null? ls) '()]
         [else
          (let ((first (f (car ls))))
            (cons first (m@p f (cdr ls))))])))
    (define expose
      (lambda (p)
        (match p
          [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
           (let ([saved fp-offset])
             `(letrec ([,label* (lambda () ,(begin (set! fp-offset saved)
                                                   (expose tail*)))] ...)
                ,(begin (set! fp-offset saved) (expose tail))))]
          [(begin ,ef* ... ,tail)
           `(begin ,@(m@p expose `(,ef* ... ,tail)))]
          [(if ,test ,conseq ,alt)
           (let* ([test^ (expose test)]
                  [saved fp-offset]
                  [conseq^ (begin (set! fp-offset saved) (expose conseq))]
                  [alt^ (begin (set! fp-offset saved) (expose alt))])
             `(if ,test^ ,conseq^ ,alt^))]
          [(set! ,var (,op ,triv1 ,triv2))
           (guard (eq? var frame-pointer-register))
           (set! fp-offset ((eval op) fp-offset triv2))
           `(set! ,var (,op ,triv1 ,triv2))]
          [(set! ,[var] (,op/mref ,[triv1] ,[triv2]))
           `(set! ,var (,op/mref ,triv1 ,triv2))]
          [(set! ,[var] ,[triv])
           `(set! ,var ,triv)]
          [(mset! ,base ,off ,val)
           `(mset! ,base ,off ,val)]
          [(return-point ,label ,[tail])
           `(return-point ,label ,tail)]
          [(,[triv] ,[triv*] ...) `(,triv ,triv* ...)]
          [,v (guard (frame-var? v))
              (make-disp-opnd frame-pointer-register
                              (- (fxsll (frame-var->index v) align-shift)
                                 fp-offset))]
          [,p p])))
    (expose p)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Pass: expose-basic-blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expose-basic-blocks
  (lambda (p)
    (define new-def* '())
    (define add-def
      (lambda (def)
        (set! new-def* (union `(,def) new-def*))))
    (define shortcut
      (lambda (seq)
        (define cut
          (lambda (p)
            (match p
              [(if (true) ,a ,b) a]
              [(if (false) ,a ,b) b]
              [,p p])))
        (map cut seq)))
    (define make-def
      (lambda (l seq)
        (match (shortcut seq)
          [() '()]
          [((,triv)) (guard (and *enable-optimize-jumps* (label? triv)))
           `((,triv))]
          [,seq
           (let ([label (if (label? l) l (unique-label l))])
             (add-def `(,label (lambda () ,(make-begin seq))))
             `((,label)))])))
    (define expose1 (lambda (p) (make-begin (expose `(,p) id))))
    (define expose
      (lambda (seq C)
        (match seq
          [(letrec ([,label* (lambda () ,[expose1 -> e1*])] ...) ,[expose1 -> e2*])
           `(letrec ((,label* (lambda () ,e1*)) ... ,new-def* ...) ,e2*)]
          [((begin ,s ...)) (expose `(,s ...) C)]
          [((if ,test ,conseq ,alt) ,t* ...)
           (let* ([er* (if (null? t*) '() (make-def 'j (expose `(,t* ...) C)))]
                  [C^ (if (null? t*) C (lambda (eh*) (C `(,@eh* ,@er*))))]
                  [ec* (make-def 'c (expose `(,conseq) C^))]
                  [ea* (make-def 'a (expose `(,alt) C^))])
             (expose `(,test) (lambda (et*)
                                (shortcut `((if ,@et* ,@ec* ,@ea*))))))]
          [((return-point ,label ,tail) ,t* ...)
           (let ([et* (make-def label (expose `(,t* ...) C))])
             (expose `(,tail) (lambda (eh*) eh*)))]
          [(,h ,t ,t* ...)
           (expose `(,h) (lambda (eh*) `(,@eh* ,@(expose `(,t ,t* ...) C))))]
          [((nop)) (C '())]
          [,other (C other)])))
    (expose p id)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; flatten-program
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flatten-program
  (lambda (p)
    (define flatten
      (lambda (p next-l)
        (match p
          [(letrec ,[flatten-defs -> def*] ,[tail])
           (let ([tail (cond
                        [(null? def*) tail]
                        [else
                         (match tail
                           [(,st* ... (jump ,tail)) (guard (eq? tail (caar def*)))
                            `(,st* ...)]
                           [,tail tail])])])
             `(code ,@tail ,def* ... ...))]
          [(,label* (lambda () ,[tail*])) `(,label* ,@tail*)]
          [(begin ,[ef*] ... ,[tail]) `(,ef* ... ... ,@tail)]
          [(if ,test (,conseq) (,alt))
           (cond [(eq? conseq next-l)
                  `((if (not ,test) (jump ,alt)))]
                 [(eq? alt next-l)
                  `((if ,test (jump ,conseq)))]
                 [else `((if ,test (jump ,conseq)) (jump ,alt))])]
          [(set! ,a ,b) `((set! ,a ,b))]
          [(mset! ,base ,off ,val) `((mset! ,base ,off ,val))]
          [(,[triv]) (if (eq? triv next-l) '() `((jump ,triv)))]
          [,p p])))
    (define flatten-defs
      (lambda (defs)
        (match defs
          [() '()]
          [([,lab (lambda () ,body)]) `(,(flatten `(,lab (lambda () ,body)) #f))]
          [([,lab1 (lambda () ,body1)]
            [,lab2 (lambda () ,body2)]
            [,lab3 (lambda () ,body3)] ...)
           `(,(flatten `(,lab1 (lambda () ,body1)) lab2)
             ,@(flatten-defs `([,lab2 (lambda () ,body2)]
                               [,lab3 (lambda () ,body3)]...)))])))
    (flatten p #f)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; generate-x86-64
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This helper is needed to replace the one in helper.ss because it needs
;; to handle mset! and mref.

(define-who rand->x86-64-arg
  (lambda (rand)
    (define (register? x)
      (memq x '(rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15)))
    (cond
     [(string? rand) rand] ; precooked operand
     [(number? rand)  (format "$~s" rand)]
     [(register? rand)  (format "%~s" rand)]
     [(label? rand) (format "~a(%rip)" (label->x86-64-label rand))]
     [(disp-opnd? rand)
      (format "~s(%~s)" (disp-opnd-offset rand) (disp-opnd-reg rand))]
     [(mref? rand)
      (match rand
        [(mref ,base ,off) (guard (and (register? base) (register? off)))
         (format "(%~s,%~s)" base off)]
        [(mref ,base ,off) (guard (and (register? base) (number? off)))
         (format "~s(%~s)" off base)]
        [(mref ,base ,off) (guard (and (number? base) (register? off)))
         (format "~s(%~s)" base off)])]
     [else (error who "invalid instruction argument ~s" rand)])))

(define generate-x86-64
  (lambda (p)
    (define binop-lookup
      (lambda (op)
        (let ([op-map '([+      . addq  ]
                        [-      . subq  ]
                        [*      . imulq ]
                        [sra    . sarq  ]
                        [logand . andq  ]
                        [logor  . orq   ])])
          (cond
           [(assq op op-map) => cdr]
           [else (error 'binop-lookup "unsupported operator ~s" op)]))))
    (define relop-lookup
      (lambda (op pos?)
        (let ([op-map '([=  . (je  jne ) ]
                        [>  . (jg  jle ) ]
                        [>= . (jge jl  ) ]
                        [<  . (jl  jge ) ]
                        [<= . (jle jg  ) ])])
          (if pos?
              (car (cdr (assq op op-map)))
              (cadr (cdr (assq op op-map)))))))
    (define emit-test
      (lambda (test v)
        (match test
          [(,op ,a ,b)
           (emit 'cmpq b a)
           (emit-jump (relop-lookup op #t) v)]
          [(not (,op ,a ,b))
           (emit 'cmpq b a)
           (emit-jump (relop-lookup op #f) v)])))
    (define code-gen
      (lambda (p)
        (match p
          [(code ,stmt* ...) (for-each code-gen stmt*)]
          [(set! ,x (,op ,y ,z)) (guard (binop? op))
           (emit (binop-lookup op) (rand->x86-64-arg z) (rand->x86-64-arg y))]
          [(set! ,x ,y)
           (if (label? y)
               (emit 'leaq (rand->x86-64-arg y) (rand->x86-64-arg x))
               (emit 'movq (rand->x86-64-arg y) (rand->x86-64-arg x)))]
          [(mset! ,base ,off (,op ,rand1 ,rand2)) (guard (binop? op))
           (match rand1
             [(mref ,base^ ,off^)
              (if (or (not (eq? base base^)) (not (eq? off off^)))
                  (error 'code-gen
                         "source and dst location don't match: (~a,~a) and (~a,~a)"
                         base off base^ off^))]
             [else (error 'code-gen "illegal instruction: ~a"
                          `(mset! ,base ,off (,op ,rand1 ,rand2)))])
           (emit (binop-lookup op) (rand->x86-64-arg rand2) (rand->x86-64-arg rand1))]
          [(mset! ,base ,off ,val)
           (emit 'movq (rand->x86-64-arg val) (rand->x86-64-arg `(mref ,base ,off)))]
          [(if ,test (jump ,v)) (emit-test test v)]
          [(jump ,v) (emit-jump 'jmp v)]
          [,x (guard (label? x)) (emit-label x)]
          [,p (error 'code-gen "invalid statement ~a" p)])))
    (emit-program
     (code-gen p))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; various optimization passes from various assignments are collected here
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;; optimize-direct-call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; transform ((lambda (x* ...) body) a* ...) into (let ([x* a*] ...) body).

(define optimize-direct-call
  (lambda (x)
    (match x
      [(quote ,imm)
       `(quote ,imm)]
      [(if ,[t] ,[c] ,[a])
       `(if ,t ,c ,a)]
      [(begin ,[ef*] ...)
       `(begin ,ef* ...)]
      [((lambda (,fml* ...) ,[body]) ,[x*] ...)
       `(let ([,fml* ,x*] ...) ,body)]
      [(let ([,x* ,[v*]] ...) ,[e])
       `(let ([,x* ,v*] ...) ,e)]
      [(letrec ([,uvar* (lambda (,fml** ...) ,[x*])] ...) ,[e])
       `(letrec ([,uvar* (lambda (,fml** ...) ,x*)] ...) ,e)]
      [(,[f] ,[x*] ...)
       `(,f ,x* ...)]
      [,x x])))


;;;;;;;;;;;;;;;;;;;;; optimize-known-call ;;;;;;;;;;;;;;;;;;;;;;;;;

;; This pass is no longer needed because convert-closures does what we need
;; with it. As a check, I added a message to this pass. When this pass is
;; enabled and if it successfully optimized any known-call, it will print a
;; message. No message is printed, so this pass is not included in the
;; final passes.

;; remove the indirect calls when the closure is known. extract the label
;; inside the closure for each invocation of the closure.

(define optimize-known-call
  (lambda (x)
    (define lookup
      (lambda (x s)
        (cond
         [(assq x s) => cadr]
         [else #f])))
    (define optimize
      (lambda (cls)
        (lambda (x)
          (match x
            [(letrec ((,l* (lambda (,fml* ...) (bind-free (,x* ...) ,expr*))) ...)
               (closures ([,uvar* ,lc* ,fv* ...] ...) ,expr))
             (let* ([cls^ (append `([,uvar* ,lc*] ...) cls)]
                    [expr*^ (map (optimize cls^) expr*)]
                    [expr^ ((optimize cls^) expr)])
               `(letrec ((,l* (lambda (,fml* ...) (bind-free (,x* ...) ,expr*^))) ...)
                  (closures ([,uvar* ,lc* ,fv* ...] ...) ,expr^)))]
            [(let ([,uvar* ,[expr*]] ...) ,[expr])
             `(let ([,uvar* ,expr*] ...) ,expr)]
            [(begin ,[e*] ...) `(begin ,e* ...)]
            [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
            [(quote ,imm) `(quote ,imm)]
            [(,prim ,[x*] ...) (guard (prim? prim))
             `(,prim ,x* ...)]
            [(,[f] ,[f^] ,[x*] ...)
             `(,(or (lookup f cls) f) ,f^ ,x* ...)]
            [,x x]))))
    (let ([x* ((optimize '()) x)])
      (if (not (equal? x* x))
          (begin
            (printf "optimize-known-call is effective!\n")
            (pretty-print x)
            (printf "\n => \n\n")
            (pretty-print x*)
            x*)
          x))))




;;;;;;;;;;;;;;;;;;;;;;;;;;; optimize-jumps ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; This pass is mostly subsumed by expose-basic-blocks, but there might be
; (silly?) code written by programmers that needs this pass to optimize,
; like:

;; (letrec ([f (lambda () (g))]
;;          [g (lambda () (h))]
;;          [h (lambda () 1)])
;;   (f))

; function: eliminate jumps which contains only a jump to another label
; input: grammar after expose-basic-blocks
; output: same grammar but without those indirections

(define optimize-jumps
  (lambda (x)
    (define walk
      (lambda (s)
        (lambda (x)
          (cond
           [(assq x s) => (lambda (p) ((walk s) (cdr p)))]
           [else x]))))
    (define find-jumps
      (lambda (di)
        (define find-jumps1
          (lambda (di do s)
            (match di
              [() (values (reverse do) s)]
              [((,a (lambda () (,b))) ,d* ...) (guard (label? b))
               (let ([b* ((walk s) b)])
                 (cond
                  [(eq? a b*)
                   (find-jumps1 `(,d* ...) (cons `(,a (lambda () (,a))) do) s)]
                  [else
                   (find-jumps1 `(,d* ...) do (cons `(,a . ,b*) s))]))]
              [((,a (lambda () (begin (,b)))) ,d* ...) (guard (label? b))
               (let ([b* ((walk s) b)])
                 (cond
                  [(eq? a b*)
                   (find-jumps1 `(,d* ...) (cons `(,a (lambda () (,a))) do) s)]
                  [else
                   (find-jumps1 `(,d* ...) do (cons `(,a . ,b*) s))]))]
              [(,d ,d* ...)
               (find-jumps1 `(,d* ...) (cons d do) s)])))
        (find-jumps1 di '() '())))
    (define optimize
      (lambda (g)
        (lambda (x)
          (match x
            [(letrec ([,label (lambda () ,tail*)] ...) ,tail)
             (let-values ([(d* g) (find-jumps `([,label (lambda () ,tail*)] ...))])
               (match d*
                 [([,label (lambda () ,[(optimize g) -> tail*])] ...)
                  `(letrec ([,label (lambda () ,tail*)] ...) ,((optimize g) tail))]))]
            [(begin ,[e*] ...) `(begin ,e* ...)]
            [(if (,relop ,[x] ,[y]) ,[c] ,[a])
             `(if (,relop ,x ,y) ,c ,a)]
            [(set! ,[x] (,op ,[y] ,[z]))
             `(set! ,x (,op ,y ,z))]
            [(set! ,[x] ,[v])
             `(set! ,x ,v)]
            [(,x) (guard (label? x))
             `(,((walk g) x))]
            [,x (guard (label? x)) ((walk g) x)]
            [,x x]))))
    (if *enable-optimize-jumps* ((optimize #f) x) x)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;; pre-optimize ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; This is an additional pass added on my own in order to do some constant
; propagation. This can eliminate some code and thus saves some overhead.

; For example, the following program normally creates two closures, but now
; it doesn't create any closures because the value of t and f are flowed
; into the procedures and thus they don't have any free variables.

;; (let ([t #t] [f #f])
;;   (letrec ((even (lambda (x) (if (= x 0) t (odd (- x 1)))))
;;            (odd (lambda (x) (if (= x 0) f (even (- x 1))))))
;;     (odd 13)))

; No structured constants (pairs, vectors) are optimized due to the
; complication introduced by convert-complex-datum which made them
; indistinguishable. A reordering of the earlier passes may be needed to
; deal with those constants.

(define pre-optimize
  (lambda (x)
    (define env0
      `([+      . ,+      ]
        [-      . ,-      ]
        [*      . ,*      ]
        [sra    . ,sra    ]
        [logand . ,logand ]
        [logor  . ,logor  ]
        [=      . ,=      ]
        [>      . ,>      ]
        [>=     . ,>=     ]
        [<      . ,<      ]
        [<=     . ,<=     ]))
    (define lookup
      (lambda (x env)
        (cond
         [(assq x env) => cdr]
         [else x])))
    (define andall
      (lambda (ls)
        (cond
         [(null? ls) #t]
         [(car ls) (andall (cdr ls))]
         [else #f])))
    (define const?
      (lambda (x)
        (cond
         [(or (number? x) (boolean? x) (null? x) (vector? x)) #t]
         [(pair? x) (and (const? (car x)) (const? (cdr x)))]
         [else #f])))
    (define make-quote
      (lambda (val)
        (if (const? val) `(quote ,val) val)))
    (define separate
      (lambda (p? ls)
        (let loop ([ls ls] [tl '()] [fl '()])
          (cond
           [(null? ls) (values (reverse tl) (reverse fl))]
           [(p? (car ls)) (loop (cdr ls) (cons (car ls) tl) fl)]
           [else (loop (cdr ls) tl (cons (car ls) fl))]))))
    (define optimize
      (lambda (env tail?)
        (lambda (x)
          (match x
            [(,letr ([,uvar* ,[(optimize env #f) -> val*]] ...)
               (assigned (,as* ...) ,expr))
             (guard (memq letr '(let letrec)))
             (letv* ([(env^ bd^)
                      (separate (lambda (b) (and (not (memq (car b) as*))
                                                 (const? (cadr b))))
                                `([,uvar* ,val*] ...))]
                     [(expr^) ((optimize (append (list->alist env^) env) #t) expr)])
                 (let ([val* (map make-quote val*)])
                   `(,letr ([,uvar* ,val*] ...)
                      (assigned (,as* ...) ,expr^))))]
            [(lambda (,x* ...)
               (assigned (,as* ...) ,[(optimize env #t) -> body]))
             `(lambda (,x* ...) (assigned (,as* ...) ,body))]
            [(begin ,[(optimize env #t) -> ef*] ...)
             `(begin ,ef* ...)]
            [(if ,[(optimize env #f) -> t]
                 ,[(optimize env #t) -> c]
                 ,[(optimize env #t) -> a])
             (cond
              [(const? t) (if t c a)]
              [else `(if ,(make-quote t) ,c ,a)])]
            [(set! ,x ,[(optimize env #t) -> v])
             `(set! ,x ,v)]
            [(quote ,imm)
             (if tail? (make-quote imm) imm)]
            [(,f ,x* ...)
             (let ([ff ((optimize env #f) f)]
                   [xx* (map (optimize env #f) x*)])
               (cond
                [(and (procedure? ff) (andall (map const? xx*)))
                 (if tail?
                     (make-quote (apply ff xx*))
                     (apply ff xx*))]
                [else (let ([xx* (map make-quote xx*)])
                        `(,(if (procedure? ff) f ff) ,xx* ...))]))]
            [,x (let ([val (lookup x env)])
                  (if tail? (make-quote val) val))]))))
    (if *enable-pre-optimize*
        ((optimize env0 #t) x)
        x)))




;; (move bias)

;;;;;;;;;;;;;;;;;;;;;;;;;; forward-locations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; This pass has four sub-passes:

; - forward-propagate:  abstract interpretation forwards

; - backward-delete: backward live analysis to eliminate
; unnecessary statements.

; - backward-propagate: backward scan to mark statements that can
;   be "back propagated".

; - forward-delete: perform the back propagate and delete moved statements.




;;;;;;;;;;;;;;;;;;;;;;;;;;; forward-locations ;;;;;;;;;;;;;;;;;;;;;;;;;;;

; foward-locations to be used just before uncover-frame-conflict and
; uncover-register-conflict. It just calls forward-propagate,
; backward-delete, back-mark and forward-delete to eliminate
; unnecessary moves.

(define forward-locations
  (lambda (x ulocal*)
    (let ([p1 (backward-delete (forward-propagate x ulocal*))])
      (forward-delete (backward-propagate p1 ulocal*)))))



;;; Example from Challenge Assignment A

;; (test-one
;;  '(letrec ([sum3$1 (lambda (x.1 y.2 z.3)
;;                      (+ x.1 (+ y.2 z.3)))])
;;     (sum3$1 '5 '10 '15)))



;; (letrec ([sum3$1 (lambda ()
;;                    (begin
;;                      (nop)
;;                      (nop)
;;                      (nop)
;;                      (set! rcx fv0)
;;                      (set! rax r9)
;;                      (set! rax (+ rax rcx))
;;                      (set! r9 rax)
;;                      (set! rax r8)
;;                      (set! rax (+ rax r9))
;;                      (nop)
;;                      (r15)))])
;;   (begin
;;     (nop)
;;     (set! fv0 120)
;;     (set! r9 80)
;;     (set! r8 40)
;;     (nop)
;;     (sum3$1)))


;; (letrec ([sum3$4 (lambda ()
;;                    (begin
;;                      (nop)
;;                      (nop)
;;                      (nop)
;;                      (nop)
;;                      (set! rax r9)
;;                      (set! rax (+ rax fv0))
;;                      (set! rcx rax)
;;                      (set! rax r8)
;;                      (set! rax (+ rax rcx))
;;                      (nop)
;;                      (r15)))])
;;   (begin
;;     (nop)
;;     (set! fv0 120)
;;     (set! r8 40)
;;     (set! r9 80)
;;     (nop)
;;     (sum3$4)))




;;; a cool example from test 100:


;; (forward-locations
;;  '(begin
;;    (set! rp.11 r15)
;;    (set! v.6 r8)
;;    (set! i.5 r9)
;;    (set! n.4 fv0)
;;    (if (< i.5 n.4)
;;        (begin
;;          (set! t.10 (+ 5 i.5))
;;          (mset! v.6 t.10 i.5)
;;          (set! t.9 (+ i.5 8))
;;          (begin
;;            (set! fv0 n.4)
;;            (set! r8 v.6)
;;            (set! r9 t.9)
;;            (set! r15 rp.11)
;;            (iota-fill!$3 rbp r15 rdx fv0 r8
;;                          r9)))
;;        (begin
;;          (set! rax 30)
;;          (rp.11 rbp rax rdx))))
;;  '())

;; ==>

;; (begin
;;   (nop)
;;   (nop)
;;   (nop)
;;   (nop)
;;   (if (< r9 fv0)
;;       (begin
;;         (set! t.10 (+ 5 r9))
;;         (mset! r8 t.10 r9)
;;         (set! r9 (+ r9 8))
;;         (nop)
;;         (nop)
;;         (nop)
;;         (nop)
;;         (iota-fill!$3 rbp r15 rdx fv0 r8 r9))
;;       (begin
;;         (set! rax 30) 
;;         (r15 rbp rax rdx))))





;;;;;;;;; forward-propagate ;;;;;;;;;;;

;; This pass does forward propagation on the input program. This
;; pass is quite aggressive, it tries to evaluate expressions when
;; they contain only constants. In order to forward the locations
;; correctly, there are several rules that we must follow:

; 1. When encounter forms like (set! x y), first, eliminate in the
; substitution any pair that has x in the car or cdr, because their
; references are deprecated by this assignment. Then, extend the
; substitution with (x . y), that is, point x to the new location or
; constant y. Additionally, the assignment to frame-pointer-register would
; eliminate all mappings for frame-vars!

; 2. When there is a reference to a location x, walk x in the substitution
; and update the reference to use the "walked location" instead. This way,
; we forward the locations. This also applies to y in rule 1.

; 3. Because procedure calls may modify the registers and frame locations,
; we force a "forget" when we see procedure calls. This is done by clearing
; the substitution. Nothing goes across calls.

; 4. Currently this pass doesn't move memory locations because they are
; hard to reason about.

; 5. Currently any unspillable variables will kill another unspillable in
; the substitution because there doesn't seem to be a good way to prevent
; them to get a life range that is too big such that they would be spilled.

; 6. All machine constraints must be respected because the locations might
; be moved to where it violates the machine constraints

(define forward-propagate
  (lambda (x ulocal*)
    (define ext
      (lambda (x v s)
        (cond
         [(eq? x v) s]
         [(not (pair? v))
          (cons `(,x . ,v) s)]
         [else s])))
    (define lookup
      (lambda (x s)
        (cond
         [(assq x s) => cdr]
         [else x])))
    (define intersect
      (lambda (e1 e2)
        (cond
         [(null? e2) '()]
         [(null? e1) '()]
         [(member (car e1) e2)
          (cons (car e1) (intersect (cdr e1) e2))]
         [else (intersect (cdr e1) e2)])))
    (define eliminate
      (lambda (x s)
        (filter (lambda (p)
                  (and (not (or (eq? x (cdr p)) (eq? x (car p))))
                       (not (and (eq? x frame-pointer-register)
                                 (or (frame-var? (car p))
                                     (frame-var? (cdr p)))))
                       (not (and (memq x ulocal*)
                                 (memq (cdr p) ulocal*)))))
                s)))
    (define mem?
      (lambda (x)
        (match x
          [(mref ,base ,off) #t]
          [,x (or (frame-var? x) (label? x))])))
    (define forward
      (lambda (seq s lhs)
        (match seq
          [((begin ,ef* ...))
           (letv* ([(es* s1) (forward `(,ef* ...) s #f)])
             (values `(,(make-begin es*)) s1))]
          [((if ,test ,conseq ,alt))
           (letv* ([(et* s1) (forward `(,test) s #f)]
                   [(ec* s2) (forward `(,conseq) s1 #f)]
                   [(ea* s3) (forward `(,alt) s1 #f)])
             (match et*
               [((true)) (values ec* s2)]
               [((false)) (values ea* s3)]
               [,else (values `((if ,@et* ,@ec* ,@ea*)) (intersect s2 s3))]))]
          [((set! ,x ,y))
           (letv* ([(ey* s1) (forward `(,y) s x)])
             (values `((set! ,x ,@ey*)) (ext x (car ey*) (eliminate x s))))]
          [((mset! ,base ,off ,val))
           (letv* ([(eb* s1) (forward `(,base) s #f)]
                   [(eo* s2) (forward `(,off) s #f)]
                   [(ev* s3) (forward `(,val) s `(mref ,@eb* ,@eo*))])
             (let ([eb* (if (mem? (car eb*)) `(,base) eb*)]
                   [eo* (if (mem? (car eo*)) `(,off) eo*)]
                   [ev* (if (mem? (car ev*)) `(,val) ev*)])
               (values `((mset! ,@eb* ,@eo* ,@ev*)) s)))]
          [((mref ,base ,off))
           (letv* ([(eb* s1) (forward `(,base) s #f)]
                   [(eo* s2) (forward `(,off) s #f)])
             (let ([eb* (if (mem? (car eb*)) `(,base) eb*)]
                   [eo* (if (mem? (car eo*)) `(,off) eo*)])
               (values `((mref ,@eb* ,@eo*)) s)))]
          [((return-point ,label ,tail))
           (letv* ([(et* s1) (forward `(,tail) s #f)])
             (values `((return-point ,label ,@et*)) '()))] ; forget
          [(,h ,t ,t* ...)
           (letv* ([(eh* s1) (forward `(,h) s #f)]
                   [(et* s2) (forward `(,t ,t* ...) s1 #f)])
             (values `(,@eh* ,@et*) s2))]
          [((,op ,x ,y)) (guard (or (binop? op) (relop? op)))
           (letv* ([(ex* s1) (forward `(,x) s #f)]
                   [(ey* s2) (forward `(,y) s #f)])
             (cond
              [(and (binop? op) (number? (car ex*)) (number? (car ey*)))
               (values (list (eval `(,op ,@ex* ,@ey*))) s)]
              [(and (relop? op) (number? (car ex*)) (number? (car ey*)))
               (values (if (eval `(,op ,@ex* ,@ey*)) `((true)) `((false))) s)]
              [else
               (let* ([ex* (cond
                            [(and (equal? x lhs) (not (equal? (car ex*) lhs))) `(,x)]
                            [(and (eq? op '*) (mem? (car ex*))) `(,x)]
                            [(and (mem? (car ey*)) (mem? (car ex*))) `(,x)]
                            [(and (relop? op) (not (register? (car ex*)))) `(,x)]
                            [(and (int64? (car ex*)) (not (int32? (car ex*)))) `(,x)]
                            [else ex*])]
                      [ey* (cond
                            [(and (equal? y lhs) (not (equal? (car ey*) lhs))) `(,y)]
                            [(and (mem? (car ex*)) (mem? (car ey*))) `(,y)]
                            [(and (int64? (car ey*)) (not (int32? (car ey*)))) `(,y)]
                            [else ey*])])
                 (values `((,op ,@ex* ,@ey*)) s))]))]
          [((,target ,c-live* ...))
           (letv* ([(et* s1) (forward `(,target) s #f)])
             (values `((,@et* ,c-live* ...)) s))]
          [((nop)) (values `((nop)) s)]
          [(,x) (values (list (lookup x s)) s)])))
    (letv* ([(ex* s1) (forward x '() #f)]) ex*)))




;;;;;;;;;; backward-delete ;;;;;;;;;;;;

; This helper is similar to uncover-*-conflict, except that it does
; not distinguish uvars, registers, frame-vars. They are all treated
; the same because the only thing we care is the liveness of the
; locations. It eliminates assignments like (set! x y) when x is not
; in the live set to this point, because that means that it is not
; referenced afterwards. This way, we eliminate the assignments
; which was made unnecessary during the forward pass.

(define backward-delete
  (lambda (x)
    (define backward
      (lambda (seq live* f-live*)
        (match seq
          [((begin ,s ...))
           (letv* ([(es* ls*) (backward `(,s ...) live* f-live*)])
             (values `((begin ,@es*)) ls*))]
          [((if ,test ,conseq ,alt))
           (letv* ([(ec* lc*) (backward `(,conseq) live* f-live*)]
                   [(ea* la*) (backward `(,alt) live* f-live*)]
                   [(et* lt*) (backward `(,test) lc* la*)])
             (if (and (equal? ec* `((nop))) (equal? ea* `((nop))))
                 (values `((nop)) lt*)
                 (values `((if ,@et* ,@ec* ,@ea*)) lt*)))]
          [((set! ,x ,y))
           (cond
            [(or (eq? x y) (not (memq x live*)))
             (set! updated #t)
             (values `((nop)) live*)]
            [else
             (letv* ([(ey* ly*) (backward `(,y) live* f-live*)])
               (values `((set! ,x ,@ey*))
                       (union (difference live* `(,x)) ly*))) ])]
          [((mset! ,base ,off ,val))
           (letv* ([(eb* lb*) (backward `(,base) live* f-live*)]
                   [(eo* lo*) (backward `(,off) live* f-live*)]
                   [(ev* lv*) (backward `(,val) live* f-live*)])
             (values `((mset! ,@eb* ,@eo* ,@ev*))
                     (union live* lb* lo* lv*)))]
          [((return-point ,label ,tail))
           (letv* ([(et* lt*) (backward `(,tail) live* f-live*)])
             (values `((return-point ,label ,@et*)) lt*))]
          [(,h ,t ,t* ...)
           (letv* ([(et* lt*) (backward `(,t ,t* ...) live* f-live*)]
                   [(eh* lh*) (backward `(,h) lt* f-live*)])
             (values `(,@eh* ,@et*) lh*))]
          [((mref ,base ,off))
           (letv* ([(eb* lb*) (backward `(,base) live* f-live*)]
                   [(eo* lo*) (backward `(,off) live* f-live*)])
             (values `((mref ,@eb* ,@eo*)) (union live* lb* lo*)))]
          [((true)) (values `((true)) live*)]
          [((false)) (values `((false)) f-live*)]
          [((,op ,x ,y)) (guard (or (binop? op) (relop? op)))
           (letv* ([(ex* lx*) (backward `(,x) live* f-live*)]
                   [(ey* ly*) (backward `(,y) live* f-live*)])
             (values `((,op ,@ex* ,@ey*))
                     (union live* f-live* lx* ly*)))]
          [((,target ,c-live* ...))
           (letv* ([(et* lt*) (backward `(,target) live* f-live*)])
             (values `((,@et* ,c-live* ...))
                     (union live* lt* c-live*)))]
          [((nop)) (values `((nop)) live*)]
          [(,x) (guard (location? x)) (values `(,x) `(,x))]
          [(,x) (values `(,x) '())])))
    (letv* ([(ex* lx*) (backward x '() '())]) ex*)))




;---------- backward-propagate -----------

;;; backward propagation is for cases that can't be eliminated by
;;; forward-propagate and backward-delete, for example:

;; (forward-delete
;;  (backward-propagate
;;   '(begin
;;      (set! x.1 y.2)
;;      (set! y.2 (+ y.2 16))
;;      (set! z.3 x.1)
;;      (r15 y.2 z.3))
;;   '()))


;; ==>
;; (begin
;;   (set! z.3 y.2)
;;   (set! y.2 (+ y.2 16))
;;   (nop)
;;   (r15 y.2 z.3))


(define backward-propagate
  (lambda (x ulocal*)
    (define location?
      (lambda (x)
        (and (or (uvar? x) (register? x))
             (not (memq x ulocal*)))))
    (define ext
      (lambda (y x env)
        (cond
         [(not (location? y)) env]
         [else (cons (cons y x) env)])))
    (define rem
      (lambda (ls env)
        (filter (lambda (x) (not (memq (cdr x) ls))) env)))
    (define assq2
      (lambda (x ls)
        (cond
         [(null? ls) #f]
         [(eq? x (cdar ls)) (car ls)]
         [else (assq2 x (cdr ls))])))
    (define merge-env
      (lambda (env1 env2)
        (cond
         [(null? env1) '()]
         [(assq2 (cdar env1) env2) =>
          (lambda (p)
            (cond
             [(eq? (car p) (caar env1))
              (cons p (merge-env (cdr env1) env2))]
             [else
              (merge-env (cdr env1) env2)]))]
         [else (merge-env (cdr env1) env2)])))
    (define clear
      (lambda (env)
        '()))
    (define make-live
      (lambda (x)
        (if (location? x) `(,x) '())))
    (define backward
      (lambda (seq env live)
        (match seq
          [((begin ,s ...))
           (letv* ([(es* env1 live*) (backward `(,s ...) env live)])
             (values `((begin ,@es*)) env1 live*))]
          [((if ,test ,conseq ,alt))
           (letv* ([(ec* env1 live1) (backward `(,conseq) env live)]
                   [(ea* env2 live2) (backward `(,alt) env live)]
                   [(et* env3 live3) (backward `(,test) (merge-env env1 env2)
                                               (append live1 live2))])
             (if (and (equal? ec* `((nop))) (equal? ea* `((nop))))
                 (values `((nop)) env3 live3)
                 (values `((if ,@et* ,@ec* ,@ea*)) env3 live3)))]
          [((set! ,x ,y))
;           (printf "~a: ~a~n" `(set! ,x ,y) live)
           (letv* ([(ey* env1 live1) (backward `(,y) env live)]
                   [p (assq x env)])
             (cond
              [(and p (not (or (memq x live)
                               (memq (cdr p) live))))
               (values `((back (set! ,(cdr p) ,y)))
                       (let ([env^ (remq p env)])
                         (if (location? y) (ext y (cdr p) env^) env^))
                       (if (location? y)
                           (remq (cdr p) live)
                           (append live1 (remq (cdr p) live))))]
              [else
               (values `((set! ,x ,y))
                       (let ([env^ (rem `(,y) env)])
                         (if (and (not (frame-var? x)) (location? y)) 
                             (ext y x env^)
                             env^))
                       (if (and (not (frame-var? x)) (location? y))
                           (remq x live)
                           (append live1 (remq x live))))]))]
          [((return-point ,label ,tail))
           (letv* ([(et* env1 live1) (backward `(,tail) (clear env) live)])
             (values `((return-point ,label ,@et*)) env1 live1))]
          [((mset! ,base ,off ,val))
           (letv* ([(ev* env1 live1) (backward `(,val) env live)])
             (values `((mset! ,base ,off ,val)) (rem `(,base ,off ,val) env1)
                     (append `(,@(make-live base) ,@(make-live off))
                             live1 live)))]
          [((mref ,base ,off))
           (values `((mref ,base ,off)) (rem `(,base ,off) env) 
                   `(,@(make-live base) ,@(make-live off)))]
          [((,op ,x ,y))
           (letv* ([(ex* env1 live1) (backward `(,x) env live)]
                   [(ey* env2 live2) (backward `(,y) env live)])
             (values `((,op ,x ,y))
                     (rem `(,x ,y) env)
                     (append live1 live2)))]
          [((,f ,call-live* ...))
           (values `((,f ,call-live* ...))
                   (rem call-live* env)
                   (append call-live* live))]
          [(,h ,t ,t* ...)
           (letv* ([(et* env1 live1) (backward `(,t ,t* ...) env live)]
                   [(eh* env2 live2) (backward `(,h) env1 live1)])
             (values `(,@eh* ,@et*) env2 live2))]
          [(,x) (values `(,x) env (make-live x))])))
    (letv* ([(ex* env^ live*) (backward x '() '())]) ex*)))



(define forward-delete
  (lambda (x)
    (define check-self
      (lambda (x)
        (match x
          [((set! ,x ,y)) (if (eq? x y) `((nop)) `((set! ,x ,y)))])))
    (define forward
      (lambda (seq env)
        (match seq
          [((begin ,ef* ...))
           (letv* ([(es* env1) (forward `(,ef* ...) env)])
             (values `(,(make-begin es*)) env1))]
          [((if ,test ,conseq ,alt))
           (letv* ([(et* env1) (forward `(,test) env)]
                   [(ec* env2) (forward `(,conseq) env1)]
                   [(ea* env3) (forward `(,alt) env1)])
             (values `((if ,@et* ,@ec* ,@ea*)) env3))]
          [((back (set! ,x ,y)))
           (values (check-self `((set! ,x ,y))) (cons x env))]
          [((set! ,x ,y))
           (cond
            [(memq x env)
             (values `((nop)) (remq x env))]
            [else (values (check-self `((set! ,x ,y))) env)])]
          [((return-point ,label ,tail))
           (letv* ([(et* env1) (forward `(,tail) env)])
             (values `((return-point ,label ,@et*)) env1))]
          [(,h ,t ,t* ...)
           (letv* ([(eh* env1) (forward `(,h) env)]
                   [(et* env2) (forward `(,t ,t* ...) env1)])
             (values `(,@eh* ,@et*) env2))]
          [(,x) (values `(,x) env)])))
    (letv* ([(x^ env^) (forward x '())]) x^)))




;;; backward propagation is for cases like

;; (forward-delete
;;  (backward-propagate
;;   '(begin
;;      (set! x.1 y.2)
;;      (set! y.2 (+ y.2 16))
;;      (set! z.3 x.1)
;;      (r15 y.2 z.3))
;;   '()))


;; ==>
;; (begin
;;   (set! z.3 y.2)
;;   (set! y.2 (+ y.2 16))
;;   (nop)
;;   (r15 y.2 z.3))


;; (forward-delete
;;  (backward-propagate
;;   '(begin
;;      (set! x.1 y.2)
;;      (set! y.2 z.3)
;;      (set! z.3 x.1)
;;      (r15 y.2 z.3))
;;   '()))

;; ==> unchanged because (set! y.2 z.3) blocks the path.







;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Challenge Assignment B

;; Here are the passes which does closure "optimization". Actually they are
;; not optimization. They just generates fast code directly. For
;; documentation, see Challenge Assignment B.

;;;;;;;;;;;;;;;;;;;;;;;;;;; uncover-dynamic ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uncover-dynamic
  (lambda (x)
    (define ext append)
    (define uncover
      (lambda (lab*)
        (lambda (x)
          (match x
            [(letrec ([,uvar* (lambda (,x** ...)
                                ,[(uncover (ext uvar* lab*)) -> fv** cv** lam*])] ...)
               ,[(uncover (ext uvar* lab*)) -> fv* cv* expr])
             (let* ([fv-rhs** (map difference fv** x**)]
                    [dv-free* (map car (filter (lambda (x) (not (null? (cdr x))))
                                               `((,uvar* . ,fv-rhs**) ...)))]
                    [fv-lam** (map remq uvar* fv-rhs**)]
                    [fv-all* (union (apply union fv-rhs**) fv*)]
                    [dv-in* (union (intersection uvar* fv-all*) dv-free*)]
                    [fv-out* (difference fv-all* uvar*)]
                    [cv-lam** (map remq uvar* cv**)]
                    [cv-out* (difference (union (apply union cv**) cv*) uvar*)])
               (values fv-out* cv-out*
                       `(letrec ([,uvar*
                                  (lambda (,x** ...)
                                    (free ((,fv-lam** ...) (,cv-lam** ...)) ,lam*))] ...)
                          (dynamic (,dv-in* ...) ,expr))))]
            [(let ([,uvar* ,[(uncover lab*) -> fv** cv** expr*]] ...)
               ,[(uncover lab*) -> fv* cv* expr])
             (values (union (apply union fv**) (difference fv* uvar*))
                     (union (apply union cv**) (difference cv* uvar*))
                     `(let ([,uvar* ,expr*] ...) ,expr))]
            [(begin ,[(uncover lab*) -> fv** cv** expr*] ...)
             (values (apply union fv**) (apply union cv**) `(begin ,expr* ...))]
            [(if ,[(uncover lab*) -> fv-t* cv-t* e-t]
                 ,[(uncover lab*) -> fv-c* cv-c* e-c]
                 ,[(uncover lab*) -> fv-a* cv-a* e-a])
             (values (union fv-t* fv-c* fv-a*)
                     (union cv-t* cv-c* cv-a*)
                     `(if ,e-t ,e-c ,e-a))]
            [(quote ,imm)
             (values '() '() `(quote ,imm))]
            [(,f ,[(uncover lab*) -> fv** cv** arg*] ...)
             (cond
              [(prim? f)
               (values (apply union fv**) (apply union cv**) `(,f ,arg* ...))]
              [(memq f lab*)
               (values (apply union fv**)
                       (set-cons f (apply union cv**))
                       `(,f ,arg* ...))]
              [else
               (letv* ([(fv-f* cv-f* f) ((uncover lab*) f)])
                 (values (union fv-f* (apply union fv**))
                         (union cv-f* (apply union cv**))
                         `(,f ,arg* ...)))])]
            [,x (values `(,x) '() x)]))))
    (letv* ([(fv* cv* x*) ((uncover '()) x)]) x*)))




;;;;;;;;;;;;;;;;;;;;;;;;;;; convert-closures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define convert-closures
  (lambda (x)
    (define grow
      (lambda (node* dv*)
        (let loop ([node* node*] [node^ '()] [dv^ dv*] [go #t])
          (match node*
            [() (if go (loop node^ '() dv^ #f) (values dv^ node^))]
            [([,u1 ((,fv1* ...) (,cv1* ...))] [,u2 ((,fv2* ...) (,cv2* ...))] ...)
             (let ([fv^ (intersection cv1* dv^)])
               (cond
                [(null? fv^)
                 (loop `([,u2 ((,fv2* ...) (,cv2* ...))] ...)
                       (append node^ `([,u1 ((,fv1* ...) (,cv1* ...))]))
                       dv^ #f)]
                [else
                 (let ([fv1^ (union fv1* fv^)]
                       [cv1^ (difference cv1* fv^)])
                   (loop `([,u2 ((,fv2* ...) (,cv2* ...))] ...)
                         (append node^ `([,u1 ((,fv1^ ...) (,cv1^ ...))]))
                         (set-cons u1 dv^)
                         #t))]))]))))
    (define lookup
      (lambda (x env)
        (cond
         [(assq x env) => cdr]
         [else x])))
    (define convert
      (lambda (lab* dyn*)
        (lambda (map* x)
          (match x
            [(letrec ([,uvar* (lambda (,x* ...)
                                (free ((,fv* ...) (,cv* ...)) ,body*))] ...)
               (dynamic (,dv* ...) ,expr))
             (letv* ([dyn^ (append dv* dyn*)]
                     [(dv^ node^) (grow `([,uvar* ((,fv* ...) (,cv* ...))] ...) dyn^)]
                     [map^ (map (lambda (x)
                                  (if (memq x dv^) `((,x . ,(unique-name 'cp))) '()))
                                uvar*)]
                     [cp* (map (lambda (x) (if (null? x) '(dummy) `(,(cdar x)))) map^)]
                     [cpl* (map (lambda (x) (if (null? x) '() `(,(cdar x)))) map^)]
                     [labs (map unique-label uvar*)]
                     [lab^ (append (difference uvar* dv^) lab*)]
                     [body^ (map (convert lab^ dyn^) map^ body*)]
                     [clo* (apply append
                                  (map (lambda (x)
                                         (match x
                                           [(,u ((,fv ...) (,cv ...)))
                                            (if (memq u dv^)
                                                (let ([fv^ (map (lambda (x)
                                                                  (let ([p (assq x map*)])
                                                                    (if p (cdr p) x)))
                                                                fv)])
                                                  `([,u ,(unique-label u) ,fv^ ...]))
                                                '())]))
                                       node^))])
                 (match node^
                   [([,u* ((,fv* ...) (,cv* ...))] ...)
                    `(letrec ([,labs (lambda (,@cpl* ,x* ...)
                                       (bind-free (,@cp* ,fv* ...) ,body^)) ] ...)
                       (closures ,clo* ,((convert lab^ dyn^) map* expr)))]))]
            [(let ([,uvar* ,[expr*]] ...) ,[expr])
             `(let ([,uvar* ,expr*] ...) ,expr)]
            [(begin ,[e*] ...)
             `(begin ,e* ...)]
            [(if ,[t] ,[c] ,[a])
             `(if ,t ,c ,a)]
            [(quote ,imm)
             `(quote ,imm)]
            [(,prim ,[x*] ...) (guard (prim? prim))
             `(,prim ,x* ...)]
            [(,f ,[x*] ...) (guard (uvar? f))
             (let ([fl (unique-label f)])
               (cond
                [(memq f lab*) `(,fl ,x* ...)]
                [(assq f map*) => (lambda (p) `(,fl ,(cdr p) ,x* ...))]
                [(memq f dyn*) `(,fl ,f ,x* ...)]
                [else `(,f ,f ,x* ...)]))]
            [(,[f] ,[x*] ...)
             (let ([tmp (unique-name 't)])
               `(let ([,tmp ,f])
                  (,tmp ,tmp ,x* ...)))]
            [,x (cond
                 [(assq x map*) => cdr]
                 [else x])]))))
    (if *enable-closure-optimization*
        ((convert '() '()) '() (uncover-dynamic x))
        (convert-closures-nopt x))))




;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Analyzing Facilities ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define *all-closures* '())

(define-who analyze-closure-size
  (define Lambda
    (lambda (x)
      (match x
        [(lambda (,fml* ...)
           (bind-free (,cp ,free* ...)
             ,[Expr -> s*]))
         s*]
        [,x (error who "invalid Lambda ~s" x)])))
  (define Expr
    (lambda (x)
      (match x
        [,label (guard (label? label)) '()]
        [,uvar (guard (uvar? uvar)) '()]
        [(quote ,imm) '()]
        [(if ,[test-s*] ,[conseq-s*] ,[altern-s*])
         (append test-s* conseq-s* altern-s*)]
        [(begin ,[s**] ... ,[s*]) (apply append s* s**)]
        [(let ([,lhs* ,[s**]] ...) ,[s*]) (apply append s* s**)]
        [(letrec ([,llabel* ,[Lambda -> s**]] ...)
           (closures ([,name* ,clabel* ,free** ...] ...)
             ,[s*]))
         (apply append (map length free**) s* s**)]
        [(,prim ,[s**] ...)
         (guard (prim? prim))
         (apply append s**)]
        [(,[s*] ,[s**] ...) (apply append s* s**)]
        [,x (error who "invalid Expr ~s" x)])))
  (define analyze
    (lambda (x)
      (let ([s* (Expr x)])
        (let ([n (length s*)])
          (set! *all-closures* (append *all-closures* s*))
          (printf "closure num = ~s, avg = ~s: ~s\n"
                  n
                  (if (= n 0) '* (exact->inexact (/ (apply + s*) n)))
                  s*)))
      x))
  (lambda (x)
    (if *enable-analyze*
        (analyze x)
        x)))



(define *all-code-size* '())

(define analyze-code-size
  (lambda (x)
    (define analyze
      (lambda (x)
        (match x
          [(code ,[ins*] ...)
           (printf "code size: ~a\n" (apply + ins*))
           (set! *all-code-size* (cons (apply + ins*) *all-code-size*))
           x]
          [,x (if (label? x) 0 1)])))
    (if *enable-analyze*
        (analyze x)
        x)))


(define test-all-analyze
  (lambda ()
    (define bool->word
      (lambda (x)
        (if x "Yes" "No")))
    (fluid-let ([*enable-analyze* #t]
                [*all-closures* '()]
                [*all-code-size* '()])
      (test-all)
      (printf "\n** Options **
        forward-locations:     ~a
        closure optimization:  ~a
        pre-optimization:      ~a
        optimize jumps:        ~a\n\n"
              (bool->word *enable-forward-locations*)
              (bool->word *enable-closure-optimization*)
              (bool->word *enable-pre-optimize*)
              (bool->word *enable-optimize-jumps*))
      (printf "** closure analysis report **
       total closures created:  ~a
       total free var:          ~a
       average free var:        ~a\n\n"
              (length *all-closures*)
              (apply + *all-closures*)
              (exact->inexact (/ (apply + *all-closures*)
                                 (length *all-closures*))))
      (printf "** code length report **
       total code length:    ~a
       average code length:  ~a\n"
              (apply + *all-code-size*)
              (exact->inexact (/ (apply + *all-code-size*)
                                 (length *all-code-size*)))))))





;-------------------------------------------------------------
;                         test
;-------------------------------------------------------------



(compiler-passes '(
  parse-scheme
  convert-complex-datum
  uncover-assigned
  purify-letrec
  pre-optimize
  convert-assignments
  optimize-direct-call
  remove-anonymous-lambda
  sanitize-binding-forms
;  uncover-free
  convert-closures
  analyze-closure-size ;;;
;  optimize-known-call
  introduce-procedure-primitives
  lift-letrec
  normalize-context
  specify-representation
  uncover-locals
  remove-let
  verify-uil
  remove-complex-opera*
  impose-calling-conventions
  uncover-frame-conflict
  pre-assign-frame
  assign-new-frame
  (iterate
   finalize-frame-locations
   select-instructions
   uncover-register-conflict
   assign-registers
   (break when everybody-home?)
   assign-frame)
  finalize-locations
  expose-frame-var
  expose-basic-blocks
  optimize-jumps
  flatten-program
  analyze-code-size ;;;
;  generate-x86-64  ;; turn it on only on 64-bit machines
))


(load "tests.ss")
(tracer #f)
(test-all)

;; (test-all-analyze)
;; (test-one (nth 107 tests))

