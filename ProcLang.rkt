#lang racket
; Let Lang implementation
; Dean DeHart
; Oakland University

; References:
; 1. http://www.cs.sfu.ca/CourseCentral/383/havens/notes/Lecture11.pdf
; 2. https://github.com/mwand/eopl3/blob/master/chapter3/let-lang/lang.scm
; 3. EOPL 3rd Ed. By Daniel P. Friedman & Mitchell Wand, 2008.

; Need include for cases, define-datatype, etc.
(require (lib "eopl.ss" "eopl"))

(define empty-env-record?
  null?)

(define environment?
  (lambda (x)
    (or (empty-env-record?)
        (and (pair? x)
             (symbol? (caar x))
             (expval? (cadar x))
             (environment? (cdr x))))))

(define empty-env?
  (lambda (x)
    (empty-env-record? x)))

; This gets the symbol from the newest env.
(define extended-env-record->sym
  (lambda (record)
    (caar record)))
; This gets the expval from the newest env.
(define extended-env-record->val
  (lambda (record)
    (cadar record)))

; This removes the current env and gets the old one.
(define extended-env-record->old-env
  (lambda (record)
    (cdr record)))

(define apply-env
  (lambda (env search-sym)
    (if (empty-env? env)
        (eopl:error 'apply-env "No binding for ~s" search-sym)
        (let ([sym (extended-env-record->sym env)]
              [val (extended-env-record->val env)]
              [old-env (extended-env-record->old-env env)])
          (if (eqv? search-sym sym)
              val
              (apply-env old-env search-sym))))))

(define extended-env-record
  (lambda (sym val old-env)
    (cons (list  sym val) old-env)))

(define extend-env
  (lambda (sym val old-env)
    (extended-env-record sym val old-env)))

(define empty-env-record
  (lambda ()
    '()))

(define empty-env
  (lambda ()
    (empty-env-record)))

; Lexical specification of the language using SLLGen
  (define the-lexical-spec
      '((whitespace (whitespace) skip) ; Skip the whitespace
        (comment ("%" (arbno (not #\newline))) skip)
        (identifier
         (letter (arbno (or letter digit "_" "-" "?")))
         symbol)
        (number (digit (arbno digit)) number)
        (number ("-" digit (arbno digit)) number)
        ; Operators that take one argument and return a bool.
        (bool-unary-operator ((or "null?" "zero?")) string)
        ; Operators that take two arguments and return a bool.
        (bool-binary-operator ((or "equal?" "greater?" "less?")) string)
        ; Operators that take one argument and return something.
        (unary-operator ((or "car" "cdr" "minus" "print")) string)
        (binary-operator ((or "-" "*" "/" "+" "cons")) string)
        (n-ary-operator ("list") string)))

(define the-grammar
    '((program (expression) a-program)
      
      (expression (number) const-exp)
      (expression (identifier) var-exp)
      (expression
       ("if" expression "then" expression "else" expression)
       if-exp)
      
      #;(expression
       ("minus" "(" expression ")")
       minus-exp)

      (expression
       ("let" (arbno identifier "=" expression) "in" expression)
       let-exp)

      (expression
       ("let*" (arbno identifier "=" expression) "in" expression)
       let*-exp)

      (expression
       ("emptylist")
       emptylist-exp)

      (expression
       ("unpack" (arbno identifier) "=" expression "in" expression)
       unpack-exp)
      
      (expression
       ("half" "(" expression ")")
       half-exp)

      (expression
       (binary-operator "(" expression "," expression ")")
       binary-app-exp)

      (expression
       (bool-unary-operator "(" expression ")")
       bool-unary-app-exp)
      
      (expression
       (unary-operator "(" expression ")")
       unary-app-exp)
      
      (expression
       (n-ary-operator "(" (separated-list expression ",") ")")
       n-ary-app-exp)
      ; Proc Definitions
      (expression
       ("proc" "(" (separated-list identifier ",") ")" expression)
       proc-exp)

      (expression
       ("letproc" identifier "(" identifier ")" "=" expression "in" expression)
       letproc-exp)

      (expression
       ("(" expression (arbno expression) ")")
       call-exp)))

; Initial Environment (p. 69)
(define init-env
  (lambda ()
    (extend-env
     `i (num-val 1)
     (extend-env
      `v (num-val 5)
      (extend-env
       `x (num-val 10)
       (empty-env))))))
; Expressed Values (Figure 3.7, p. 70)
(define-datatype expval expval?
  [num-val
   (num number?)]
  [bool-val
   (bool boolean?)]
  [emptylist-val]
  [pair-val (car expval?)
            (cdr expval?)]
  [proc-val
   (proc proc?)])

(define-datatype proc proc?
  [procedure (vars (list-of symbol?))
             (body expression?)])

(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (printf "Expressed value extractor error: ~s ~s" `num val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (printf "Expressed value extractor error: ~s ~s" `bool val)))))

(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (printf "Expressed value extractor error: ~s ~s" `proc val)))))

(define apply-procedure
  (lambda (proc1 vals env)
    (cases proc proc1
      [procedure (vars body)
                 (value-of body
                           (let loop ([env env]
                                      [vars vars]
                                      [vals vals])
                             (if (null? vars)
                                 (if (null? vals)
                                     env
                                     (eopl:error 'apply-procedure "Too many arguments."))
                                 (if (null? vals)
                                     (eopl:error 'apply-procedure "Not enough arguments.")
                                     (loop (extend-env (car vars)
                                                       (car vals)
                                                       env)
                                           (cdr vars)
                                           (cdr vals))))))])))
; This procedure is the actual value-of procedure.
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      
      (if-exp (exp1 exp2 exp3)
              (let ([val1 (value-of exp1 env)])
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      ; The old let-exp
      #;(let-exp (var exp1 body)
               (let ([val1 (value-of exp1 env)])
                 (value-of body
                           (extend-env var val1 env))))
      ; Exercise 3.16 Homework 4 Question 4.
      ; New let-exp
      (let-exp (vars exps body)
               ; This will create a container from the list of variables
               ; with all of them having been evaluated in the environment.
               ; Ex: Let x = 5 y = 6 in -(y,x)
               ; It will evaluate x & y in the environment p.
               (let ([values (map (lambda (exp)
                                    (value-of exp env))
                                  exps)])
                 (value-of body
                           (let loop ([env env]
                                      [vars vars]
                                      [values values])
                             (if (null? vars)
                                 env
                                 (loop (extend-env (car vars) (car values) env)
                                       (cdr vars)
                                       (cdr values)))))))
      (let*-exp (vars exps body)
                (let loop ([env env]
                           [vars vars]
                           [exps exps])
                  (if (null? vars)
                      (value-of body env)
                      (loop (extend-env (car vars)
                                        (value-of (car exps) env)
                                        env)
                            (cdr vars)
                            (cdr exps)))))
                                        
      ; Needed for exercise 3.18
      (emptylist-exp ()
                     (emptylist-val))
      ; Exercise 3.18 Homework 4 Question 5.
      ; Unpack-exp
      (unpack-exp (vars exp1 body)
                  (let loop ([env env]
                             [vars vars]
                             [vals (value-of exp1 env)])
                    (if (null? vars)
                        (cases expval vals
                          [emptylist-val () (value-of body env)]
                          [pair-val (car-vals cdr-vals)
                                    (eopl:error 'value-of "Too many values to unpack.")]
                          [else (eopl:error 'value-of "Expected a pair.")])
                        (cases expval vals
                          [emptylist-val () (eopl:error 'value-of "Not enough values to unpack.")]
                          [pair-val (car-vals cdr-vals) (loop (extend-env (car vars) car-vals env)
                                                              (cdr vars)
                                                              cdr-vals)]
                          [else (eopl:error 'value-of "Expected a pair.")]))))
      
      
      #;(minus-exp (exp1)
             (let ([val1 (value-of exp1 env)])
                   (num-val (- (expval->num val1)))))
      (unary-app-exp (rator exp1)
                     (let ([val (value-of exp1 env)])
                       (cond
                         [(equal? rator "car")
                          (cases expval val
                            [pair-val (car cdr) car]
                            [else (eopl:error 'value-of "Expected a pair")])]
                         [(equal? rator "cdr")
                          (cases expval val
                            [pair-val (car cdr) cdr]
                            [else (eopl:error 'value-of "Expected a pair")])]
                         [(equal? rator "minus")
                          (num-val (- (expval->num val)))]
                         [equal? rator "print"
                                 (let ([scheme-value
                                        (let loop ([val val])
                                          (cases expval val
                                            [num-val (value) value]
                                            [bool-val (boolean) boolean]
                                            [emptylist-val () '()]
                                            [pair-val (car cdr)
                                                      (cons (loop car)
                                                            (loop cdr))]
                                            [proc-val (proc) proc]))])
                                   (display scheme-value)
                                   (newline)
                                   (num-val 1))]
                         [else (eopl:error 'value-of-bool-exp "Unknown operator: ~s" rator)])))
                       
                        
      [half-exp (exp1)
                (let ([result (value-of exp1 env)])
                  (num-val (/ (expval->num result) 2)))]
      ; Exercise 3.7
      (binary-app-exp (rator exp1 exp2)
                      (cond
                        [(equal? rator "-")
                         (arithmetic (string->procedure rator) exp1 exp2 env)]
                        [(equal? rator "+")
                         (arithmetic (string->procedure rator) exp1 exp2 env)]
                        [(equal? rator "*")
                         (arithmetic (string->procedure rator) exp1 exp2 env)]
                        [(equal? rator "/")
                         (arithmetic (string->procedure rator) exp1 exp2 env)]
                        [(equal? rator "cons")
                         (pair-val (value-of (car exp) env) (value-of (cdr exp) env))]
                        [else (eopl:error 'value-of "Expected a good rator")]))
      (bool-unary-app-exp (rator exp1)
                          (let ([val (value-of exp1 env)])
                            
                            (cond
                              [(equal? rator "null?")
                               (bool-val (cases expval val
                                           [emptylist-val () #t]
                                           [else #f]))]
                              [(equal? rator "zero?")
                               (bool-val (zero? (expval->num val)))]
                              [else (printf "Unknown operator: ~s." rator)])))
      (n-ary-app-exp (rator exps)
                     (let ([vals (map (lambda (e)
                                        (value-of e env))
                                        exps)])
                       (cond
                         [(equal? rator "list")
                          (let loop ([vals vals])
                            (if (null? vals)
                                (emptylist-val)
                                (pair-val (car vals)
                                          (loop (cdr vals)))))]
                         [else (eopl:error 'value-of-nary-exp "Unknown operator: ~s." rator)])))
      [proc-exp (vars body)
                (proc-val (procedure vars body))]
      [letproc-exp (name var body bexp)
                   (value-of bexp
                             (extend-env name
                                         (proc-val (procedure var body env))
                                         env))]
      [call-exp (rator rands)
                (let ([proc (expval->proc (value-of rator env))]
                      [args (map (lambda (rand)
                                   (value-of rand env))
                                 rands)])
                  (apply-procedure proc args env))])))

(define arithmetic
  (lambda (sym exp1 exp2 env)
    (let* ([val1 (value-of exp1 env)]
           [val2 (value-of exp2 env)]
           [num1 (expval->num val1)]
           [num2 (expval->num val2)])
                 (num-val (sym num1 num2)))))


(define string->procedure
  (lambda (s)
    (eval (string->symbol s))))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

(define repl
 (sllgen:make-rep-loop "--> "
 (lambda (pgm) (value-of-program pgm))
 (sllgen:make-stream-parser the-lexical-spec the-grammar)))

; The Interpreter for the Let Language (Figure 3.8-9, p. 71-72)
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))
; This procedure allows us to call the value-of procedure
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (init-env))))))

; Sample Program for testing purposes.
(define sp "let x = 5 in -(6,x)")
; null?(emptylist)
; Output: #(struct:bool-val #t)
; Proc test
(define proctest
"let x = 200
in let f = proc (z) -(z,x)
in let x = 100
in let g = proc (z) -(z,x)
in -((f 1), (g 1))")
(define letproctest
  "letproc g (x) = -(6,x)
in (g 4)")
(define newproctest
  "let f = proc (x,y) -(-(x,5),-(y,2))
in (f 10 3)")
; Test Dynamic Binding
(define dynbindtest
"let a = 3
  in let p = proc (x) -(x,a)
   a = 5
    in -(a,(p 2))")
(define times4
  "let makemult = proc (maker)
                proc (x)
                 if zero?(x)
                 then 0
                 else -(((maker maker) -(x,1)), -4)
in let times4 = proc (x) ((makemult makemult) x)
   in (times4 3)")
(define makefact
  "let maketimes = proc (maker)
                  proc (x)
                    proc (y)
                      if zero?(x)
                      then 0
                      else -((((maker maker) -(x, 1)) y), -(0, y))
in let times = (maketimes maketimes)
   in let makefact = proc (maker)
                       proc (x)
                         if zero?(x)
                         then 1
                         else ((times x) ((maker maker) -(x, 1)))
      in (makefact makefact)")
(define oddity
  "let false = zero?(1)
in let true = zero?(0)
   in let makeeven = proc (makeeven)
                       proc (makeodd)
                         proc (x)
                           if zero?(x)
                           then true
                           else (((makeodd makeeven) makeodd) -(x, 1))
      in let makeodd = proc (makeeven)
                         proc (makeodd)
                           proc (x)
                             if zero?(x)
                             then false
                             else (((makeeven makeeven) makeodd) -(x, 1))
         in ((makeodd makeeven) makeodd)")
(define evenity
  "let false = zero?(1)
in let true = zero?(0)
   in let makeeven = proc (makeeven)
                       proc (makeodd)
                         proc (x)
                           if zero?(x)
                           then true
                           else (((makeodd makeeven) makeodd) -(x, 1))
      in let makeodd = proc (makeeven)
                         proc (makeodd)
                           proc (x)
                             if zero?(x)
                             then false
                             else (((makeeven makeeven) makeodd) -(x, 1))
         in ((makeodd makeeven) makeodd)")


; Environment (p. 40)
#;(define empty-env
  (lambda ()
    (lambda (search-var)
      (printf "There is no binding for the search var ~s in this environment." search-var)
      (newline))))
; Extend environment is an environment that will return a binding
#;(define extend-env
  (lambda (saved-var saved-val saved-env)
    (lambda (search-var)
      (if (eqv? search-var saved-var)
          saved-val
          (apply-env saved-env search-var)))))
; Apply environment takes in an environment and a search var
#;(define apply-env
  (lambda (env search-var)
    (env search-var)))