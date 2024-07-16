(define (deep-copy obj)
    (cond
        ((null? obj) '())
        ((pair? obj) (cons (deep-copy (car obj)) (deep-copy (cdr obj))))
        (else obj)))

(define (make-let as ex)
    (if (null? as) ex `(let ,as ,ex)))
(define (make-letrec as ex)
    (if (null? as) ex `(letrec ,as ,ex)))

(define val-prim* `(+ - * car cdr cons make-vector vector-length vector-ref void))
(define pr-prim* `(<= < = > >= boolean? eq? fixnum? null? pair? vector? procedure?))
(define ef-prim* `(set-car! set-cdr! vector-set!))
(define prim* (append val-prim* pr-prim* ef-prim*))
        
;   parse-scheme
;   var -> uvar
;   add and / or / not / one-armed if / imm / expr+ ...

(define (parse-scheme expr)
    (define (prim->len p)
        (match p
            [+ 2] [- 2] [* 2] [car 1] [cdr 1] [cons 2] [make-vector 1] [vector-length 1] [vector-ref 2] [void 0]
            [<= 2] [< 2] [= 2] [> 2] [>= 2] [boolean? 1] [eq? 2] [fixnum? 1] [null? 1] [pair? 1] [vector? 1] [procedure? 1]
            [set-car! 2] [set-cdr! 2] [vector-set! 3]))

    (define (parse-and expr*)
        (case (length expr*)
            [0 `(quote #t)]
            [1 (car expr*)]
            [else `(if ,(car expr*) 
                        ,(parse-and (cdr expr*))
                        (quote #f))]))
    (define (parse-or expr*)
        (case (length expr*)
            [0 `(quote #f)]
            [1 (car expr*)]
            [else 
                (let ([uv (unique-name `por)])
                    (make-let `([,uv ,(car expr*)]) 
                              `(if ,uv ,uv ,(parse-or (cdr expr*)))))]))

    (define (parse-vector vec cnt)
        (if (= cnt (vector-length vec))
            #t
            (let ([res (parse-vector vec (+ 1 cnt))]
                  [fir (parse-datum (vector-ref vec cnt))])
                  (and res fir))))
    (define (parse-pair p)
        (if (and (parse-datum (car p)) (parse-datum (cdr p))) #t #f))

    (define (parse-datum dat)
        (if (immediate? dat)
            #t
            (cond
                [(pair? dat) (parse-pair dat)]
                [(vector? dat) (parse-vector dat 0)]
                [else #f])))
    (define (immediate? imm)
        (cond
            [(eq? imm #t) #t]
            [(eq? imm #f) #t]
            [(eq? imm `()) #t]
            [(and (integer? imm) (exact? imm) (fixnum-range? imm)) #t]
            [else #f]))

    (define (parse-expr env)
        (lambda (expr)
            (match expr
                [(if ,[(parse-expr env) -> ex1] ,[(parse-expr env) -> ex2]) 
                    (guard (not (assq `if env))) `(if ,ex1 ,ex2 (void))]
                [(if ,[(parse-expr env) -> ex1] ,[(parse-expr env) -> ex2] ,[(parse-expr env) -> ex3])
                    (guard (not (assq `if env))) `(if ,ex1 ,ex2 ,ex3)]
                [(and ,[(parse-expr env) -> ex*] ...)
                    (guard (not (assq `and env))) (parse-and ex*)]
                [(or ,[(parse-expr env) -> ex*] ...)
                    (guard (not (assq `or env))) (parse-or ex*)]
                [(begin ,[(parse-expr env) -> ex1*] ... ,[(parse-expr env) -> ex2])
                    (guard (not (assq `begin env))) (make-begin `(,ex1* ... ,ex2))]
                [(lambda ,para* ,ex1* ... ,ex2)
                    (guard (not (assq `lambda env)))
                        ; to do: verify that all paras are symbol and pairwisely different
                        (let* ([uv* (map unique-name para*)]
                               [new-env (append `([,para* . ,uv*] ...) env)]
                               [new-ex1* (map (parse-expr new-env) ex1*)]
                               [new-ex2 ((parse-expr new-env) ex2)])
                            `(lambda ,uv*
                                ,(make-begin `(,new-ex1* ... ,new-ex2))))]
                [(let ([,v* ,[(parse-expr env) -> ex1*]] ...) ,ex2* ... ,ex3)
                    (guard (not (assq `let env)))
                        ; to do: verify that all paras are symbol and pairwisely different
                        (let* ([uv* (map unique-name v*)]
                               [new-env (append `([,v* . ,uv*] ...) env)]
                               [new-ex2* (map (parse-expr new-env) ex2*)]
                               [new-ex3 ((parse-expr new-env) ex3)])
                            (make-let `([,uv* ,ex1*] ...)
                                      (make-begin `(,new-ex2* ... ,new-ex3))))]
                [(letrec ([,v* ,ex1*] ...) ,ex2* ... ,ex3)
                    (guard (not (assq `letrec env)))
                        ; to do: verify that all paras are symbol and pairwisely different
                        (let* ([uv* (map unique-name v*)]
                               [new-env (append `([,v* . ,uv*] ...) env)]
                               [new-ex1* (map (parse-expr new-env) ex1*)]
                               [new-ex2* (map (parse-expr new-env) ex2*)]
                               [new-ex3 ((parse-expr new-env) ex3)])
                            (make-letrec `([,uv* ,new-ex1*] ...)
                                         (make-begin `(,new-ex2* ... ,new-ex3))))]
                [(set! ,v ,[(parse-expr env) -> ex])
                    (guard (not (assq `set! env)))
                        (if (symbol? v)
                            (if (assq v env)
                                `(set! ,(cdr (assq v env)) ,ex)
                                (error "set!: v is not in env " v))
                            (error "set!: v is not a symbol" v))]
                [(not ,[(parse-expr env) -> ex])
                    (guard (not (assq `not env)))
                        `(if ,ex (quote #f) (quote #t))]
                [(,p ,[(parse-expr env) -> ex*] ...) 
                    (guard (and (memq p prim*) (not (assq p env))))
                        (if (= (length ex*) (prim->len p))
                            `(,p ,ex* ...) 
                            (error "prim-call: length mismatch" p))]
                [(quote ,dat)
                    (guard (not (assq `quote env)))
                        (if (parse-datum dat)
                            `(quote ,dat)
                            (error "quote: invalid datum" dat))]
                [,imm (guard (immediate? imm)) `(quote ,imm)]
                [,v (guard (symbol? v))
                    (if (assq v env)
                        (cdr (assq v env))
                        (error "var: v is not in env" v))]
                [(,[(parse-expr env) -> ex1] ,[(parse-expr env) -> ex2*] ...) `(,ex1 ,ex2* ...)]
                [,x (error "unknown fault" x)])))

    ((parse-expr `()) expr))

;   convert-complex-datum
;   (quote dat) -> (quote imm)

(define (convert-complex-datum expr)
    (define constant* `())
    (define expr* `())

    (define (convert-expr expr)
        (match expr
            [,uv (guard (uvar? uv)) expr]
            [(quote ,dat)
                (if (or (pair? dat) (vector? dat))
                    (let ([uv (unique-name `constant)]
                          [ex (convert-datum dat)])
                        (set! constant* (cons uv constant*))
                        (set! expr* (cons (deep-copy ex) expr*))
                        uv)
                    `(quote ,dat))]
            [(lambda ,para* ,[convert-expr -> ex]) `(lambda ,para* ,ex)]
            [(if ,[convert-expr -> ex1] ,[convert-expr -> ex2] ,[convert-expr -> ex3]) `(if ,ex1 ,ex2 ,ex3)]
            [(begin ,[convert-expr -> ex1*] ... ,[convert-expr -> ex2]) (make-begin `(,ex1* ... ,ex2))]
            [(let ([,uv* ,[convert-expr -> ex1*]] ...) ,[convert-expr -> ex2]) (make-let `([,uv* ,ex1*] ...) ex2)]
            [(letrec ([,uv* ,[convert-expr -> ex1*]] ...) ,[convert-expr -> ex2]) (make-letrec `([,uv* ,ex1*] ...) ex2)]
            [(set! ,uv ,[convert-expr -> ex]) `(set! ,uv ,ex)]
            [(,p ,[convert-expr -> ex*] ...) (guard (memq p prim*)) `(,p ,ex* ...)]
            [(,[convert-expr -> ex1] ,[convert-expr -> ex2*] ...) `(,ex1 ,ex2* ...)]))
    
    (define (helper vec dat cnt)
        (if (= cnt (vector-length dat))
            `()
            (let ([res (helper vec dat (+ 1 cnt))]
                  [fir `(vector-set! ,vec (quote ,cnt) ,(convert-datum (vector-ref dat cnt)))])
                  (cons fir res))))

    (define (make-vector datum)
        (let* ([uv (unique-name `vec)]
               [vector-set* (helper uv datum 0)])
            (match datum [,x ; in order to use ... 
                (make-let `([,uv (make-vector (quote ,(vector-length datum)))])
                          (make-begin `(,vector-set* ... ,uv)))])))
    
    (define (make-pair datum)
        (let ([fir (convert-datum (car datum))]
              [sec (convert-datum (cdr datum))])
            `(cons ,fir ,sec)))

    (define (convert-datum datum)
        (cond   
            [(vector? datum) (make-vector datum)]
            [(pair? datum) (make-pair datum)]
            [else `(quote ,datum)]))

    (let* ([new-ex (convert-expr expr)]
           [cp-expr* (deep-copy expr*)])
        (match expr [,x ; in order to use ...
            (make-let `([,constant* ,cp-expr*] ...) new-ex)])))

;   uncover-assigned
;   find all assigned variables and record them in (assigned) form

(define (uncover-assigned expr)
    (define (uncover-expr expr)
        (match expr
            [,uv (guard (uvar? uv)) (values expr `())]
            [(quote ,imm) (values expr `())]
            [(lambda ,para* ,[uncover-expr -> ex uv*])
                (values `(lambda ,para* (assigned ,(intersection para* uv*) ,ex))
                        (difference uv* para*))]
            [(if ,[uncover-expr -> ex1 uv1*] ,[uncover-expr -> ex2 uv2*] ,[uncover-expr -> ex3 uv3*])
                (values `(if ,ex1 ,ex2 ,ex3) (union uv1* uv2* uv3*))]
            [(begin ,[uncover-expr -> ex1* uv1**] ... ,[uncover-expr -> ex2 uv2*])
                (values (make-begin `(,ex1* ... ,ex2)) (union uv2* (apply union uv1**)))]
            [(let ([,uv* ,[uncover-expr -> ex1* uv1**]] ...) ,[uncover-expr -> ex2 uv2*])
                (values `(let ([,uv* ,ex1*] ...) (assigned ,(intersection uv* uv2*) ,ex2))
                        (union (difference uv2* uv*) (apply union uv1**)))]
            [(letrec ([,uv* ,[uncover-expr -> ex1* uv1**]] ...) ,[uncover-expr -> ex2 uv2*])
                (let ([as-uv* (union uv2* (apply union uv1**))])
                    (values `(letrec ([,uv* ,ex1*] ...) (assigned ,(intersection uv* as-uv*) ,ex2))
                        (difference as-uv* uv*)))]
            [(set! ,uv ,[uncover-expr -> ex uv*])
                (values `(set! ,uv ,ex) (set-cons uv uv*))]
            [(,p ,[uncover-expr -> ex* uv**] ...) (guard (memq p prim*)) 
                (values `(,p ,ex* ...) (apply union uv**))]
            [(,[uncover-expr -> ex1 uv1*] ,[uncover-expr -> ex2* uv2**] ...) 
                (values `(,ex1 ,ex2* ...) (union uv1* (apply union uv2**)))]))

    (let-values ([(ex uv*) (uncover-expr expr)]) ex))

;   purify-letrec
;   all letrec expressions should be pure, i.e., are lambda expressions and not assigned
;   otherwise we will convert it to (let (let (set!)))

(define (purify-letrec expr)
    (define (lambdas? expr*)
        (if (null? expr*)
            #t
            (let ([res (lambdas? (cdr expr*))]
                  [fir (car expr*)])
                (match fir
                    [(lambda ,para* ,ex) res]
                    [,x #f]))))

    (define (purify-expr expr)
        (match expr
            [,uv (guard (uvar? uv)) expr]
            [(quote ,imm) expr]
            [(lambda ,para* (assigned ,as-para* ,[purify-expr -> ex]))
                `(lambda ,para* (assigned ,as-para* ,ex))]
            [(if ,[purify-expr -> ex1] ,[purify-expr -> ex2] ,[purify-expr -> ex3])
                `(if ,ex1 ,ex2 ,ex3)]
            [(begin ,[purify-expr -> ex1*] ... ,[purify-expr -> ex2])
                (make-begin `(,ex1* ... ,ex2))]
            [(let ([,uv* ,[purify-expr -> ex1*]] ...) (assigned ,as-uv* ,[purify-expr -> ex2]))
                `(let ([,uv* ,ex1*] ...) (assigned ,as-uv* ,ex2))]
            [(letrec ([,uv* ,[purify-expr -> ex1*]] ...) (assigned ,as-uv* ,[purify-expr -> ex2]))
                (if (and (lambdas? ex1*) (null? as-uv*))
                    `(letrec ([,uv* ,ex1*] ...) ,ex2)
                    (let* ([tmp-uv* (map unique-name uv*)]
						   [set* `((set! ,uv* ,tmp-uv*) ...)])
						`(let ([,uv* (void)] ...) (assigned ,uv*
							(begin
								(let ([,tmp-uv* ,ex1*] ...) (assigned () (begin ,set* ...)))
								,ex2)))))]
            [(set! ,uv ,[purify-expr -> ex]) `(set! ,uv ,ex)]
            [(,p ,[purify-expr -> ex*] ...) (guard (memq p prim*)) `(,p ,ex* ...)]
            [(,[purify-expr -> ex1] ,[purify-expr -> ex2*] ...) `(,ex1 ,ex2* ...)]))

    (purify-expr expr))

;   convert-assignments
;   convert all assigned variable into (car x) & (set-car! x)
;   1. store imm in heap area 2. modify the data instead of the pointer

(define (convert-assignments expr)
    (define (f assoc*)
        (lambda (x) 
            (if (assq x assoc*)
                (cdr (assq x assoc*))
                x)))

    (define (convert-expr assigned-uv*)
        (lambda (expr)
            (match expr
                [,uv (guard (uvar? uv))
                    (if (memq uv assigned-uv*) `(car ,uv) uv)]
                [(quote ,imm) expr]
                [(lambda ,para* (assigned ,as-uv* ,ex))
                    (let* ([tmp-uv* (map unique-name as-uv*)]
                           [assoc* `((,as-uv* . ,tmp-uv*) ...)]
                           [new-para* (map (f assoc*) para*)])
                        `(lambda ,new-para* 
                            ,(make-let `([,as-uv* (cons ,tmp-uv* (void))] ...)
                                       ((convert-expr (append assigned-uv* as-uv*)) ex))))]
                [(if ,[(convert-expr assigned-uv*) -> ex1] 
                     ,[(convert-expr assigned-uv*) -> ex2] 
                     ,[(convert-expr assigned-uv*) -> ex3])
                    `(if ,ex1 ,ex2 ,ex3)]
                [(begin ,[(convert-expr assigned-uv*) -> ex1*] ... ,[(convert-expr assigned-uv*) -> ex2])
                    (make-begin `(,ex1* ... ,ex2))]
                [(let ([,uv* ,[(convert-expr assigned-uv*) -> ex1*]] ...) (assigned ,as-uv* ,ex2))
                    (let* ([tmp-uv* (map unique-name as-uv*)]
                           [assoc* `((,as-uv* . ,tmp-uv*) ...)]
                           [new-uv* (map (f assoc*) uv*)])
                        (make-let `([,new-uv* ,ex1*] ...) 
                                  (make-let `([,as-uv* (cons ,tmp-uv* (void))] ...)
                                            ((convert-expr (append assigned-uv* as-uv*)) ex2))))]
                [(letrec ([,uv* ,[(convert-expr assigned-uv*) -> ex1*]] ...) ,[(convert-expr assigned-uv*) -> ex2])
                    `(letrec ([,uv* ,ex1*] ...) ,ex2)]
                [(set! ,uv ,[(convert-expr assigned-uv*) -> ex])
                    (if (memq uv assigned-uv*)
                        `(set-car! ,uv ,ex)
                        `(set! ,uv ,ex))]
                [(,p ,[(convert-expr assigned-uv*) -> ex*] ...) (guard (memq p prim*)) `(,p ,ex* ...)]
                [(,[(convert-expr assigned-uv*) -> ex1] ,[(convert-expr assigned-uv*) -> ex2*] ...)
                    `(,ex1 ,ex2* ...)])))

    ((convert-expr `()) expr))

;   optimize-direct-call
;   transfrom those def-when-used anonymous lambda into let expressions

(define (optimize-direct-call expr)
    (define (opt-expr expr)
        (match expr
            [,uv (guard (uvar? uv)) expr]
            [(quote ,imm) expr]
            [(lambda ,para* ,[opt-expr -> ex]) `(lambda ,para* ,ex)]
            [(if ,[opt-expr -> ex1] ,[opt-expr -> ex2] ,[opt-expr -> ex3]) `(if ,ex1 ,ex2 ,ex3)]
            [(begin ,[opt-expr -> ex1*] ... ,[opt-expr -> ex2]) (make-begin `(,ex1* ... ,ex2))]
            [(let ([,uv* ,[opt-expr -> ex1*]] ...) ,[opt-expr -> ex2]) (make-let `([,uv* ,ex1*] ...) ex2)]
            [(letrec ([,uv* (lambda ,para** ,[opt-expr -> ex1*])] ...) ,[opt-expr -> ex2])
                `(letrec ([,uv* (lambda ,para** ,ex1*)] ...) ,ex2)]
            [(,p ,[opt-expr -> ex*] ...) (guard (memq p prim*)) `(,p ,ex* ...)]
            [((lambda ,para* ,[opt-expr -> ex1]) ,[opt-expr -> ex2*] ...) (make-let `([,para* ,ex2*] ...) ex1)]
            [(,[opt-expr -> ex1] ,[opt-expr -> ex2*] ...) `(,ex1 ,ex2* ...)]))

    (opt-expr expr))

;   remove-anonymous-lambda
;   each anonymous lambda will be given a name

(define (remove-anonymous-lambda expr)
    (define (let-helper expr)
        (match expr
            [(lambda ,para* ,[remove-expr -> ex]) `(lambda ,para* ,ex)]
            [,[remove-expr -> ex] ex]))

    (define (remove-expr expr)
        (match expr
            [,uv (guard (uvar? uv)) expr]
            [(quote ,imm) expr]
            [(lambda ,para* ,[remove-expr -> ex]) 
                (let ([uv (unique-name `anon)])
                    `(letrec ([,uv (lambda ,para* ,ex)]) ,uv))]
            [(if ,[remove-expr -> ex1] ,[remove-expr -> ex2] ,[remove-expr -> ex3]) `(if ,ex1 ,ex2 ,ex3)]
            [(begin ,[remove-expr -> ex1*] ... ,[remove-expr -> ex2]) (make-begin `(,ex1* ... ,ex2))]
            [(let ([,uv* ,[let-helper -> ex1*]] ...) ,[remove-expr -> ex2])
                `(let ([,uv* ,ex1*] ...) ,ex2)]
            [(letrec ([,uv* (lambda ,para** ,[remove-expr -> ex1*])] ...) ,[remove-expr -> ex2])
                `(letrec ([,uv* (lambda ,para** ,ex1*)] ...) ,ex2)]
            [(,p ,[remove-expr -> ex*] ...) (guard (memq p prim*)) `(,p ,ex* ...)]
            [(,[remove-expr -> ex1] ,[remove-expr -> ex2*] ...) `(,ex1 ,ex2* ...)]))

    (remove-expr expr))

;   sanitize-binding-forms
;   at this point, letrec is okay, however let may bind a lambda exoression
;   (let ([x (lambda ...)])) -> (letrec)

(define (sanitize-binding-forms expr)
    (define (filter uvar* expr*)
        (if (null? expr*)
            (values `() `())
            (let-values ([(proc* other*) (filter (cdr uvar*) (cdr expr*))])
                (let ([uvar (car uvar*)]
                      [expr (car expr*)])
                    (match expr
                        [(lambda ,para* ,[sanitize-expr -> ex])
                            (values (cons `[,uvar (lambda ,para* ,ex)] proc*) other*)]
                        [,[sanitize-expr -> ex]
                            (values proc* (cons `[,uvar ,ex] other*))])))))
    (define (sanitize-expr expr)
        (match expr
            [,uv (guard (uvar? uv)) expr]
            [(quote ,imm) expr]
            [(if ,[sanitize-expr -> ex1] ,[sanitize-expr -> ex2] ,[sanitize-expr -> ex3]) `(if ,ex1 ,ex2 ,ex3)]
            [(begin ,[sanitize-expr -> ex1*] ... ,[sanitize-expr -> ex2]) (make-begin `(,ex1* ... ,ex2))]
            [(let ([,uv* ,ex1*] ...) ,[sanitize-expr -> ex2])
                (let-values ([(proc* other*) (filter uv* ex1*)])
                    (make-letrec proc* (make-let other* ex2)))]
            [(letrec ([,uv* (lambda ,para** ,[sanitize-expr -> ex1*])] ...) ,[sanitize-expr -> ex2])
                (make-letrec `([,uv* (lambda ,para** ,ex1*)] ...) ex2)]
            [(,p ,[sanitize-expr -> ex*] ...) (guard (memq p prim*)) `(,p ,ex* ...)]
            [(,[sanitize-expr -> ex1] ,[sanitize-expr -> ex2*] ...) `(,ex1 ,ex2* ...)]))

    (sanitize-expr expr))

;   uncover-free
;   find free variables in each procedure

(define (uncover-free expr)
    (define (uncover-expr expr)
        (match expr
            [,uv (guard (uvar? uv)) (values expr `(,uv))]
            [(quote ,imm) (values expr `())]
            [(if ,[uncover-expr -> ex1 uv1*] ,[uncover-expr -> ex2 uv2*] ,[uncover-expr -> ex3 uv3*])
                (values `(if ,ex1 ,ex2 ,ex3) (union uv1* uv2* uv3*))]
            [(begin ,[uncover-expr -> ex1* uv1**] ... ,[uncover-expr -> ex2 uv2*])
                (values (make-begin `(,ex1* ... ,ex2)) (union uv2* (apply union uv1**)))]
            [(let ([,uv* ,[uncover-expr -> ex1* uv1**]] ...) ,[uncover-expr -> ex2 uv2*])
                (values `(let ([,uv* ,ex1*] ...) ,ex2) (union (difference uv2* uv*) (apply union uv1**)))]
            [(letrec ([,uv* (lambda ,para** ,[uncover-expr -> ex1* uv1**])] ...) ,[uncover-expr -> ex2 uv2*])
                (let ([free-uv** (map difference uv1** para**)])
                    (values `(letrec ([,uv* (lambda ,para** (free ,free-uv** ,ex1*))] ...) ,ex2)
                            (union (difference (apply union free-uv**) uv*) (difference uv2* uv*))))]
            [(,p ,[uncover-expr -> ex* uv**] ...) (guard (memq p prim*)) 
                (values `(,p ,ex* ...) (apply union uv**))]
            [(,[uncover-expr -> ex1 uv1*] ,[uncover-expr -> ex2* uv2**] ...) 
                (values `(,ex1 ,ex2* ...) (union uv1* (apply union uv2**)))]))

    (let-values ([(ex uv*) (uncover-expr expr)]) ex))

;   convert-closures
;   add cp; add label; add closure form

(define (convert-closures expr)
    (define (create-cp x) (unique-name `cp))
    (define (convert-expr expr)
        (match expr
            [,uv (guard (uvar? uv)) expr]
            [(quote ,imm) expr]
            [(if ,[convert-expr -> ex1] ,[convert-expr -> ex2] ,[convert-expr -> ex3]) `(if ,ex1 ,ex2 ,ex3)]
            [(begin ,[convert-expr -> ex1*] ... ,[convert-expr -> ex2]) (make-begin `(,ex1* ... ,ex2))]
            [(let ([,uv* ,[convert-expr -> ex1*]] ...) ,[convert-expr -> ex2]) `(let ([,uv* ,ex1*] ...) ,ex2)]
            [(letrec ([,uv* (lambda ,para** (free ,fuv** ,[convert-expr -> ex1*]))] ...) ,[convert-expr -> ex2])
                (let ([lb* (map unique-label uv*)]
                      [cp* (map create-cp uv*)])
                    `(letrec ([,lb* (lambda (,cp* ,para** ...)
                                            (bind-free (,cp* ,fuv** ...) ,ex1*))] ...)
                             (closures ([,uv* ,lb* ,fuv** ...] ...) ,ex2)))]
            [(,p ,[convert-expr -> ex*] ...) (guard (memq p prim*)) `(,p ,ex* ...)]
            [(,[convert-expr -> ex1] ,[convert-expr -> ex2*] ...) `(,ex1 ,ex2* ...)
                (if (uvar? ex1)
                    `(,ex1 ,ex1 ,ex2* ...)
                    (let ([tmp (unique-name `convert)])
                        `(let ([,tmp ,ex1])
                            (,tmp ,tmp ,ex2* ...))))]))
    
    (convert-expr expr))

;   optimize-known-call
;   for known calls, give the label directly instead of using procedure-code

(define (optimize-known-call expr)
    (define (opt-expr proc*)
        (lambda (expr)
            (match expr
                [,uv (guard (uvar? uv)) expr]
                [(quote ,imm) expr]
                [(lambda ,para* ,[(opt-expr proc*) -> ex]) `(lambda ,para* ,ex)]
                [(if ,[(opt-expr proc*) -> ex1] ,[(opt-expr proc*) -> ex2] ,[(opt-expr proc*) -> ex3]) `(if ,ex1 ,ex2 ,ex3)]
                [(begin ,[(opt-expr proc*) -> ex1*] ... ,[(opt-expr proc*) -> ex2]) (make-begin `(,ex1* ... ,ex2))]
                [(let ([,uv* ,[(opt-expr proc*) -> ex1*]] ...) ,[(opt-expr proc*) -> ex2]) `(let ([,uv* ,ex1*] ...) ,ex2)]
                [(letrec ([,lb* (lambda (,cp* ,para** ...)
                                        (bind-free (,cp_* ,fuv** ...) ,ex1*))] ...)
                         (closures ([,uv* ,lb_* ,fuv_** ...] ...) ,ex2))
                    (let* ([new-proc* (append proc* uv*)]
                           [new-ex1* (map (opt-expr new-proc*) ex1*)]
                           [new-ex2 ((opt-expr new-proc*) ex2)])
                        `(letrec ([,lb* (lambda (,cp* ,para** ...)
                                        (bind-free (,cp_* ,fuv** ...) ,new-ex1*))] ...)
                                 (closures ([,uv* ,lb_* ,fuv_** ...] ...) ,new-ex2)))]
                [(,p ,[(opt-expr proc*) -> ex*] ...) (guard (memq p prim*)) `(,p ,ex* ...)]
                [((lambda ,para* ,[(opt-expr proc*) -> ex1]) ,[(opt-expr proc*) -> ex2*] ...) `(let ([,para* ,ex2*] ...) ,ex1)]
                [(,ex1 ,[(opt-expr proc*) -> ex2*] ...)
                    (if (memq ex1 proc*)
                        `(,(unique-label ex1) ,ex2* ...)
                        `(,ex1 ,ex2* ...))])))

    ((opt-expr `()) expr))

;   introduce-procedure-primitives
;   1. use (procedure-ref cp x) to when you need fuvs
;   2. convert closure form to the def&setting of closures

(define (introduce-procedure-primitives expr)
    (define (kth aim ls cnt)
        (if (eq? aim (car ls))
            cnt
            (kth aim (cdr ls) (+ 1 cnt))))

    (define (makeproc uv lb fuv*)
        `[,uv (make-procedure ,lb (quote ,(length fuv*)))])
    (define (helper uv lb ls* cnt cp fuv*)
        (if (null? ls*)
            `()
            (let ([fir `(procedure-set! ,uv (quote ,cnt) ,(get (car ls*) cp fuv*))]
                  [rem (helper uv lb (cdr ls*) (+ 1 cnt) cp fuv*)])
                (cons fir rem))))
    (define (procset cp fuv*)
        (lambda (uv lb ls*) (helper uv lb ls* 0 cp fuv*)))
    
    (define (get uv cp fuv*)
        (if (memq uv fuv*)
            `(procedure-ref ,cp (quote ,(kth uv fuv* 0)))
            uv))

    (define (intro-closure cp fuv*)
        (lambda (closure)
            (match closure
                [(closures ([,uv* ,lb* ,fuv** ...] ...) ,[(intro-expr cp fuv*) -> ex])
                    (let ([makeproc* (map makeproc uv* lb* fuv**)]
                          [procset* (map (procset cp fuv*) uv* lb* fuv**)])
                        `(let ,makeproc* ,(make-begin `(,procset* ... ... ,ex))))])))
    
    (define (intro-lambda lamb)
        (match lamb
            [(lambda ,para* (bind-free (,cp ,fuv* ...) ,ex))
                `(lambda ,para* ,((intro-expr cp fuv*) ex))]))

    (define (intro-expr cp fuv*)
        (lambda (expr)
            (match expr
                [,uv (guard (uvar? uv)) (get uv cp fuv*)]
                [(quote ,imm) expr]
                [(if ,[(intro-expr cp fuv*) -> ex1] ,[(intro-expr cp fuv*) -> ex2] ,[(intro-expr cp fuv*) -> ex3])
                    `(if ,ex1 ,ex2 ,ex3)]
                [(begin ,[(intro-expr cp fuv*) -> ex1*] ... ,[(intro-expr cp fuv*) -> ex2])
                    (make-begin `(,ex1* ... ,ex2))]
                [(let ([,uv* ,[(intro-expr cp fuv*) -> ex1*]] ...) ,[(intro-expr cp fuv*) -> ex2])
                    `(let ([,uv* ,ex1*] ...) ,ex2)]
                [(letrec ([,lb* ,[intro-lambda -> ex1*]] ...) ,[(intro-closure cp fuv*) -> ex2])
                    `(letrec ([,lb* ,ex1*] ...) ,ex2)]
                [(,p ,[(intro-expr cp fuv*) -> ex*] ...) (guard (memq p prim*)) `(,p ,ex* ...)]
                [(,proc ,[(intro-expr cp fuv*) -> arg1] ,[(intro-expr cp fuv*) -> arg*] ...)
                    (if (label? proc)
                        `(,proc ,arg1 ,arg* ...)
                        `((procedure-code ,((intro-expr cp fuv*) proc)) ,arg1 ,arg* ...))])))
    ((intro-expr `() `()) expr))

;   lift-letrec
;   bring letrec to the outer layer

(define (lift-letrec expr)
    (define new-val-prim* `(+ - * car cdr cons make-vector vector-length vector-ref void make-procedure procedure-code procedure-ref))
    (define new-pr-prim* `(<= < = > >= boolean? eq? fixnum? null? pair? vector? procedure?))
    (define new-ef-prim* `(set-car! set-cdr! vector-set! procedure-set!))
    (define new-prim* (append new-val-prim* new-pr-prim* new-ef-prim*))
    (define proc* `())
    (define (lift-expr expr)
        (match expr
            [,lb (guard (label? lb)) expr]
            [,uv (guard (uvar? uv)) expr]
            [(quote ,imm) expr]
            [(if ,[lift-expr -> ex1] ,[lift-expr -> ex2] ,[lift-expr -> ex3]) `(if ,ex1 ,ex2 ,ex3)]
            [(begin ,[lift-expr -> ex1*] ... ,[lift-expr -> ex2]) (make-begin `(,ex1* ... ,ex2))]
            [(let ([,uv* ,[lift-expr -> ex1*]] ...) ,[lift-expr -> ex2]) (make-let `([,uv* ,ex1*] ...) ex2)]
            [(letrec ([,lb* (lambda ,para** ,[lift-expr -> ex1*])] ...) ,[lift-expr -> ex2])
                (begin
                    (set! proc* (append proc* (deep-copy `([,lb* (lambda ,para** ,ex1*)] ...))))
                    ex2)]
            [(,p ,[lift-expr -> ex*] ...) (guard (memq p new-prim*)) `(,p ,ex* ...)]
            [(,[lift-expr -> ex1] ,[lift-expr -> ex2*] ...) `(,ex1 ,ex2* ...)]))

    (begin
        (set! proc* `())
        (let ([ex (lift-expr expr)])
            `(letrec ,proc* ,ex))))

;   normalize-context
;   distinguish value, pred, effect
;   based on the grammer structure, make corresponding changes

(define (normalize-context program)
    (define new-val-prim* `(+ - * car cdr cons make-vector vector-length vector-ref void make-procedure procedure-code procedure-ref))
    (define new-pr-prim* `(<= < = > >= boolean? eq? fixnum? null? pair? vector? procedure?))
    (define new-ef-prim* `(set-car! set-cdr! vector-set! procedure-set!))
    (define new-prim* (append new-val-prim* new-pr-prim* new-ef-prim*))
    (define (make-nopless-begin x*)
        (let ([x* (remove `(nop) x*)])
            (if (null? x*)
            `(nop)
            (make-begin x*))))

    (define (normalize-program program)
        (match program
            [(letrec ([,lb* (lambda ,para** ,[normalize-value -> val1*])] ...) ,[normalize-value -> val2])
                `(letrec ([,lb* (lambda ,para** ,val1*)] ...) ,val2)]))
    
    (define (normalize-value value)
        (match value
            [,lb (guard (label? lb)) value]
            [,uv (guard (uvar? uv)) value]
            [(quote ,imm) value]
            [(if ,[normalize-pred -> pr] ,[normalize-value -> val1] ,[normalize-value -> val2]) `(if ,pr ,val1 ,val2)]
            [(begin ,[normalize-effect -> ef*] ... ,[normalize-value -> val]) (make-begin `(,ef* ... ,val))]
            [(let ([,uv* ,[normalize-value -> val1*]] ...) ,[normalize-value -> val2]) `(let ([,uv* ,val1*] ...) ,val2)]
            [(,vp ,[normalize-value -> val*] ...) (guard (memq vp new-val-prim*))
                `(,vp ,val* ...)]
            [(,pp ,[normalize-value -> val*] ...) (guard (memq pp new-pr-prim*))
                `(if (,pp ,val* ...) '#t '#f)]
            [(,ep ,[normalize-value -> val*] ...) (guard (memq ep new-ef-prim*))
                (make-begin `((,ep ,val* ...) (void)))]
            [(,[normalize-value -> val1] ,[normalize-value -> val2*] ...) `(,val1 ,val2* ...)]))
    
    (define (normalize-pred pred)
        (match pred
            [,lb (guard (label? lb)) `(true)]
            [,uv (guard (uvar? uv)) `(if (eq? ,uv '#f) (false) (true))]
            [(quote ,imm) (if imm `(true) `(false))]
            [(if ,[normalize-pred -> pr1] ,[normalize-pred -> pr2] ,[normalize-pred -> pr3]) `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[normalize-effect -> ef*] ... ,[normalize-pred -> pr]) (make-begin `(,ef* ... ,pr))]
            [(let ([,uv* ,[normalize-value -> val*]] ...) ,[normalize-pred -> pr]) `(let ([,uv* ,val*] ...) ,pr)]
            [(,pp ,[normalize-value -> val*] ...) (guard (memq pp new-pr-prim*))
                `(,pp ,val* ...)]
            [(,vp ,[normalize-value -> val*] ...) (guard (memq vp new-val-prim*))
                `(if (eq? (,vp ,val* ...) '#f) (false) (true))]
            [(,ep ,[normalize-value -> val*] ...) (guard (memq ep new-ef-prim*))
                (make-begin `((,ep ,val* ...) (true)))]
            [(,[normalize-value -> val1] ,[normalize-value -> val2*] ...) 
                `(if (eq? (,val1 ,val2* ...) '#f) (false) (true))]))
    
    (define (normalize-effect effect)
        (match effect
            [,lb (guard (label? lb)) `(nop)]
            [,uv (guard (uvar? uv)) `(nop)]
            [(quote ,imm) `(nop)]
            [(if ,[normalize-pred -> pr] ,[normalize-effect -> ef1] ,[normalize-effect -> ef2]) `(if ,pr ,ef1 ,ef2)]
            [(begin ,[normalize-effect -> ef1*] ... ,[normalize-effect -> ef2]) (make-begin `(,ef1* ... ,ef2))]
            [(let ([,uv* ,[normalize-value -> val*]] ...) ,[normalize-effect -> ef]) `(let ([,uv* ,val*] ...) ,ef)]
            [(,ep ,[normalize-value -> val*] ...) (guard (memq ep new-ef-prim*))
                `(,ep ,val* ...)]
            [(,pp ,[normalize-effect -> ef*] ...) (guard (memq pp new-pr-prim*))
                (make-nopless-begin ef*)]
            [(,vp ,[normalize-effect -> ef*] ...) (guard (memq vp new-val-prim*))
                (make-nopless-begin ef*)]
            [(,[normalize-value -> val1] ,[normalize-value -> val2*] ...) `(,val1 ,val2* ...)]))
    
    (normalize-program program))

;   specify representation
;   discard different data types
;   turn back to numeric calculation

(define (specify-representation program)
    (define (specify-program program)
        (match program
            [(letrec ([,lb* (lambda ,para** ,[specify-value -> val1*])] ...) ,[specify-value -> val2])
                `(letrec ([,lb* (lambda ,para** ,val1*)] ...) ,val2)]))
    
    (define (specify-value value)
        (match value
            [(quote ,imm)
                (case imm
                    [#t $true]
                    [#f $false]
                    [`() $nil]
                    [else (ash imm shift-fixnum)])]
            [(void) $void]
            [(* ,[specify-value -> val1] ,[specify-value -> val2])
                (cond
                    [(integer? val1) `(* ,(sra val1 shift-fixnum) ,val2)]
                    [(integer? val2) `(* ,val1 ,(sra val2 shift-fixnum))]
                    [else `(* (sra ,val1 ,shift-fixnum) ,val2)])]
            [(+ ,[specify-value -> val1] ,[specify-value -> val2]) `(+ ,val1 ,val2)]
            [(- ,[specify-value -> val1] ,[specify-value -> val2]) `(- ,val1 ,val2)]
            [(car ,[specify-value -> val]) `(mref ,val ,(- disp-car tag-pair))]
            [(cdr ,[specify-value -> val]) `(mref ,val ,(- disp-cdr tag-pair))]
            [(cons ,[specify-value -> val1] ,[specify-value -> val2])
                (let ([tmp (unique-name 'cons)])
					`(let ([,tmp (+ (alloc ,size-pair) ,tag-pair)])
						(begin
							(mset! ,tmp ,(- disp-car tag-pair) ,val1)
							(mset! ,tmp ,(- disp-cdr tag-pair) ,val2)
							,tmp)))]
            [(make-vector ,[specify-value -> val])
				(if (integer? val)
                    (let ([tmp (unique-name 'makev)])
                        `(let ([,tmp (+ (alloc ,(+ disp-vector-data val)) ,tag-vector)])
							(begin
								(mset! ,tmp ,(- disp-vector-length tag-vector) ,val)
								,tmp)))
                    (let ([tmp1 (unique-name 'makev)]
                          [tmp2 (unique-name 'makev)])
                        `(let ([,tmp1 ,val])
                            (let ([,tmp2 (+ (alloc (+ ,disp-vector-data ,tmp1)) ,tag-vector)])
								(begin
									(mset! ,tmp2 ,(- disp-vector-length tag-vector) ,tmp1)
									,tmp2)))))]
            [(vector-length ,[specify-value -> val])
                `(mref ,val ,(- disp-vector-length tag-vector))]
            [(vector-ref ,[specify-value -> val1] ,[specify-value -> val2])
				(if (integer? val2) 
					`(mref ,val1 ,(+ (- disp-vector-data tag-vector) val2))
					`(mref ,val1 (+ ,(- disp-vector-data tag-vector) ,val2)))]
            [(make-procedure ,[specify-value -> val1] ,[specify-value -> val2])
                (if (integer? val2)
                    (let ([tmp (unique-name 'makep)])
                        `(let ([,tmp (+ (alloc ,(+ disp-procedure-data val2)) ,tag-procedure)])
                            (begin
                                (mset! ,tmp ,(- disp-procedure-code tag-procedure) ,val1)
                                ,tmp)))
                    (let ([tmp (unique-name 'makep)])
                        `(let ([,tmp (+ (alloc (+ ,disp-procedure-data ,val2)) ,tag-vector)])
							(begin
								(mset! ,tmp ,(- disp-procedure-code tag-procedure) ,val1)
								,tmp))))]
            [(procedure-code ,[specify-value -> val])
				`(mref ,val ,(- disp-procedure-code tag-procedure))]
            [(procedure-ref ,[specify-value -> val1] ,[specify-value -> val2])
				(if (integer? val2) 
					`(mref ,val1 ,(+ (- disp-procedure-data tag-procedure) val2))
					`(mref ,val1 (+ ,(- disp-procedure-data tag-procedure) ,val2)))]
            [,uv (guard (uvar? uv)) uv]
            [,lb (guard (label? lb)) lb]
            [(if ,[specify-pred -> pr] ,[specify-value -> val1] ,[specify-value -> val2]) `(if ,pr ,val1 ,val2)]
            [(begin ,[specify-effect -> ef*] ... ,[specify-value -> val]) (make-begin `(,ef* ... ,val))]
            [(let ([,uv* ,[specify-value -> val1*]] ...) ,[specify-value -> val2]) `(let ([,uv* ,val1*] ...) ,val2)]
            [(,[specify-value -> val1] ,[specify-value -> val2*] ...) `(,val1 ,val2* ...)]))
    
    (define (specify-pred pred)
        (match pred
            [(eq? ,[specify-value -> val1] ,[specify-value -> val2]) `(= ,val1 ,val2)]
            [(boolean? ,[specify-value -> val]) `(= (logand ,val ,mask-boolean) ,tag-boolean)]
            [(fixnum? ,[specify-value -> val]) `(= (logand ,val ,mask-fixnum) ,tag-fixnum)]
            [(null? ,[specify-value -> val]) `(= ,val ,$nil)]
            [(pair? ,[specify-value -> val]) `(= (logand ,val ,mask-pair) ,tag-pair)]
            [(vector? ,[specify-value -> val]) `(= (logand ,val ,mask-vector) ,tag-vector)]
            [(procedure? ,[specify-value -> val]) `(= (logand ,val ,mask-procedure) ,tag-procedure)]
            [(,relop ,[specify-value -> val1] ,[specify-value -> val2])
                (guard (memq relop `(> < >= <= =))) `(,relop ,val1 ,val2)]
            [(true) `(true)]
            [(false) `(false)]
            [(if ,[specify-pred -> pr1] ,[specify-pred -> pr2] ,[specify-pred -> pr3]) `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[specify-effect -> ef*] ... ,[specify-pred -> pr]) (make-begin `(,ef* ... ,pr))]
            [(let ([,uv* ,[specify-value -> val*]] ...) ,[specify-pred -> pr]) `(let ([,uv* ,val*] ...) ,pr)]))
    
    (define (specify-effect effect)
        (match effect
            [(set-car! ,[specify-value -> val1] ,[specify-value -> val2]) `(mset! ,val1 ,(- disp-car tag-pair) ,val2)]
            [(set-cdr! ,[specify-value -> val1] ,[specify-value -> val2]) `(mset! ,val1 ,(- disp-cdr tag-pair) ,val2)]
            [(vector-set! ,[specify-value -> val1] ,[specify-value -> val2] ,[specify-value -> val3])
                (if (integer? val2) 
					`(mset! ,val1 ,(+ (- disp-vector-data tag-vector) val2) ,val3)
					`(mset! ,val1 (+ ,(- disp-vector-data tag-vector) ,val2) ,val3))]
            [(procedure-set! ,[specify-value -> val1] ,[specify-value -> val2] ,[specify-value -> val3])
                (if (integer? val2) 
					`(mset! ,val1 ,(+ (- disp-procedure-data tag-procedure) val2) ,val3)
					`(mset! ,val1 (+ ,(- disp-procedure-data tag-procedure) ,val2) ,val3))]
            [(nop) `(nop)]
            [(if ,[specify-pred -> pr] ,[specify-effect -> ef1] ,[specify-effect -> ef2]) `(if ,pr ,ef1 ,ef2)]
            [(begin ,[specify-effect -> ef1*] ... ,[specify-effect -> ef2]) (make-begin `(,ef1* ... ,ef2))]
            [(let ([,uv* ,[specify-value -> val*]] ...) ,[specify-effect -> ef]) `(let ([,uv* ,val*] ...) ,ef)]
            [(,[specify-value -> val1] ,[specify-value -> val2*] ...) `(,val1 ,val2* ...)]))

    (specify-program program))

;   uncover-locals
;   find uvars and add body structure
;   the 'tail' structure is for the convenience of compiler
;   from the perspective of programmers, there is no difference between 'tail' and 'value'

(define (uncover-locals program)
    (define (uncover-program program)
        (match program
            [(letrec ([,lb* (lambda ,para** ,tl1*)] ...) ,tl2)
                (let* ([local** (map uncover-tail tl1*)]
                       [bd1* `((locals ,local** ,tl1*) ...)]
                       [bd2 `(locals ,(uncover-tail tl2) ,tl2)])
                    `(letrec ([,lb* (lambda ,para** ,bd1*)] ...) ,bd2))]))
    
    (define (uncover-tail tail)
        (match tail
            [(if ,[uncover-pred -> pr] ,[uncover-tail -> tl1] ,[uncover-tail -> tl2]) (union pr tl1 tl2)]
            [(begin ,[uncover-effect -> ef*] ... ,[uncover-tail -> tl]) (union `(,ef* ... ...) tl)]
            [(let ([,uv* ,[uncover-value -> val*]] ...) ,[uncover-tail -> tl]) (union uv* `(,val* ... ...) tl)]
            [(,binop ,[uncover-value -> val1] ,[uncover-value -> val2])
                (guard (memq binop `(+ - * logand logor sra mref))) (union val1 val2)]
            [(alloc ,[uncover-value -> val]) val]
            [(,[uncover-value -> val1] ,[uncover-value -> val2*] ...) (union val1 `(,val2* ... ...))]
            [,tr `()]))
    
    (define (uncover-pred pred)
        (match pred
            [(if ,[uncover-pred -> pr1] ,[uncover-pred -> pr2] ,[uncover-pred -> pr3]) (union pr1 pr2 pr3)]
            [(begin ,[uncover-effect -> ef*] ... ,[uncover-pred -> pr]) (union `(,ef* ... ...) pr)]
            [(let ([,uv* ,[uncover-value -> val*]] ...) ,[uncover-pred -> pr]) (union uv* `(,val* ... ...) pr)]
            [(,relop ,[uncover-value -> val1] ,[uncover-value -> val2]) (union val1 val2)]
            [(true) `()]
            [(false) `()]))
    
    (define (uncover-effect effect)
        (match effect
            [(nop) `()]
            [(if ,[uncover-pred -> pr] ,[uncover-effect -> ef1] ,[uncover-effect -> ef2]) (union pr ef1 ef2)]
            [(begin ,[uncover-effect -> ef1*] ... ,[uncover-effect -> ef2]) (union `(,ef1* ... ...) ef2)]
            [(let ([,uv* ,[uncover-value -> val*]] ...) ,[uncover-effect -> ef]) (union uv* `(,val* ... ...) ef)]
            [(mset! ,[uncover-value -> val1] ,[uncover-value -> val2] ,[uncover-value -> val3]) (union val1 val2 val3)]
            [(,[uncover-value -> val1] ,[uncover-value -> val2*] ...) (union val1 `(,val2* ... ...))]))
    
    (define (uncover-value value)
        (match value
            [(if ,[uncover-pred -> pr] ,[uncover-value -> val1] ,[uncover-value -> val2]) (union pr val1 val2)]
            [(begin ,[uncover-effect -> ef*] ... ,[uncover-value -> val]) (union `(,ef* ... ...) val)]
            [(let ([,uv* ,[uncover-value -> val1*]] ...) ,[uncover-value -> val2]) (union uv* `(,val1* ... ...) val2)]
            [(,binop ,[uncover-value -> val1] ,[uncover-value -> val2])
                (guard (memq binop `(+ - * logand logor sra mref))) (union val1 val2)]
            [(alloc ,[uncover-value -> val]) val]
            [(,[uncover-value -> val1] ,[uncover-value -> val2*] ...) (union val1 `(,val2* ... ...))]
            [,tr `()]))

    (uncover-program program))

;   remove-let
;   let -> set!

(define (remove-let program)
    (define (remove-program program)
        (match program
            [(letrec ([,lb* (lambda ,para** ,[remove-body -> bd1*])] ...) ,[remove-body -> bd2])
                `(letrec ([,lb* (lambda ,para** ,bd1*)] ...) ,bd2)]))

    (define (remove-body body)
        (match body
            [(locals ,uv* ,[remove-tail -> tl])
                `(locals ,uv* ,tl)]))
    
    (define (remove-tail tail)
        (match tail
            [(if ,[remove-pred -> pr] ,[remove-tail -> tl1] ,[remove-tail -> tl2]) `(if ,pr ,tl1 ,tl2)]
            [(begin ,[remove-effect -> ef*] ... ,[remove-tail -> tl]) (make-begin `(,ef* ... ,tl))]
            [(let ([,uv* ,[remove-value -> val*]] ...) ,[remove-tail -> tl]) (make-begin `((set! ,uv* ,val*) ... ,tl))]
            [(,binop ,[remove-value -> val1] ,[remove-value -> val2])
                (guard (memq binop `(+ - * logand logor sra mref))) `(,binop ,val1 ,val2)]
            [(alloc ,[remove-value -> val]) `(alloc ,val)]
            [(,[remove-value -> val1] ,[remove-value -> val2*] ...) `(,val1 ,val2* ...)]
            [,tr tr]))
    
    (define (remove-pred pred)
        (match pred
            [(if ,[remove-pred -> pr1] ,[remove-pred -> pr2] ,[remove-pred -> pr3]) `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[remove-effect -> ef*] ... ,[remove-pred -> pr]) (make-begin `(,ef* ... ,pr))]
            [(let ([,uv* ,[remove-value -> val*]] ...) ,[remove-pred -> pr]) (make-begin `((set! ,uv* ,val*) ... ,pr))]
            [(,relop ,[remove-value -> val1] ,[remove-value -> val2]) `(,relop ,val1 ,val2)]
            [(true) `(true)]
            [(false) `(false)]))
    
    (define (remove-effect effect)
        (match effect
            [(nop) `(nop)]
            [(if ,[remove-pred -> pr] ,[remove-effect -> ef1] ,[remove-effect -> ef2]) `(if ,pr ,ef1 ,ef2)]
            [(begin ,[remove-effect -> ef1*] ... ,[remove-effect -> ef2]) (make-begin `(,ef1* ... ,ef2))]
            [(let ([,uv* ,[remove-value -> val*]] ...) ,[remove-effect -> ef]) (make-begin `((set! ,uv* ,val*) ... ,ef))]
            [(mset! ,[remove-value -> val1] ,[remove-value -> val2] ,[remove-value -> val3]) `(mset! ,val1 ,val2 ,val3)]
            [(,[remove-value -> val1] ,[remove-value -> val2*] ...) `(,val1 ,val2* ...)]))
    
    (define (remove-value value)
        (match value
            [(if ,[remove-pred -> pr] ,[remove-value -> val1] ,[remove-value -> val2]) `(if ,pr ,val1 ,val2)]
            [(begin ,[remove-effect -> ef*] ... ,[remove-value -> val]) (make-begin `(,ef* ... ,val))]
            [(let ([,uv* ,[remove-value -> val*]] ...) ,[remove-value -> val]) (make-begin `((set! ,uv* ,val*) ... ,val))]
            [(,binop ,[remove-value -> val1] ,[remove-value -> val2])
                (guard (memq binop `(+ - * logand logor sra mref))) `(,binop ,val1 ,val2)]
            [(alloc ,[remove-value -> val]) `(alloc ,val)]
            [(,[remove-value -> val1] ,[remove-value -> val2*] ...) `(,val1 ,val2* ...)]
            [,tr tr]))

    (remove-program program))

;   verify-uil
;   do nothing
;   actually, we should verify the correctness of uil

(define (verify-uil x) x) 

;   remove-complect-opera*
;   using set!, make all reference of value -> triv, also flatten value itself

(define (remove-complex-opera* program)
    (define (remove-program program)
        (match program
            [(letrec ([,lb* (lambda ,para** ,[remove-body -> bd1*])] ...) ,[remove-body -> bd2])
                `(letrec ([,lb* (lambda ,para** ,bd1*)] ...) ,bd2)]))

    (define (remove-body body)
        (match body
            [(locals ,uv* ,[remove-tail -> tl new-uv*])
                `(locals ,(append uv* new-uv*) ,tl)]))
    
    (define (remove-tail tail)
        (match tail
            [(if ,[remove-pred -> pr uv*-pr] ,[remove-tail -> tl1 uv*-tl1] ,[remove-tail -> tl2 uv*-tl2])
                (values `(if ,pr ,tl1 ,tl2) (append uv*-pr uv*-tl1 uv*-tl2))]
            [(begin ,[remove-effect -> ef* uv*-ef*] ... ,[remove-tail -> tl uv*-tl])
                (values (make-begin `(,ef* ... ,tl)) (apply append uv*-tl uv*-ef*))]
            [(,binop ,val1 ,val2) (guard (memq binop `(+ - * logand logor sra)))
                (let-values ([(set* tr* uv*) (muti-remove-helper (list val1 val2))])
                    (values (make-begin `(,set* ... (,binop ,tr* ...))) uv*))]
            [(alloc ,val)
                (let-values ([(set* tr* uv*) (muti-remove-helper (list val))])
                    (values (make-begin `(,set* ... (alloc ,tr* ...))) uv*))]
            [(mref ,val1 ,val2)
                (let-values ([(set* tr* uv*) (muti-remove-helper (list val1 val2))])
                    (values (make-begin `(,set* ... (mref ,tr* ...))) uv*))]
            [(,val1 ,val2* ...)
                (let-values ([(set* call uv*) (muti-remove-helper (cons val1 val2*))])
                    (values (make-begin `(,set* ... ,call)) uv*))]
            [,tr (values tr `())]))
    
    (define (remove-pred pred)
        (match pred
            [(true) (values `(true) `())]
            [(false) (values `(false) `())]
            [(if ,[remove-pred -> pr1 uv*-pr1] ,[remove-pred -> pr2 uv*-pr2] ,[remove-pred -> pr3 uv*-pr3])
                (values `(if ,pr1 ,pr2 ,pr3) (append uv*-pr1 uv*-pr2 uv*-pr3))]
            [(begin ,[remove-effect -> ef* uv*-ef*] ... ,[remove-pred -> pr uv*-pr])
                (values (make-begin `(,ef* ... ,pr)) (apply append uv*-pr uv*-ef*))]
            [(,relop ,val1 ,val2)
                (let-values ([(set* tr* uv*) (muti-remove-helper (list val1 val2))])
                    (values (make-begin `(,set* ... (,relop ,tr* ...))) uv*))]))
    
    (define (remove-effect effect)
        (match effect
            [(nop) (values `(nop) `())]
            [(begin ,[remove-effect -> ef1* uv*-ef1*] ... ,[remove-effect -> ef2 uv*-ef2])
                (values (make-begin `(,ef1* ... ,ef2)) (apply append uv*-ef2 uv*-ef1*))]
            [(if ,[remove-pred -> pr uv*-pr] ,[remove-effect -> ef1 uv*-ef1] ,[remove-effect -> ef2 uv*-ef2])
                (values `(if ,pr ,ef1 ,ef2) (append uv*-pr uv*-ef1 uv*-ef2))]
            [(set! ,uv ,[remove-value -> val uv*-val])
                (values `(set! ,uv ,val) uv*-val)]
            [(mset! ,val1 ,val2 ,val3)
                (let-values ([(set* tr* uv*) (muti-remove-helper (list val1 val2 val3))])
                    (values (make-begin `(,set* ... (mset! ,tr* ...))) uv*))]
            [(,val1 ,val2* ...)
                (let-values ([(set* call uv*) (muti-remove-helper (cons val1 val2*))])
                    (values (make-begin `(,set* ... ,call)) uv*))]))
    
    (define (remove-value value)
        (match value
            [(if ,[remove-pred -> pr uv*-pr] ,[remove-value -> val1 uv*-val1] ,[remove-value -> val2 uv*-val2])
                (values `(if ,pr ,val1 ,val2) (append uv*-pr uv*-val1 uv*-val2))]
            [(begin ,[remove-effect -> ef* uv*-ef*] ... ,[remove-value -> val uv*-val])
                (values (make-begin `(,ef* ... ,val)) (apply append uv*-val uv*-ef*))]
            [(,binop ,val1 ,val2) (guard (memq binop `(+ - * logand logor sra)))
                (let-values ([(set* tr* uv*) (muti-remove-helper (list val1 val2))])
                    (values (make-begin `(,set* ... (,binop ,tr* ...))) uv*))]
            [(alloc ,val)
                (let-values ([(set* tr* uv*) (muti-remove-helper (list val))])
                    (values (make-begin `(,set* ... (alloc ,tr* ...))) uv*))]
            [(mref ,val1 ,val2)
                (let-values ([(set* tr* uv*) (muti-remove-helper (list val1 val2))])
                    (values (make-begin `(,set* ... (mref ,tr* ...))) uv*))]
            [(,val1 ,val2* ...)
                (let-values ([(set* tr* uv*) (muti-remove-helper (cons val1 val2*))])
                    (values (make-begin `(,set* ... ,tr*)) uv*))]
            [,tr (values tr `())]))

    (define (muti-remove-helper value*)
        (if (null? value*)
            (values `() `() `())
            (let-values ([(set* call uv*) (muti-remove-helper (cdr value*))])
                (let ([val (car value*)])
                    (if (list? val)
                        (let-values ([(new-val uv*-val) (remove-value val)])
                            (let ([uv (unique-name 'rco)])
                                (values (cons `(set! ,uv ,new-val) set*)
                                        (cons uv call)
                                        (cons uv (append uv*-val uv*)))))
                        (values set* (cons val call) uv*))))))

    (remove-program program))

;   flatten-set!
;   discard 'value' structure, turn it into multiple set! 
;   (set! uvar value) -> (set! uvar triv) / binop / proc / mref / alloc

(define (flatten-set! program)
    (define (flat-program program)
        (match program
            [(letrec ([,lb* (lambda ,para** ,[flat-body -> bd1*])] ...) ,[flat-body -> bd2])
                `(letrec ([,lb* (lambda ,para** ,bd1*)] ...) ,bd2)]))

    (define (flat-body body)
        (match body
            [(locals ,uv* ,[flat-tail -> tl])
                `(locals ,uv* ,tl)]))
    
    (define (flat-tail tail)
        (match tail
            [(if ,[flat-pred -> pr] ,[flat-tail -> tl1] ,[flat-tail -> tl2]) `(if ,pr ,tl1 ,tl2)]
            [(begin ,[flat-effect -> ef*] ... ,[flat-tail -> tl]) (make-begin `(,ef* ... ,tl))]
            [(,binop ,tr1 ,tr2) (guard (memq binop `(+ - * logand logor sra))) tail]
            [(alloc ,tr) tail]
            [(mref ,tr1 ,tr2) tail]
            [(,tr1 ,tr2* ...) tail]
            [,tr tail]))
    
    (define (flat-pred pred)
        (match pred
            [(true) pred]
            [(false) pred]
            [(if ,[flat-pred -> pr1] ,[flat-pred -> pr2] ,[flat-pred -> pr3])
                `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[flat-effect -> ef*] ... ,[flat-pred -> pr])
                (make-begin `(,ef* ... ,pr))]
            [(,relop ,tr1 ,tr2) pred]))
    
    (define (flat-effect effect)
        (match effect
            [(nop) effect]
            [(begin ,[flat-effect -> ef1*] ... ,[flat-effect -> ef2])
                (make-begin `(,ef1* ... ,ef2))]
            [(if ,[flat-pred -> pr] ,[flat-effect -> ef1] ,[flat-effect -> ef2])
                `(if ,pr ,ef1 ,ef2)]
            [(set! ,uv ,val) (flat-value val uv)]
            [(mset! ,tr1 ,tr2 ,tr3) effect]
            [(,tr1 ,tr2* ...) effect]))
    
    (define (flat-value value uvar)
        (match value
            [(if ,[flat-pred -> pr] ,val1 ,val2)
                `(if ,pr ,(flat-value val1 uvar) ,(flat-value val2 uvar))]
            [(begin ,[flat-effect -> ef*] ... ,val)
                (make-begin `(,ef* ... ,(flat-value val uvar)))]
            [(,binop ,tr1 ,tr2) (guard (memq binop `(+ - * logand logor sra)))
                `(set! ,uvar (,binop ,tr1 ,tr2))]
            [(alloc ,tr) `(set! ,uvar (alloc ,tr))]
            [(mref ,tr1 ,tr2) `(set! ,uvar (mref ,tr1 ,tr2))]
            [(,tr1 ,tr2* ...) `(set! ,uvar (,tr1 ,tr2* ...))]  
            [,tr `(set! ,uvar ,tr)]))

    (flat-program program))

;   impose-calling-conventions
;   add set! for caller and callee, expose (tr, loc* ...)
;   add return-point form

(define (impose-calling-conventions program)
    (define (impose-program program)
        (match program
            [(letrec ([,lb* (lambda ,para** ,bd1*)] ...) ,bd2)
                (let* ([new-bd1* (map impose-body bd1* para**)]
                       [new-bd2 (impose-body bd2 `())])
                    `(letrec ([,lb* (lambda () ,new-bd1*)] ...) ,new-bd2))]))

    ; dangerous variable
    (define nfv** `())
    
    (define (impose-body body parameter*)
        (match body
            [(locals ,uv* ,tl)
                (begin 
                    (set! nfv** `())
                    (let* ([uv-rp (unique-name `uv-rp)]
                           [loc* (para->loc parameter* parameter-registers 0)]
                           [set* `((set! ,parameter* ,loc*) ...)]
                           [new-tl (make-begin `((set! ,uv-rp ,return-address-register)
                                                 ,set* ...
                                                 ,(impose-tail tl uv-rp)))])
                        (let ([cp-nfv** (deep-copy nfv**)])
                            `(locals (,uv* ... ,uv-rp ,parameter* ... ,cp-nfv** ... ...)
                                (new-frames ,cp-nfv** ,new-tl)))))]))
    
    (define (impose-tail tail uv-rp)
        (match tail
            [(if ,[impose-pred -> pr] ,tl1 ,tl2)
                `(if ,pr ,(impose-tail tl1 uv-rp) ,(impose-tail tl2 uv-rp))]
            [(begin ,[impose-effect -> ef*] ... ,tl)
                (make-begin `(,ef* ... ,(impose-tail tl uv-rp)))]
            [(,binop ,tr1 ,tr2) (guard (memq binop `(+ - * logand logor sra)))
                (make-begin `((set! ,return-value-register (,binop ,tr1 ,tr2))
                              (,uv-rp ,allocation-pointer-register ,frame-pointer-register ,return-value-register)))]
            [(alloc ,tr)
                (make-begin `((set! ,return-value-register (alloc ,tr))
                              (,uv-rp ,allocation-pointer-register ,frame-pointer-register ,return-value-register)))]
            [(mref ,tr1 ,tr2) 
                (make-begin `((set! ,return-value-register (mref ,tr1 ,tr2))
                              (,uv-rp ,allocation-pointer-register ,frame-pointer-register ,return-value-register)))]
            [(,tr1 ,tr2* ...) 
                (let* ([loc* (para->loc tr2* parameter-registers 0)]
                       [set* `((set! ,loc* ,tr2*) ...)]
                       [new-set* (fv-first set*)]
                       [new-tl (make-begin `(,new-set* ...
                                             (set! ,return-address-register ,uv-rp)
                                             (,tr1 ,allocation-pointer-register ,frame-pointer-register ,return-address-register ,loc* ...)))])
                    new-tl)]
            [,tr 
                (make-begin `((set! ,return-value-register ,tr)
                              (,uv-rp ,allocation-pointer-register ,frame-pointer-register ,return-value-register)))]))
    
    (define (impose-pred pred)
        (match pred
            [(true) pred]
            [(false) pred]
            [(if ,[impose-pred -> pr1] ,[impose-pred -> pr2] ,[impose-pred -> pr3]) `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[impose-effect -> ef*] ... ,[impose-pred -> pr]) (make-begin `(,ef* ... ,pr))]
            [(,relop ,tr1 ,tr2) pred]))
    
    (define (impose-effect effect)
        (match effect
            [(nop) effect]
            [(begin ,[impose-effect -> ef1*] ... ,[impose-effect -> ef2])
                (make-begin `(,ef1* ... ,ef2))]
            [(if ,[impose-pred -> pr] ,[impose-effect -> ef1] ,[impose-effect -> ef2])
                `(if ,pr ,ef1 ,ef2)]
            [(set! ,uv (,binop ,tr1 ,tr2)) (guard (memq binop `(+ - * logand logor sra))) effect]
            [(set! ,uv (alloc ,tr)) effect]
            [(set! ,uv (mref ,tr1 ,tr2)) effect]
            [(set! ,uv (,tr1 ,tr2* ...))
                (make-begin (list (non-tail-call tr1 tr2*) `(set! ,uv ,return-value-register)))]
            [(set! ,uv ,tr) effect]
            [(mset! ,tr1 ,tr2 ,tr3) effect]
            [(,tr1 ,tr2* ...) (non-tail-call tr1 tr2*)]))

    (define (non-tail-call func para*) (match func [,x ; in order to use ...
        (let* ([rp-label (unique-label `return-label)]
               [loc* (non-tail-para->loc para* parameter-registers)]
               [nfv* (difference loc* registers)]
               [set* `((set! ,loc* ,para*) ...)]
               [new-set* (fv-first set*)]
               [call (make-begin `(,new-set* ...
                                   (set! ,return-address-register ,rp-label)
                                   (,func ,allocation-pointer-register ,frame-pointer-register ,return-address-register ,loc* ...)))])
            (set! nfv** (cons (deep-copy nfv*) nfv**))
            `(return-point ,rp-label ,call))]))

    (define (non-tail-para->loc para* reg*)
        (if (null? para*)
            `()
            (if (null? reg*)
                (cons (unique-name `uv-nfv) (non-tail-para->loc (cdr para*) reg*))
                (cons (car reg*) (non-tail-para->loc (cdr para*) (cdr reg*))))))
    
    (define (para->loc para* reg* cnt)
        (if (null? para*)
            `()
            (if (null? reg*)
                (cons (index->frame-var cnt) (para->loc (cdr para*) reg* (+ 1 cnt)))
                (cons (car reg*) (para->loc (cdr para*) (cdr reg*) cnt)))))
    
    (define (fv-first set*)
        (let* ([n (length parameter-registers)]
               [ls1 (get1 set* 0 n)]
               [ls2 (get2 set* 0 n)])
            (append ls2 ls1)))
    (define (get1 ls cur tot)
        (if (or (null? ls) (= cur tot))
            `()
            (cons (car ls) (get1 (cdr ls) (+ 1 cur) tot))))
    (define (get2 ls cur tot)
        (if (or (null? ls) (= cur tot))
            ls
            (get2 (cdr ls) (+ 1 cur) tot)))
    
    (impose-program program))

;   expose-allocation-pointer
;   discard alloc form

(define (expose-allocation-pointer program)
    (define (expose-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[expose-body -> bd1*])] ...) ,[expose-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))
    
    (define (expose-body body)
        (match body
            [(locals ,local* (new-frames ,nfv** ,[expose-tail -> tl]))
                `(locals ,local* (new-frames ,nfv** ,tl))]))

    (define (expose-tail tail)
        (match tail
            [(if ,[expose-pred -> pr] ,[expose-tail -> tl1] ,[expose-tail -> tl2])
                `(if ,pr ,tl1 ,tl2)]
            [(begin ,[expose-effect -> ef*] ... ,[expose-tail -> tl])
                (make-begin `(,ef* ... ,tl))]
            [(,tr ,loc* ...) tail]))

    (define (expose-pred pred)
        (match pred
            [(true) pred]
            [(false) pred]
            [(if ,[expose-pred -> pr1] ,[expose-pred -> pr2] ,[expose-pred -> pr3]) `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[expose-effect -> ef*] ... ,[expose-pred -> pr]) (make-begin `(,ef* ... ,pr))]
            [(,relop ,tr1 ,tr2) pred]))
                
    (define (expose-effect effect)
        (match effect
            [(nop) effect]
            [(begin ,[expose-effect -> ef1*] ... ,[expose-effect -> ef2]) (make-begin `(,ef1* ... ,ef2))]
            [(if ,[expose-pred -> pr] ,[expose-effect -> ef1] ,[expose-effect -> ef2]) `(if ,pr ,ef1 ,ef2)]
            [(set! ,uv (,binop ,tr1 ,tr2)) (guard (memq binop `(+ - * logand logor sra))) effect]
            [(set! ,uv (alloc ,tr))
                (make-begin `((set! ,uv ,allocation-pointer-register)
                              (set! ,allocation-pointer-register (+ ,allocation-pointer-register ,tr))))]
            [(set! ,uv (mref ,tr1 ,tr2)) effect]
            [(set! ,uv ,tr) effect]
            [(mset! ,tr1 ,tr2 ,tr3) effect]
            [(return-point ,lb ,[expose-tail -> tl]) `(return-point ,lb ,tl)]
            [(,tr1 ,tr2* ...) effect]))

    (expose-program program))

;   uncover-frame-conflict
;   add frame-conflict-graph for each body, find call-live-list

(define (uncover-frame-conflict program)
    (define (uncover-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[uncover-body -> bd1*])] ...) ,[uncover-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    ; dangerous variable
    ; deep-copy before used
    (define fcg `())
    (define clv* `())
    (define (uncover-body body)
        (match body
            [(locals ,local* (new-frames ,nfv** ,tl))
                (begin
                    (set! fcg `((,local*) ...))
                    (set! clv* `())
                    (uncover-tail tl)
                    (let* ([cp-clv* (deep-copy clv*)]
                           [sp* (filter2 cp-clv*)])
                        `(locals ,(difference local* sp*)
                            (new-frames ,nfv**
                                (spills ,sp*
                                    (frame-conflict ,(deep-copy fcg)
                                        (call-live ,cp-clv* ,tl)))))))]))

    (define (try-to-add x live-set)
        (if (or (frame-var? x) (uvar? x))
            (set-cons x live-set)
            live-set))
    (define (try-to-delete x live-set)
        (if (or (frame-var? x) (uvar? x))
            (difference live-set `(,x))
            live-set))
    (define (filter ls)
        (if (null? ls)
            `()
            (try-to-add (car ls) (filter (cdr ls)))))
    (define (filter2 ls)
        (if (null? ls)
            `()
            (if (uvar? (car ls))
                (cons (car ls) (filter2 (cdr ls)))
                (filter2 (cdr ls)))))
    
    (define (add-conflict x live-set)
        (if (null? live-set)
            `()
            (begin 
                (let ([y (car live-set)])
                    (cond
                        [(and (uvar? x)(frame-var? y))
                            (let ([entry (assq x fcg)])
                                (set-cdr! entry (set-cons y (cdr entry))))]
                        [(and (uvar? y)(frame-var? x))
                            (let ([entry (assq y fcg)])
                                (set-cdr! entry (set-cons x (cdr entry))))]
                        [(and (uvar? y)(uvar? x))
                            (let ([entry-x (assq x fcg)]
                                  [entry-y (assq y fcg)])
                                (set-cdr! entry-x (set-cons y (cdr entry-x)))
                                (set-cdr! entry-y (set-cons x (cdr entry-y))))]
                        [else `()]))
                (add-conflict x (cdr live-set)))))
    
    ; (effetc* live-set) -> (ls)
    (define (uncover-effect* effect* live-set)
        (if (null? effect*)
            live-set
            (let ([ls (uncover-effect* (cdr effect*) live-set)])
                (uncover-effect (car effect*) ls))))

    ; (tail) -> (ls)
    (define (uncover-tail tail)
        (match tail
            [(if ,pr ,[uncover-tail -> ls-tl1] ,[uncover-tail -> ls-tl2])
                (uncover-pred pr (union ls-tl1 ls-tl2))]
            [(begin ,ef* ... ,[uncover-tail -> ls-tl])
                (uncover-effect* ef* ls-tl)]
            [(,tr ,loc* ...)
                (try-to-add tr (filter loc*))]))

    ; (pred live-set) -> (ls)
    (define (uncover-pred pred live-set)
        (match pred
            [(true) live-set]
            [(false) live-set]
            [(if ,pr1 ,pr2 ,pr3)
                (let ([ls-pr2 (uncover-pred pr2 live-set)]
                      [ls-pr3 (uncover-pred pr3 live-set)])
                    (uncover-pred pr1 (union ls-pr2 ls-pr3)))]
            [(begin ,ef* ... ,pr)
                (let ([ls-pr (uncover-pred pr live-set)])
                    (uncover-effect* ef* ls-pr))]
            [(,relop ,tr1 ,tr2)
                (try-to-add tr1 (try-to-add tr2 live-set))]))
    
    ; (effect live-set) -> (ls)
    (define (uncover-effect effect live-set)
        (match effect
            [(nop) live-set]
            [(begin ,ef1* ... ,ef2)
                (let ([ls-ef2 (uncover-effect ef2 live-set)])
                    (uncover-effect* ef1* ls-ef2))]
            [(if ,pr ,ef1 ,ef2)
                (let ([ls-ef1 (uncover-effect ef1 live-set)]
                      [ls-ef2 (uncover-effect ef2 live-set)])
                    (uncover-pred pr (union ls-ef1 ls-ef2)))]
            [(set! ,v (,binop ,tr1 ,tr2)) (guard (memq binop `(+ - * logand logor sra mref)))
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (frame-var? v) (uvar? v)) (add-conflict v ls) `())
                        (try-to-add tr1 (try-to-add tr2 ls))))]
            [(set! ,v ,tr)
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (frame-var? v) (uvar? v)) (add-conflict v (difference ls `(,tr))) `())
                        (try-to-add tr ls)))]
            [(mset! ,tr1 ,tr2 ,tr3) (try-to-add tr1 (try-to-add tr2 (try-to-add tr3 live-set)))]
            [(return-point ,lb ,tl)
                (begin
                    (set! clv* (union clv* (deep-copy live-set)))
                    (let ([ls (uncover-tail tl)])
                        (union live-set ls)))]))
    
    (uncover-program program))

;   pre-assign-frame
;   assign frame location for call-live uvars

(define (pre-assign-frame program)
    (define (assign-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[assign-body -> bd1*])] ...) ,[assign-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (assign-body body)
        (match body
            [(locals ,local*
                (new-frames ,nfv**
                    (spills ,sp*
                        (frame-conflict ,fcg 
                            (call-live ,clv* ,tl)))))
                (let ([as (assign fcg sp*)])
                    `(locals ,local*
                        (new-frames ,nfv**
                            (locate ,as
                                (frame-conflict ,fcg
                                    (call-live ,clv* ,tl))))))]
            [(locate ,as ,tl)
                `(locate ,as ,tl)]))

    (define (find-first-available ctr*)
        (let while ([i 0])
            (let ([fv (index->frame-var i)])
                (if (memq fv ctr*)
                    (while (+ i 1))
                    fv))))
    (define (filter assignment)
        (lambda (x)
            (cond
                [(frame-var? x) x]
                [(and (uvar? x) (assq x assignment)) (cadr (assq x assignment))]
                [else `invalid])))

    ; (conflict-graph spill*) -> (as)
    (define (assign conflict-graph spill*) 
        (if (null? spill*)
            `()
            (let ([node (car spill*)])
                (let* ([as (assign conflict-graph (cdr spill*))]
                       [entry (assq node conflict-graph)]
                       [ctr* (map (filter as) (cdr entry))]
                       [loc (find-first-available ctr*)])
                    (cons (list node loc) as)))))

    (assign-program program))

;   assign-new-frame
;   set frame size & assign frame location for uv-nfv.x

(define (assign-new-frame program)
    (define (assign-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[assign-body -> bd1*])] ...) ,[assign-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    ; frame size
    (define n 0)
    (define (assign-body body)
        (match body
            [(locals ,local*
                (new-frames ,nfv**
                    (locate ,as
                        (frame-conflict ,fcg
                            (call-live ,clv* ,tl)))))
                (begin
                    (set! n (find-max clv* as))
                    (let* ([new-tl (assign-tail tl)]
                           [new-as (assign nfv**)]
                           [new-local* (difference local* `(,nfv** ... ...))])
                        `(locals ,new-local*
                            (ulocals ()
                                (locate ,(append as new-as)
                                    (frame-conflict ,fcg ,new-tl))))))]))
    
    (define (assign nfv**)
        (if (null? nfv**)
            `()
            (append (assign-helper (car nfv**) 0) (assign (cdr nfv**)))))
    (define (assign-helper nfv* cnt)
        (if (null? nfv*)
            `()
            (cons (list (car nfv*) (index->frame-var (+ (+ n cnt) 1)))
                  (assign-helper (cdr nfv*) (+ cnt 1)))))
    
    (define (max a b) (if (> a b) a b))
    (define (find-max call-live* assignment)
        (if (null? call-live*)
            0
            (let ([var (car call-live*)]
                  [res (find-max (cdr call-live*) assignment)])
                (if (frame-var? var)
                    (max (frame-var->index var) res)
                    (max (frame-var->index (cadr (assq var assignment))) res)))))
    
    (define (assign-tail tail)
        (match tail
            [(if ,[assign-tail -> pr] ,[assign-tail -> tl1] ,[assign-tail -> tl2]) `(if ,pr ,tl1 ,tl2)]
            [(begin ,[assign-effect -> ef*] ... ,[assign-tail -> tl]) (make-begin `(,ef* ... ,tl)) ]
            [(,tr ,loc* ...) `(,tr ,loc* ...)]))
    
    (define (assign-pred pred)
        (match pred
            [(true) `(true)]
            [(false) `(false)]
            [(if ,[assign-pred -> pr1] ,[assign-pred -> pr2] ,[assign-pred -> pr3]) `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[assign-effect -> ef*] ... ,[assign-pred -> pr]) (make-begin `(,ef* ... ,pr))]
            [(,relop ,tr1 ,tr2) `(,relop ,tr1 ,tr2)]))

    (define (assign-effect effect)
        (match effect
            [(nop) `(nop)]
            [(begin ,[assign-effect -> ef1*] ... ,[assign-effect -> ef2]) (make-begin `(,ef1* ... ,ef2))]
            [(if ,[assign-pred -> pr] ,[assign-effect -> ef1] ,[assign-effect -> ef2]) `(if ,pr ,ef1 ,ef2)]
            [(set! ,v (mref ,tr1 ,tr2)) `(set! ,v (mref ,tr1 ,tr2))]
            [(set! ,v (,binop ,tr1 ,tr2)) `(set! ,v (,binop ,tr1 ,tr2))]
            [(set! ,v ,tr) `(set! ,v ,tr)]
            [(mset! ,tr1 ,tr2 ,tr3) `(mset! ,tr1 ,tr2 ,tr3)]
            [(return-point ,lb ,tl)
                (make-begin
					`((set! ,frame-pointer-register (+ ,frame-pointer-register ,(ash (+ 1 n) align-shift)))
					  (return-point ,lb ,tl)
					  (set! ,frame-pointer-register (- ,frame-pointer-register ,(ash (+ 1 n) align-shift)))))]))
    
    (assign-program program))

;   finalize-frame-locations
;   replace the located uvars with locs, r.8 -> fv10, locate form remains

(define (finalize-frame-locations program)
    (define (finalize-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[finalize-body -> bd1*])] ...) ,[finalize-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (finalize-body body)
        (match body
            [(locals ,local*
                (ulocals ,ulocal*
                    (locate ,as
                        (frame-conflict ,fcg ,tl))))
                (let ([new-tl ((makefunc-tail as) tl)])
                    `(locals ,local*
                        (ulocals ,ulocal*
                            (locate ,as
                                (frame-conflict ,fcg ,new-tl)))))]
            [(locate ,as ,tl)
                `(locate ,as ,tl)]))

    (define (makefunc-tail env)
        (lambda (tail) 
            (match tail
                [(if ,[(makefunc-pred env) -> pr] ,[(makefunc-tail env) -> tl1] ,[(makefunc-tail env) -> tl2])
                    `(if ,pr ,tl1 ,tl2)]
                [(begin ,[(makefunc-effect env) -> ef*] ... ,[(makefunc-tail env) -> tl])
                    `(begin ,ef* ... ,tl)]
                [(,tr ,loc* ...) (map (f env) (cons tr loc*))])))

    (define (makefunc-pred env)
        (lambda (pred) 
            (match pred
                [(true) `(true)]
                [(false) `(false)]
                [(if ,[(makefunc-pred env) -> pr1] ,[(makefunc-pred env) -> pr2] ,[(makefunc-pred env) -> pr3])
                    `(if ,pr1 ,pr2 ,pr3)]
                [(begin ,[(makefunc-effect env) -> ef*] ... ,[(makefunc-pred env) -> pr])
                    `(begin ,ef* ... ,pr)]
                [(,relop ,tr1 ,tr2)
                    `(,relop ,((f env) tr1) ,((f env) tr2))])))

    (define (makefunc-effect env)
        (lambda (effect) 
            (match effect
                [(nop) `(nop)]
                [(begin ,[(makefunc-effect env) -> ef1*] ... ,[(makefunc-effect env) -> ef2])
                    `(begin ,ef1* ... ,ef2)]
                [(if ,[(makefunc-pred env) -> pr] ,[(makefunc-effect env) -> ef1] ,[(makefunc-effect env) -> ef2])
                    `(if ,pr ,ef1 ,ef2)]
                [(set! ,v (,binop ,tr1 ,tr2)) (guard (memq binop `(+ - * logand logor sra mref)))
                    `(set! ,((f env) v) (,binop ,((f env) tr1) ,((f env) tr2)))]
                [(set! ,v ,tr)
                    (if (eq? ((f env) v) ((f env) tr))
                        `(nop)
                        `(set! ,((f env) v) ,((f env) tr)))]
                [(mset! ,tr1 ,tr2 ,tr3)
                    `(mset! ,((f env) tr1) ,((f env) tr2) ,((f env) tr3))]
                [(return-point ,lb ,[(makefunc-tail env) -> tl])
                    `(return-point ,lb ,tl)])))
                    
    ; helper function: find x in env
    (define (f env)
        (lambda (x)
            (if (and (uvar? x) (assq x env))
                (cadr (assq x env))
                x)))
    
    (finalize-program program))

;   select-instructions
;   rewrite set! & (triv) & mset! & (relop)

(define (select-instructions program)
    (define (operator^ relop)
	    (case relop
		    [`> `<]
		    [`< `>]
			[`<= `>=]
            [`>= `<=]
		    [`= `=]))
        
    (define (INT64? x)
        (if (and (int64? x) (not (int32? x))) #t #f))

    ; (tail) -> (tl uv*)
    (define (select-tail tail)
        (match tail
            [(if ,[select-pred -> pr u-pr] ,[select-tail -> tl1 u-tl1] ,[select-tail -> tl2 u-tl2])
                (values `(if ,pr ,tl1 ,tl2) (append u-pr u-tl1 u-tl2))]
            [(begin ,[select-effect -> ef* u-ef*] ... ,[select-tail -> tl u-tl])
                (values (make-begin `(,ef* ... ,tl)) (apply append u-tl u-ef*))]
            [(,tr ,loc* ...)
                (if (integer? tr) ; constrain: tr can't be interger
                    (let ([uv (unique-name 't)])
                        (values `(begin (set! ,uv ,tr) (,uv ,loc* ...)) `(,uv)))
                    (values `(,tr ,loc* ...) '()))]))
    
    ; (pred) -> (pr uv*)
    (define (select-pred pred)
        (match pred
            [(true) (values `(true) `())]
            [(false) (values `(false) `())]
            [(if ,[select-pred -> pr1 u-pr1] ,[select-pred -> pr2 u-pr2] ,[select-pred -> pr3 u-pr3])
                (values `(if ,pr1 ,pr2 ,pr3) (append u-pr1 u-pr2 u-pr3))]
            [(begin ,[select-effect -> ef* u-ef*] ... ,[select-pred -> pr u-pr])
                (values (make-begin `(,ef* ... ,pr)) (apply append u-pr u-ef*))]
            [(,relop ,tr1 ,tr2) ; constrains on relop
                (cond 
                    ; tr1: fv / uv / reg / lb / int | tr2: fv / uv / reg / lb / int
                    [(or (label? tr1) (INT64? tr1))
                        (let ([uv (unique-name 't)])
                            (let-values ([(pr u-pr) (select-pred `(begin (set! ,uv ,tr1) (,relop ,uv ,tr2)))])
                                (values pr (cons uv u-pr))))]
                    [(or (label? tr2) (INT64? tr2))
                        (let ([uv (unique-name 't)])
                            (let-values ([(pr u-pr) (select-pred `(begin (set! ,uv ,tr2) (,relop ,tr1 ,uv)))])
                                (values pr (cons uv u-pr))))]
                    ; tr1: fv / uv / reg / int32 | tr2: fv / uv / reg / int32
                    [(and (int32? tr1) (int32? tr2))
                        (let ([uv (unique-name 't)])
                            (values `(begin (set! ,uv ,tr1) (,relop ,uv ,tr2)) `(,uv)))]
                    [(and (frame-var? tr1) (frame-var? tr2))
                        (let ([uv (unique-name 't)])
                            (values `(begin (set! ,uv ,tr1) (,relop ,uv ,tr2)) `(,uv)))]               
                    [(int32? tr1)
                        (values `(,(operator^ relop) ,tr2 ,tr1) `())]
                    [else
                        (values `(,relop ,tr1 ,tr2) `())])]))
    
    ; (effect) -> (ef uv*)
    (define (select-effect effect)
        (match effect
            [(nop) (values `(nop) `())]
            [(begin ,[select-effect -> ef1* u-ef1*] ... ,[select-effect -> ef2 u-ef2])
                (values (make-begin `(,ef1* ... ,ef2)) (apply append u-ef2 u-ef1*))]
            [(if ,[select-pred -> pr u-pr] ,[select-effect -> ef1 u-ef1] ,[select-effect -> ef2 u-ef2])
                (values `(if ,pr ,ef1 ,ef2) (append u-pr u-ef1 u-ef2))]
            [(set! ,v (mref ,tr1 ,tr2))
                (cond 
                    [(and (not (register? v)) (not (uvar? v)))
                        (let ([uv (unique-name 't)])
                            (let-values ([(ef u-ef) (select-effect `(begin
                                                                     (set! ,uv (mref ,tr1 ,tr2))
                                                                     (set! ,v ,uv)))])
                                (values ef (cons uv u-ef))))]
                    [(integer? tr1)
                        (cond
                            [(or (register? tr2) (uvar? tr2))
                                (values `(set! ,v (mref ,tr1 ,tr2)) `())]
                            [else
                                (let ([uv (unique-name 't)])
                                    (values `(begin (set! ,uv ,tr2) (set! ,v (mref ,tr1 ,uv))) `(,uv)))])]
                    [(integer? tr2)
                        (cond
                            [(or (register? tr1) (uvar? tr1))
                                (values `(set! ,v (mref ,tr1 ,tr2)) `())]
                            [else
                                (let ([uv (unique-name 't)])
                                    (values `(begin (set! ,uv ,tr1) (set! ,v (mref ,uv ,tr2))) `(,uv)))])]
                    [(and (not (register? tr1)) (not (uvar? tr1)))
                        (let ([uv (unique-name 't)])
                            (let-values ([(ef u-ef) (select-effect `(begin
                                                                     (set! ,uv ,tr1)
                                                                     (set! ,v (mref ,uv ,tr2))))])
                                (values ef (cons uv u-ef))))]
                    [(and (not (register? tr2)) (not (uvar? tr2)))
                        (let ([uv (unique-name 't)])
                            (let-values ([(ef u-ef) (select-effect `(begin
                                                                     (set! ,uv ,tr2)
                                                                     (set! ,v (mref ,tr1 ,uv))))])
                                (values ef (cons uv u-ef))))]
                    [else (values `(set! ,v (mref ,tr1 ,tr2)) `())])]
            [(set! ,v (,binop ,tr1 ,tr2))
                (cond
                    [(and (not (eq? v tr1)) (eq? v tr2) (memq binop `(+ * logand logor)))
                        (select-effect `(set! ,v (,binop ,tr2 ,tr1)))]

                    [(not (eq? v tr1))
                        (let ([uv (unique-name 't)])
                            (let-values ([(ef u-ef) (select-effect `(begin
                                                                    (set! ,uv ,tr1)
                                                                    (set! ,uv (,binop ,uv ,tr2))
                                                                    (set! ,v ,uv)))])
                                (values ef (cons uv u-ef))))]
                    [(memq binop `(+ - logand logor))
                        (cond
                            [(or (label? tr2) (INT64? tr2) (and (frame-var? tr2) (frame-var? v)))
                                (let ([uv (unique-name 't)])
                                    (values `(begin (set! ,uv ,tr2) (set! ,v (,binop ,v ,uv))) `(,uv)))]
                            [else
                                (values `(set! ,v (,binop ,tr1 ,tr2)) `())])]
                    [(eq? binop `*)
                        (cond
                            [(frame-var? v)
                                (let ([uv (unique-name 't)])
                                    (let-values ([(ef u-ef) (select-effect `(begin
                                                                            (set! ,uv ,tr1)
                                                                            (set! ,uv (,binop ,uv ,tr2))
                                                                            (set! ,v ,uv)))])
                                        (values ef (cons uv u-ef))))]
                            [(or (label? tr2) (INT64? tr2))
                                (let ([uv (unique-name 't)])
                                    (values `(begin (set! ,uv ,tr2) (set! ,v (,binop ,v ,uv))) `(,uv)))]
                            [else
                                (values `(set! ,v (,binop ,tr1 ,tr2)) `())])]
                    [(eq? binop `sra)
                        (values `(set! ,v (,binop ,tr1 ,tr2)) `())])]
            [(set! ,v ,tr) ; constrains on set!
                (cond 
                    ; v: fv / uv / reg | tr: fv / uv / reg / lb / int
                    [(or (register? v) (uvar? v))
                        (values `(set! ,v ,tr) `())]
                    ; v: fv | tr: fv / uv / reg / lb / int
                    [(or (frame-var? tr) (label? tr) (INT64? tr))
                        (let ([uv (unique-name 't)])
							(values `(begin (set! ,uv ,tr) (set! ,v ,uv)) `(,uv)))]
                    [else 
                        (values `(set! ,v ,tr) `())])]
            [(mset! ,tr1 ,tr2 ,tr3)
                (cond 
                    [(and (not (register? tr3)) (not (uvar? tr3)) (not (integer? tr3)))
                        (let ([uv (unique-name 't)])
                            (let-values ([(ef u-ef) (select-effect `(begin
                                                                     (set! ,uv ,tr3)
                                                                     (mset! ,tr1 ,tr2 ,uv)))])
                                (values ef (cons uv u-ef))))]
                    [(integer? tr1)
                        (cond
                            [(or (register? tr2) (uvar? tr2))
                                (values `(mset! ,tr1 ,tr2 ,tr3) `())]
                            [else
                                (let ([uv (unique-name 't)])
                                    (values `(begin (set! ,uv ,tr2) (mset! ,tr1 ,uv ,tr3)) `(,uv)))])]
                    [(integer? tr2)
                        (cond
                            [(or (register? tr1) (uvar? tr1))
                                (values `(mset! ,tr1 ,tr2 ,tr3) `())]
                            [else
                                (let ([uv (unique-name 't)])
                                    (values `(begin (set! ,uv ,tr1) (mset! ,uv ,tr2 ,tr3)) `(,uv)))])]
                    [(and (not (register? tr1)) (not (uvar? tr1)))
                        (let ([uv (unique-name 't)])
                            (let-values ([(ef u-ef) (select-effect `(begin
                                                                     (set! ,uv ,tr1)
                                                                     (mset! ,uv ,tr2 ,tr3)))])
                                (values ef (cons uv u-ef))))]
                    [(and (not (register? tr2)) (not (uvar? tr2)))
                        (let ([uv (unique-name 't)])
                            (let-values ([(ef u-ef) (select-effect `(begin
                                                                     (set! ,uv ,tr2)
                                                                     (mset! ,tr1 ,uv ,tr3)))])
                                (values ef (cons uv u-ef))))]
                    [else (values `(mset! ,tr1 ,tr2 ,tr3) `())])]
            [(return-point ,lb ,[select-tail -> tl u-tl])
                (values `(return-point ,lb ,tl) u-tl)]))

    (define (select-body body)
        (match body
            [(locals ,local*
                (ulocals ,ulocal*
                    (locate ,as
                        (frame-conflict ,fcg ,tl))))
                (let-values ([(new-tl new-ulocal*) (select-tail tl)])
                    `(locals ,local*
                        (ulocals ,(append ulocal* new-ulocal*)
                            (locate ,as
                                (frame-conflict ,fcg ,new-tl)))))]
            [(locate ,as ,tl)
                `(locate ,as ,tl)]))

    (define (select-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[select-body -> bd1*])] ...) ,[select-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))
    
    (select-program program))

;   uncover-register-conflict
;   add register-conflict-graph for each body

(define (uncover-register-conflict program)
    ; dangerous variable
    ; deep-copy before used
    (define rcg `())

    (define (uncover-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[uncover-body -> bd1*])] ...) ,[uncover-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (uncover-body body)
        (match body
            [(locals ,local*
                (ulocals ,ulocal*
                    (locate ,as
                        (frame-conflict ,fcg ,tl))))
                (begin
                    (set! rcg `((,local*) ... (,ulocal*) ...))
                    (uncover-tail tl)
                    `(locals ,local*
                        (ulocals ,ulocal*
                            (locate ,as
                                (frame-conflict ,fcg
                                    (register-conflict ,(deep-copy rcg) ,tl))))))]
            [(locate ([,uv* ,loc*] ...) ,tl)
                `(locate ([,uv* ,loc*] ...) ,tl)]))

    (define (try-to-add x live-set)
        (if (or (register? x) (uvar? x))
            (set-cons x live-set)
            live-set))
    (define (try-to-delete x live-set)
        (if (or (register? x) (uvar? x))
            (difference live-set `(,x))
            live-set))
    
    (define (add-conflict x live-set)
        (if (null? live-set)
            `()
            (begin 
                (let ([y (car live-set)])
                    (cond
                        [(and (uvar? x)(register? y))
                            (let ([entry (assq x rcg)])
                                (set-cdr! entry (set-cons y (cdr entry))))]
                        [(and (uvar? y)(register? x))
                            (let ([entry (assq y rcg)])
                                (set-cdr! entry (set-cons x (cdr entry))))]
                        [(and (uvar? y)(uvar? x))
                            (let ([entry-x (assq x rcg)]
                                  [entry-y (assq y rcg)])
                                (set-cdr! entry-x (set-cons y (cdr entry-x)))
                                (set-cdr! entry-y (set-cons x (cdr entry-y))))]
                        [else `()]))
                (add-conflict x (cdr live-set)))))

    ; only leave registers
    (define (filter ls)
        (if (null? ls)
            `()
            (try-to-add (car ls) (filter (cdr ls)))))
    
    ; (effetc* live-set) -> (ls)
    (define (uncover-effect* effect* live-set)
        (if (null? effect*)
            live-set
            (let ([ls (uncover-effect* (cdr effect*) live-set)])
                (uncover-effect (car effect*) ls))))

    ; (tail) -> (ls)
    (define (uncover-tail tail)
        (match tail
            [(if ,pr ,[uncover-tail -> ls-tl1] ,[uncover-tail -> ls-tl2])
                (uncover-pred pr (union ls-tl1 ls-tl2))]
            [(begin ,ef* ... ,[uncover-tail -> ls-tl])
                (uncover-effect* ef* ls-tl)]
            [(,tr ,loc* ...)
                (try-to-add tr (filter loc*))]))

    ; (pred live-set) -> (ls)
    (define (uncover-pred pred live-set)
        (match pred
            [(true) live-set]
            [(false) live-set]
            [(if ,pr1 ,pr2 ,pr3)
                (let ([ls-pr2 (uncover-pred pr2 live-set)]
                      [ls-pr3 (uncover-pred pr3 live-set)])
                    (uncover-pred pr1 (union ls-pr2 ls-pr3)))]
            [(begin ,ef* ... ,pr)
                (let ([ls-pr (uncover-pred pr live-set)])
                    (uncover-effect* ef* ls-pr))]
            [(,relop ,tr1 ,tr2)
                (try-to-add tr1 (try-to-add tr2 live-set))]))
    
    ; (effect live-set) -> (ls)
    (define (uncover-effect effect live-set)
        (match effect
            [(nop) live-set]
            [(begin ,ef1* ... ,ef2)
                (let ([ls-ef2 (uncover-effect ef2 live-set)])
                    (uncover-effect* ef1* ls-ef2))]
            [(if ,pr ,ef1 ,ef2)
                (let ([ls-ef1 (uncover-effect ef1 live-set)]
                      [ls-ef2 (uncover-effect ef2 live-set)])
                    (uncover-pred pr (union ls-ef1 ls-ef2)))]
            [(set! ,v (,binop ,tr1 ,tr2)) (guard (memq binop `(+ - * logand logor sra mref)))
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (register? v) (uvar? v)) (add-conflict v ls) `())
                        (try-to-add tr1 (try-to-add tr2 ls))))]
            [(set! ,v ,tr)
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (register? v) (uvar? v)) (add-conflict v (difference ls `(,tr))) `())
                        (try-to-add tr ls)))]
            [(mset! ,tr1 ,tr2 ,tr3) (try-to-add tr1 (try-to-add tr2 (try-to-add tr3 live-set)))]
            [(return-point ,lb ,tl) (uncover-tail tl)]))
    
    (uncover-program program))

;   assign-registers
;   based on the register-conflict-graph, assign uvars to registers
;   each function call is independent

(define (assign-registers program)
    (define (remove-node-helper conflict-graph node ctr-list)
        (if (null? ctr-list)
            conflict-graph
            (if (register? (car ctr-list))
                (remove-node-helper conflict-graph node (cdr ctr-list))
                (let* ([entry (assq (car ctr-list) conflict-graph)]
                       [rcg (cons (difference entry `(,node)) (remq entry conflict-graph))])
                    (remove-node-helper rcg node (cdr ctr-list))))))

    (define (remove-node conflict-graph node)
        (let* ([entry (assq node conflict-graph)])
            (remove-node-helper (remq entry conflict-graph) node (cdr entry))))
    
    (define (find-low-degree conflict-graph) 
        (if (null? conflict-graph)
            (values 0 `invalid)
            (let-values ([(deg node) (find-low-degree (cdr conflict-graph))])
                (let ([cur-deg (- (length (car conflict-graph)) 1)])
                    (if (>= cur-deg deg)
                        (values cur-deg (caar conflict-graph))
                        (values deg node))))))

    (define (find-spillable conflict-graph spillable*)
        (let ([node (car spillable*)])
            (if (assq node conflict-graph)
                node
                (find-spillable conflict-graph (cdr spillable*)))))

    (define (find-ban-list ctr-list assignment)
        (if (null? ctr-list)
            `()
            (let ([ls (find-ban-list (cdr ctr-list) assignment)]
                  [x (car ctr-list)])
                (cond
                    [(register? x) (set-cons x ls)]
                    [(uvar? x) (set-cons (cadr (assq x assignment)) ls)]))))

    ; (conflict-graph spillable* unspillable*) -> (as)
    (define (assign conflict-graph spillable* unspillable*) 
        (if (null? conflict-graph)
            `()
            (let-values ([(deg node) (find-low-degree conflict-graph)])
                (if (>= deg (length registers))
                    (let* ([node (find-spillable conflict-graph spillable*)]
                           [entry (assq node conflict-graph)]
                           [rcg (remove-node conflict-graph node)]
                           [as (assign rcg spillable* unspillable*)] ;?
                           [ban-reg-ls (find-ban-list (cdr entry) as)]
                           [loc (if (null? (difference registers ban-reg-ls))
                                    `spill
                                    (car (difference registers ban-reg-ls)))])
                        (cons (list node loc) as))
                    (let* ([entry (assq node conflict-graph)]
                           [rcg (remove-node conflict-graph node)]
                           [as (assign rcg spillable* unspillable*)] ; ?
                           [ban-reg-ls (find-ban-list (cdr entry) as)]
                           [loc (car (difference registers ban-reg-ls))])
                        (cons (list node loc) as))))))

    (define (assign-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[assign-body -> bd1*])] ...) ,[assign-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (find-spills assignment)
        (if (null? assignment)
            `()
            (let ([entry (car assignment)])
                (if (eq? (cadr entry) `spill)
                    (cons (car entry) (find-spills (cdr assignment)))
                    (find-spills (cdr assignment))))))

    (define (assign-body body)
        (match body
            [(locals ,local*
                (ulocals ,ulocal*
                    (locate ,as
                        (frame-conflict ,fcg
                            (register-conflict ,rcg ,tl)))))
                (let* ([new-as (assign rcg local* ulocal*)]
                       [sp* (find-spills new-as)]
                       [new-local* (difference local* sp*)])
                    (if (null? sp*)
                        `(locate ,(append as new-as) ,tl)
                        `(locals ,new-local*
                            (ulocals ,ulocal*
                                (spills ,sp*
                                    (locate ,as
                                        (frame-conflict ,fcg ,tl)))))))]
            [(locate ,as ,tl)
                `(locate ,as ,tl)]))

    (assign-program program))

;   assign-frame
;   based on the frame-conflict-graph, assign uvars to frame

(define (assign-frame program)
    (define (find-first-available ctr*)
        (let while ([i 0])
            (let ([fv (index->frame-var i)])
                (if (memq fv ctr*)
                    (while (+ i 1))
                    fv))))
    
    (define (filter assignment)
        (lambda (x)
            (cond
                [(frame-var? x) x]
                [(and (uvar? x) (assq x assignment)) (cadr (assq x assignment))]
                [else `invalid])))

    ; (conflict-graph spill* assignment) -> (as)
    (define (assign conflict-graph spill* assignment) 
        (if (null? spill*)
            assignment
            (let ([node (car spill*)])
                (let* ([as (assign conflict-graph (cdr spill*) assignment)]
                       [entry (assq node conflict-graph)]
                       [ctr* (map (filter as) (cdr entry))]
                       [loc (find-first-available ctr*)])
                    (cons (list node loc) as)))))

    (define (assign-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[assign-body -> bd1*])] ...) ,[assign-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (assign-body body)
        (match body
            [(locals ,local*
                (ulocals ,ulocal*
                    (spills ,sp*
                        (locate ,as
                            (frame-conflict ,fcg ,tl)))))
                (let ([new-as (assign fcg sp* as)])
                    `(locals ,local*
                        (ulocals ,ulocal*
                            (locate ,new-as
                                (frame-conflict ,fcg ,tl)))))]
            [(locate ,as ,tl)
                `(locate ,as ,tl)]))

    (assign-program program))

;   discard-call-live
;   in tail: (triv loc*) -> (triv)

(define (discard-call-live program)
    (define (discard-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[discard-body -> bd1*])] ...) ,[discard-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (discard-body body)
        (match body
            [(locate ,as ,[discard-tail -> tl])
                `(locate ,as ,tl)]))   

    (define (discard-tail tail)
        (match tail
            [(begin ,[discard-effect -> ef*] ... ,[discard-tail -> tl]) `(begin ,ef* ... ,tl)]
	          [(if ,[discard-pred -> pr] ,[discard-tail -> tl1] ,[discard-tail -> tl2]) `(if ,pr ,tl1 ,tl2)]
	          [(,tr ,loc* ...)  `(,tr)]))

    (define (discard-pred pred)
        (match pred
            [(true) `(true)]
            [(false) `(false)]
            [(if ,[discard-pred -> pr1] ,[discard-pred -> pr2] ,[discard-pred -> pr3]) `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[discard-effect -> ef*] ... ,[discard-pred -> pr]) (make-begin `(,ef* ... ,pr))]
            [(,relop ,tr1 ,tr2) `(,relop ,tr1 ,tr2)]))
    
    (define (discard-effect effect)
        (match effect
            [(nop) `(nop)]
            [(begin ,[discard-effect -> ef1*] ... ,[discard-effect -> ef2]) (make-begin `(,ef1* ... ,ef2))]
            [(if ,[discard-pred -> pr] ,[discard-effect -> ef1] ,[discard-effect -> ef2]) `(if ,pr ,ef1 ,ef2)]
            [(set! ,v (,binop ,tr1 ,tr2)) `(set! ,v (,binop ,tr1 ,tr2))]
            [(set! ,v ,tr) `(set! ,v ,tr)]
            [(mset! ,tr1 ,tr2 ,tr3) `(mset! ,tr1 ,tr2 ,tr3)]
            [(return-point ,lb ,[discard-tail -> tl]) `(return-point ,lb ,tl)]))
    
    (discard-program program))

;   finalize-locations
;   discard location form, r.8 -> rax

(define (finalize-locations program)
    (define (finalize-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[finalize-body -> bd1*])] ...) ,[finalize-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (finalize-body body)
        (match body
            [(locate ,as ,tl)
                ((makefunc-tail as) tl)]))

    (define (makefunc-tail env)
        (lambda (tail) 
            (match tail
                [(if ,[(makefunc-pred env) -> pr] ,[(makefunc-tail env) -> tl1] ,[(makefunc-tail env) -> tl2])
                    `(if ,pr ,tl1 ,tl2)]
                [(begin ,[(makefunc-effect env) -> ef*] ... ,[(makefunc-tail env) -> tl])
                    `(begin ,ef* ... ,tl)]
                [(,tr ,loc* ...) (map (f env) (cons tr loc*))])))

    (define (makefunc-pred env)
        (lambda (pred) 
            (match pred
                [(true) `(true)]
                [(false) `(false)]
                [(if ,[(makefunc-pred env) -> pr1] ,[(makefunc-pred env) -> pr2] ,[(makefunc-pred env) -> pr3])
                    `(if ,pr1 ,pr2 ,pr3)]
                [(begin ,[(makefunc-effect env) -> ef*] ... ,[(makefunc-pred env) -> pr])
                    `(begin ,ef* ... ,pr)]
                [(,relop ,tr1 ,tr2)
                    `(,relop ,((f env) tr1) ,((f env) tr2))])))

    (define (makefunc-effect env)
        (lambda (effect) 
            (match effect
                [(nop) `(nop)]
                [(begin ,[(makefunc-effect env) -> ef1*] ... ,[(makefunc-effect env) -> ef2])
                    `(begin ,ef1* ... ,ef2)]
                [(if ,[(makefunc-pred env) -> pr] ,[(makefunc-effect env) -> ef1] ,[(makefunc-effect env) -> ef2])
                    `(if ,pr ,ef1 ,ef2)]
                [(set! ,v (,binop ,tr1 ,tr2)) (guard (memq binop `(+ - * logand logor sra mref)))
                    `(set! ,((f env) v) (,binop ,((f env) tr1) ,((f env) tr2)))]
                [(set! ,v ,tr)
                    (if (eq? ((f env) v) ((f env) tr))
                        `(nop)
                        `(set! ,((f env) v) ,((f env) tr)))]
                [(mset! ,tr1 ,tr2 ,tr3)
                    `(mset! ,((f env) tr1) ,((f env) tr2) ,((f env) tr3))]
                [(return-point ,lb ,[(makefunc-tail env) -> tl])
                    `(return-point ,lb ,tl)])))
    
    ; helper function: find x in env
    (define (f env)
        (lambda (x)
            (if (and (uvar? x) (assq x env))
                (cadr (assq x env))
                x)))
    
    (finalize-program program))

;   expose-frame-var
;   fvn -> #<disp rbp 8 * n>

(define (expose-frame-var program)
    (define (expose-triv offset)
        (lambda (triv)
            (if (frame-var? triv)
                (make-disp-opnd frame-pointer-register (- (* (ash 1 align-shift) (frame-var->index triv)) offset))
                triv)))

    (define (expose-tail tail offset)
        (match tail
            [(if ,pr ,tl1 ,tl2)
                (let*-values ([(new-pr off-pr) (expose-pred pr offset)]
                              [(new-tl1 off-tl1) (expose-tail tl1 off-pr)]
                              [(new-tl2 off-tl2) (expose-tail tl2 off-pr)])
                    (values `(if ,new-pr ,new-tl1 ,new-tl2)
                            off-tl2))]
            [(begin ,ef* ... ,tl)
                (let*-values ([(new-ef* off-ef*) (expose-effect* ef* offset)]
                              [(new-tl off-tl) (expose-tail tl off-ef*)])
                    (values `(begin ,new-ef* ... ,new-tl)
                            off-tl))]
            [(,[(expose-triv offset) -> tr]) (values `(,tr) offset)]))

    (define (expose-effect* effect* offset)
        (if (null? effect*)
            (values `() offset)
            (let*-values ([(new-ef1 off-ef1) (expose-effect (car effect*) offset)]
                          [(new-ef.. off-ef..) (expose-effect* (cdr effect*) off-ef1)])
                (values (cons new-ef1 new-ef..) off-ef..))))

    (define (expose-pred pred offset)
        (match pred
            [(true) (values pred offset)]
            [(false) (values pred offset)]
            [(if ,pr1 ,pr2 ,pr3)
                (let*-values ([(new-pr1 off-pr1) (expose-pred pr1 offset)]
                              [(new-pr2 off-pr2) (expose-pred pr2 off-pr1)]
                              [(new-pr3 off-pr3) (expose-pred pr3 off-pr1)])
                    (values `(if ,new-pr1 ,new-pr2 ,new-pr3)
                            off-pr3))]
            [(begin ,ef* ... ,pr)
                (let*-values ([(new-ef* off-ef*) (expose-effect* ef* offset)]
                              [(new-pr off-pr) (expose-pred pr off-ef*)])
                    (values `(begin ,new-ef* ... ,new-pr)
                            off-pr))]
            [(,relop ,[(expose-triv offset) -> tr1] ,[(expose-triv offset) -> tr2])
                (values `(,relop ,tr1 ,tr2) offset)]))

    (define (expose-effect effect offset)
        (match effect
            [(nop) (values effect offset)]
            [(begin ,ef1* ... ,ef2)
                (let*-values ([(new-ef1* off-ef1*) (expose-effect* ef1* offset)]
                              [(new-ef2 off-ef2) (expose-effect ef2 off-ef1*)])
                    (values `(begin ,new-ef1* ... ,new-ef2)
                            off-ef2))]
            [(if ,pr ,ef1 ,ef2)
                (let*-values ([(new-pr off-pr) (expose-pred pr offset)]
                              [(new-ef1 off-ef1) (expose-effect ef1 off-pr)]
                              [(new-ef2 off-ef2) (expose-effect ef2 off-pr)])
                    (values `(if ,new-pr ,new-ef1 ,new-ef2)
                            off-ef2))]
            [(set! ,fp (,binop ,fp ,off)) (guard (eq? fp frame-pointer-register))
         	      (if (eq? binop `+)
                    (values effect (+ offset off))
                    (values effect (- offset off)))]
            [(set! ,[(expose-triv offset) -> loc] (,binop ,[(expose-triv offset) -> tr1] ,[(expose-triv offset) -> tr2]))
                (guard (memq binop `(+ - * logand logor sra mref)))
                    (values `(set! ,loc (,binop ,tr1 ,tr2)) offset)]
            [(set! ,[(expose-triv offset) -> loc] ,[(expose-triv offset) -> tr])
                (values `(set! ,loc ,tr) offset)]
            [(mset! ,[(expose-triv offset) -> tr1] ,[(expose-triv offset) -> tr2] ,[(expose-triv offset) -> tr3])
                (values `(mset! ,tr1 ,tr2 ,tr3) offset)]
            [(return-point ,lb ,tl)
                (let*-values ([(new-tl off-tl) (expose-tail tl offset)])
                    (values `(return-point ,lb ,new-tl) off-tl))]))
    
    (define (helper ls)
        (if (null? ls)
            (values `() `())
            (let-values ([(ls1 ls2) (helper (cdr ls))]
                         [(x y) (expose-tail (car ls) 0)])
                (values (cons x ls1) (cons y ls2)))))
    (define (expose-program program)
        (match program
            [(letrec ([,lb* (lambda () ,tl1*)] ...) ,tl2)
                (let*-values ([(new-tl1* off-tl1*) (helper tl1*)]
                              [(new-tl2 off-tl2) (expose-tail tl2 0)])
                    `(letrec ([,lb* (lambda () ,new-tl1*)] ...) ,new-tl2))]))

    (expose-program program))

;   expose-memory-operands
;   mset! & mref -> disp-opnd

(define (expose-memory-operands program)
    (define (expose-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[expose-tail -> tl1*])] ...) ,[expose-tail -> tl2])
                `(letrec ([,lb* (lambda () ,tl1*)] ...) ,tl2)]))

    (define (expose-tail tail)
        (match tail
            [(begin ,[expose-effect -> ef*] ... ,[expose-tail -> tl]) `(begin ,ef* ... ,tl)]
	        [(if ,[expose-pred -> pr] ,[expose-tail -> tl1] ,[expose-tail -> tl2]) `(if ,pr ,tl1 ,tl2)]
	        [(,tr)  `(,tr)]))

    (define (expose-pred pred)
        (match pred
            [(true) `(true)]
            [(false) `(false)]
            [(if ,[expose-pred -> pr1] ,[expose-pred -> pr2] ,[expose-pred -> pr3]) `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[expose-effect -> ef*] ... ,[expose-pred -> pr]) (make-begin `(,ef* ... ,pr))]
            [(,relop ,tr1 ,tr2) `(,relop ,tr1 ,tr2)]))
    
    (define (expose-effect effect)
        (match effect
            [(nop) `(nop)]
            [(begin ,[expose-effect -> ef1*] ... ,[expose-effect -> ef2]) (make-begin `(,ef1* ... ,ef2))]
            [(if ,[expose-pred -> pr] ,[expose-effect -> ef1] ,[expose-effect -> ef2]) `(if ,pr ,ef1 ,ef2)]
            [(set! ,v (mref ,tr1 ,tr2))
                (cond
                    [(integer? tr1) `(set! ,v ,(make-disp-opnd tr2 tr1))]
                    [(integer? tr2) `(set! ,v ,(make-disp-opnd tr1 tr2))]
                    [else `(set! ,v ,(make-index-opnd tr1 tr2))])]
            [(set! ,v (,binop ,tr1 ,tr2)) `(set! ,v (,binop ,tr1 ,tr2))]
            [(set! ,v ,tr) `(set! ,v ,tr)]
            [(mset! ,tr1 ,tr2 ,tr3)
                (cond
                    [(integer? tr1) `(set! ,(make-disp-opnd tr2 tr1) ,tr3)]
                    [(integer? tr2) `(set! ,(make-disp-opnd tr1 tr2) ,tr3)]
                    [else `(set! ,(make-index-opnd tr1 tr2) ,tr3)])]
            [(return-point ,lb ,[expose-tail -> tl]) `(return-point ,lb ,tl)]))
    
    (expose-program program))

;   expose-basic-blocks
;   convert into 'basic' blocks with 'jump' at the end of each block

(define (expose-basic-blocks program)
    ; (tail) -> (tl blks)
    (define (expose-tail tail)
        (match tail
            [(if ,pr ,[expose-tail -> tl-tl1 blks-tl1] ,[expose-tail -> tl-tl2 blks-tl2])
                (let* ([lb-t (unique-label `case-t)]
                       [lb-f (unique-label `case-f)]
                       [b1 (cons `[,lb-t (lambda () ,tl-tl1)] blks-tl1)]
                       [b2 (cons `[,lb-f (lambda () ,tl-tl2)] blks-tl2)])
                    (let-values ([(tl-pr blks-pr) (expose-pred pr lb-t lb-f)])
                        (values tl-pr (append blks-pr b1 b2))))]

            [(begin ,ef* ... ,[expose-tail -> tl-tl blks-tl])
                (let-values ([(tl.. blks..) (expose-effect* ef* tl-tl)])
                    (values tl.. (append blks.. blks-tl)))]
            [(,tr) (values `(,tr) `())]))

    ; (effect* tail) -> (tl blks)
    (define (expose-effect* effect* tail)
        (if (null? effect*)
            (values tail `())
            (let*-values ([(tl.. blks..) (expose-effect* (cdr effect*) tail)]
                          [(tl-ef1 blks-ef1) (expose-effect (car effect*) tl..)])
                (values tl-ef1 (append blks-ef1 blks..)))))

    ; (pred label-t label-f) -> (tl blks)
    (define (expose-pred pred label-t label-f)
        (match pred
            [(true) (values `(,label-t) `())]
            [(false) (values `(,label-f) `())]
            [(if ,pr1 ,pr2 ,pr3)
                (let-values ([(tl-pr2 blks-pr2) (expose-pred pr2 label-t label-f)]
                             [(tl-pr3 blks-pr3) (expose-pred pr3 label-t label-f)])
                    (let* ([lb-t (unique-label `case-t)]
                           [lb-f (unique-label `case-f)]
                           [b2 (cons `[,lb-t (lambda () ,tl-pr2)] blks-pr2)]
                           [b3 (cons `[,lb-f (lambda () ,tl-pr3)] blks-pr3)])
                        (let-values ([(tl-pr1 blks-pr1) (expose-pred pr1 lb-t lb-f)])
                            (values tl-pr1 (append blks-pr1 b2 b3)))))]

            [(begin ,ef* ... ,pr)
                (let*-values ([(tl-pr blks-pr) (expose-pred pr label-t label-f)]
                              [(tl.. blks..) (expose-effect* ef* tl-pr)])
                    (values tl.. (append blks.. blks-pr)))]
            [(,relop ,tr1 ,tr2)
                (values `(if (,relop ,tr1 ,tr2) (,label-t) (,label-f)) `())]))

    ; (effect tail) -> (tl blks)
    (define (expose-effect effect tail)
        (match effect
            [(nop) (values tail `())]
            [(begin ,ef1* ... ,ef2)
                (let*-values ([(tl-ef2 blks-ef2) (expose-effect ef2 tail)]
                              [(tl.. blks..) (expose-effect* ef1* tl-ef2)])
                    (values tl.. (append blks.. blks-ef2)))]
            [(if ,pr ,ef1 ,ef2)
                (let* ([lb-nxt (unique-label `next)]
                       [b (list `[,lb-nxt (lambda () ,tail)])]
                       [tail `(,lb-nxt)])
                    (let-values ([(tl-ef1 blks-ef1) (expose-effect ef1 tail)]
                                 [(tl-ef2 blks-ef2) (expose-effect ef2 tail)])
                        (let* ([lb-t (unique-label `case-t)]
                               [lb-f (unique-label `case-f)]
                               [b1 (cons `[,lb-t (lambda () ,tl-ef1)] blks-ef1)]
                               [b2 (cons `[,lb-f (lambda () ,tl-ef2)] blks-ef2)])
                            (let-values ([(tl-pr blks-pr) (expose-pred pr lb-t lb-f)])
                                (values tl-pr (append blks-pr b1 b2 b))))))]

            [(set! ,loc (,binop ,tr1 ,tr2))
                (values (make-begin (list `(set! ,loc (,binop ,tr1 ,tr2)) tail)) `())]
            [(set! ,loc ,tr)
                (values (make-begin (list `(set! ,loc ,tr) tail)) `())]
            [(return-point ,lb ,[expose-tail -> tl-tl blks-tl])
                (let* ([b `[,lb (lambda () ,tail)]])
                    (values tl-tl (cons b blks-tl)))]))

    (define (expose-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[expose-tail -> tl-tl1* blks-tl1*])] ...) ,[expose-tail -> tl-tl2 blks-tl2])
                (let ([all-blocks (append blks-tl2 `(,blks-tl1* ... ...) `([,lb* (lambda () ,tl-tl1*)] ...))])
                    `(letrec ,all-blocks ,tl-tl2))]))

    (expose-program program))

;   optimize-jumps
;   compress simple jump
;   be careful with the loop

(define (optimize-jumps program)
    (define ls `())
    (define lb-loop (unique-label `loop))
    (define (opt-program program)
        (match program
            [(letrec ,bl* ,tl)
                (let-values ([(new-bl* assoc-ls) (check bl*)])
                    (set! ls (deep-copy assoc-ls))
                    (let ([bl-loop `[,lb-loop (lambda () (,lb-loop))]])
                        `(letrec ,(cons bl-loop (map opt-block new-bl*)) ,(opt-tail tl))))]))

    (define (check block*)
        (if (null? block*)
            (values `() `())
            (let-values ([(bl* assoc-ls) (check (cdr block*))])
                (match (car block*)
                    [[,lb1 (lambda () (,lb2)) (guard (label? lb2))]
                        (values bl* (cons `(,lb1 ,lb2) assoc-ls))]
                    [[,lb (lambda () ,tl)]
                        (values (cons (car block*) bl*) assoc-ls)]))))
    
    (define (find st)
        (let ([res (dfs st `())])
            (if res res lb-loop)))
    (define (dfs cur vis)
        (if (memq cur vis)
            #f
            (if (assq cur ls)
                (dfs (cadr (assq cur ls)) (cons cur vis))
                cur)))
    
    (define (opt-block block)
        (match block
            [[,lb (lambda () ,[opt-tail -> tl])]
                `[,lb (lambda () ,tl)]]))
    (define (opt-tail tail)
        (match tail
            [(if ,pr (,lb1) (,lb2)) `(if ,pr (,(find lb1)) (,(find lb2)))]
            [(begin ,[opt-effect -> ef*] ... ,[opt-tail -> tl]) `(begin ,ef* ... ,tl)]
            [(,tr) `(,(find tr))]))
    (define (opt-effect effect)
        (match effect
            [(set! ,loc ,tr) `(set! ,loc ,(find tr))]
            [(set! ,loc (binop ,loc_ ,tr)) `(set! ,loc (binop ,loc_ ,(find tr)))]))
    
    (opt-program program))

;   flatten-program
;   no begin& letrec; add jump

(define (flatten-program program)
    (define (flat-tail tail label-next)
        (match tail
            [(if ,pr (,lb1) (,lb2))
                (cond 
                    [(eq? label-next lb2) `((if ,pr (jump ,lb1)))]
                    [(eq? label-next lb1) `((if (not ,pr) (jump ,lb2)))]
                    [else `((if ,pr (jump ,lb1)) (jump ,lb2))])
                ]
            [(begin ,ef* ... ,tl)
                (append ef* (flat-tail tl label-next))]
            [(,tr) 
                (if (eq? tr label-next)
                    `()
                    `((jump ,tr)))]))

    (define (flat-program program)
        (match program
            [(letrec ([,lb* (lambda () ,tl1*)] ...) ,tl2)
                (append `(code)
                        (flat-tail tl2 (if (null? lb*) `a (car lb*))) 
                        (flat-lambdas lb* tl1*))]))

    ; helper function
    (define (flat-lambdas label* tail*) 
        (if (or (null? label*) (null? tail*))
            `()
            (let ([nxt-lb (if (null? (cdr label*)) `a (car (cdr label*)))])
                (append `(,(car label*)) 
                        (flat-tail (car tail*) nxt-lb)
                        (flat-lambdas (cdr label*) (cdr tail*))))))
        
    (flat-program program))

;   generate-x86-64
;   statements -> x86-64 instructions

(define (generate-x86-64 program)
    (define (which-binop binop)
        (cond
            [(eq? binop `+) `addq]
            [(eq? binop `-) `subq]
            [(eq? binop `*) `imulq]
            [(eq? binop `logand) `andq]
            [(eq? binop `logor) `orq]
            [(eq? binop `sra) `sarq]))
    (define (which-relop-not relop)
        (cond
            [(eq? relop `=) `jne]
            [(eq? relop `>) `jle]
            [(eq? relop `<) `jge]
            [(eq? relop `>=) `jl]
            [(eq? relop `<=) `jg]))
    (define (which-relop relop)
        (cond
            [(eq? relop `=) `je]
            [(eq? relop `>) `jg]
            [(eq? relop `<) `jl]
            [(eq? relop `>=) `jge]
            [(eq? relop `<=) `jle]))

    (define (generate-statement statement)
        (match statement
            [(jump ,opnd)
                (emit-jump 'jmp opnd)] ; jmp
            [(if (not (,relop ,tr1 ,tr2)) (jump ,opnd)) ; cmpq-not
                (begin (emit 'cmpq tr2 tr1)
                       (emit-jump (which-relop-not relop) opnd))]
            [(if (,relop ,tr1 ,tr2) (jump ,opnd)) ; cmpq
                (begin (emit 'cmpq tr2 tr1)
                       (emit-jump (which-relop relop) opnd))]
            [(set! ,reg ,lb) (guard (label? lb)) ; leaq
                (emit 'leaq lb reg)]
            [(set! ,v ,opnd) (guard (not (list? opnd))) ; movq
                (emit 'movq opnd v)]
            [(set! ,v (,binop ,v_ ,opnd)) ; binops
                (emit (which-binop binop) opnd v)]
            [,lb (guard (label? lb)) ; label
                (emit-label lb)]))
            
    (define generate-program
            (lambda (program)
                (match program
                    [(code ,statement+ ...) ; why
                        (for-each generate-statement statement+)])))
    
    (emit-program (generate-program program)))