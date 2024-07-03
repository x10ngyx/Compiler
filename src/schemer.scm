;   verify-scheme
;   do nothing

(define (verify-scheme x) x) 

;   finalize-locations
;   discard location, r.8 -> rax

(define (finalize-locations program)
    (define (finalize-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[finalize-body -> bd1*])] ...) ,[finalize-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (finalize-body body)
        (match body
            [(locate ([,uv* ,loc*] ...) ,tl)
                (let ([env `((,uv* . ,loc*) ...)])
                    ((makefunc-tail env) tl))]))

    (define (makefunc-tail env)
        (lambda (tail) 
            (match tail
                [(if ,[(makefunc-pred env) -> pr] ,[(makefunc-tail env) -> tl1] ,[(makefunc-tail env) -> tl2])
                    `(if ,pr ,tl1 ,tl2)]
                [(begin ,[(makefunc-effect env) -> ef*] ... ,[(makefunc-tail env) -> tl])
                    `(begin ,ef* ... ,tl)]
                [(,tr) `(,(f tr env))])))

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
                    `(,relop ,(f tr1 env) ,(f tr2 env))])))

    (define (makefunc-effect env)
        (lambda (effect) 
            (match effect
                [(nop) `(nop)]
                [(begin ,[(makefunc-effect env) -> ef1*] ... ,[(makefunc-effect env) -> ef2])
                    `(begin ,ef1* ... ,ef2)]
                [(if ,[(makefunc-pred env) -> pr] ,[(makefunc-effect env) -> ef1] ,[(makefunc-effect env) -> ef2])
                    `(if ,pr ,ef1 ,ef2)]
                [(set! ,v (,binop ,tr1 ,tr2))
                    `(set! ,(f v env) (,binop ,(f tr1 env) ,(f tr2 env)))]
                [(set! ,v ,tr)
                    `(set! ,(f v env) ,(f tr env))])))
    
    ; helper function: find x in env
    (define (f x env)
        (if (uvar? x)
            (cdr (assq x env))
            x))
    
    (finalize-program program))

;   expose-frame-var
;   fvn -> #<disp rbp 8 * n>

(define (expose-frame-var program)
    (define (expose-loc loc)
        (if (frame-var? loc)
            (make-disp-opnd `rbp (* 8 (frame-var->index loc)))
            loc))

    (define (expose-triv triv)
        (if (frame-var? triv)
            (make-disp-opnd `rbp (* 8 (frame-var->index triv)))
            triv))

    (define (expose-effect effect)
        (match effect
            [(nop) `(nop)]
            [(begin ,[expose-effect -> ef1*] ... ,[expose-effect -> ef2])
                `(begin ,ef1* ... ,ef2)]
            [(if ,[expose-pred -> pr] ,[expose-effect -> ef1] ,[expose-effect -> ef2])
                `(if ,pr ,ef1 ,ef2)]
            [(set! ,[expose-loc -> loc] (,binop ,(expose-triv -> tr1) ,(expose-triv -> tr2)))
                `(set! ,loc (,binop ,tr1 ,tr2))]
            [(set! ,[expose-loc -> loc] ,[expose-triv -> tr])
                `(set! ,loc ,tr)]))
    
    (define (expose-tail tail)
        (match tail
            [(if ,[expose-pred -> pr] ,[expose-tail -> tl1] ,[expose-tail -> tl2])
                `(if ,pr ,tl1 ,tl2)]
            [(begin ,[expose-effect -> ef*] ... ,[expose-tail -> tl])
                `(begin ,ef* ... ,tl)]
            [(,[expose-triv -> tr])
                `(,tr)]))
    
    (define (expose-pred pred)
        (match pred
            [(true) `(true)]
            [(false) `(false)]
            [(if ,[expose-pred -> pr1] ,[expose-pred -> pr2] ,[expose-pred -> pr3])
                `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[expose-effect -> ef*] ... ,[expose-pred -> pr])
                `(begin ,ef* ... ,pr)]
            [(,relop ,[expose-triv -> tr1] ,[expose-triv -> tr2])
                `(,relop ,tr1 ,tr2)]))

    (define (expose-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[expose-tail -> tl1*])] ...) ,[expose-tail -> tl2])
                `(letrec ([,lb* (lambda () ,tl1*)] ...) ,tl2)]))

        (expose-program program))

;   expose-basic-blocks
;   'basic' blocks and 'jump' at the end of each block

(define (expose-basic-blocks program)
    
    ; (tail) -> (tl blks)
    (define (expose-tail tail)
        (match tail
            [(if ,pr ,[expose-tail -> tl_tl1 blks_tl1] ,[expose-tail -> tl_tl2 blks_tl2])
                (let* ([lb-t (unique-label `case-t)]
                       [lb-f (unique-label `case-f)]
                       [b1 (cons `[,lb-t (lambda () ,tl_tl1)] blks_tl1)]
                       [b2 (cons `[,lb-f (lambda () ,tl_tl2)] blks_tl2)])
                    (let-values ([(tl_pr blks_pr) (expose-pred pr lb-t lb-f)])
                        (values tl_pr (append blks_pr b1 b2))))]

            [(begin ,ef* ... ,[expose-tail -> tl_tl blks_tl])
                (let-values ([(tl.. blks..) (expose-effect* ef* tl_tl)])
                    (values tl.. (append blks.. blks_tl)))]
            [(,tr) (values `(,tr) `())]))

    ; (effect* tail) -> (tl blks)
    (define (expose-effect* effect* tail)
        (if (null? effect*)
            (values tail `())
            (let*-values ([(tl.. blks..) (expose-effect* (cdr effect*) tail)]
                          [(tl_ef1 blks_ef1) (expose-effect (car effect*) tl..)])
                (values tl_ef1 (append blks_ef1 blks..)))))

    ; (pred label-t label-f) -> (tl blks)
    (define (expose-pred pred label-t label-f)
        (match pred
            [(true) (values `(,label-t) `())]
            [(false) (values `(,label-f) `())]
            [(if ,pr1 ,pr2 ,pr3)
                (let-values ([(tl_pr2 blks_pr2) (expose-pred pr2 label-t label-f)]
                             [(tl_pr3 blks_pr3) (expose-pred pr3 label-t label-f)])
                    (let* ([lb-t (unique-label `case-t)]
                           [lb-f (unique-label `case-f)]
                           [b2 (cons `[,lb-t (lambda () ,tl_pr2)] blks_pr2)]
                           [b3 (cons `[,lb-f (lambda () ,tl_pr3)] blks_pr3)])
                        (let-values ([(tl_pr1 blks_pr1) (expose-pred pr1 lb-t lb-f)])
                            (values tl_pr1 (append blks_pr1 b2 b3)))))]

            [(begin ,ef* ... ,pr)
                (let*-values ([(tl_pr blks_pr) (expose-pred pr label-t label-f)]
                              [(tl.. blks..) (expose-effect* ef* tl_pr)])
                    (values tl.. (append blks.. blks_pr)))]
            [(,relop ,tr1 ,tr2)
                (values `(if (,relop ,tr1 ,tr2) (,label-t) (,label-f)) `())]))

    ; (effect tail) -> (tl blks)
    (define (expose-effect effect tail)
        (match effect
            [(nop) (values tail `())]
            [(begin ,ef1* ... ,ef2)
                (let*-values ([(tl_ef2 blks_ef2) (expose-effect ef2 tail)]
                              [(tl.. blks..) (expose-effect* ef1* tl_ef2)])
                    (values tl.. (append blks.. blks_ef2)))]
            [(if ,pr ,ef1 ,ef2)
                (let* ([lb-nxt (unique-label `next)]
                       [b (list `[,lb-nxt (lambda () ,tail)])]
                       [tail `(,lb-nxt)])
                    (let-values ([(tl_ef1 blks_ef1) (expose-effect ef1 tail)]
                                 [(tl_ef2 blks_ef2) (expose-effect ef2 tail)])
                        (let* ([lb-t (unique-label `case-t)]
                               [lb-f (unique-label `case-f)]
                               [b1 (cons `[,lb-t (lambda () ,tl_ef1)] blks_ef1)]
                               [b2 (cons `[,lb-f (lambda () ,tl_ef2)] blks_ef2)])
                            (let-values ([(tl_pr blks_pr) (expose-pred pr lb-t lb-f)])
                                (values tl_pr (append blks_pr b1 b2 b))))))]

            [(set! ,loc (,binop ,tr1 ,tr2))
                (values (make-begin (list `(set! ,loc (,binop ,tr1 ,tr2)) tail)) `())]
            [(set! ,loc ,tr)
                (values (make-begin (list `(set! ,loc ,tr) tail)) `())]))

    ; helper function
    (define (flatten-once lst)
        (cond
            [(null? lst) '()]
            [else (append (car lst) (flatten-once (cdr lst)))]))

    (define (expose-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[expose-tail -> tl_tl1* blks_tl1*])] ...) ,[expose-tail -> tl_tl2 blks_tl2])
                (let ([all-blocks (append blks_tl2 (flatten-once blks_tl1*) `([,lb* (lambda () ,tl_tl1*)] ...))])
                    `(letrec ,all-blocks ,tl_tl2))]))

    (expose-program program))

;   flatten-program
;   no begin& letrec; add jump

(define (flatten-program program)
    (define (flat-tail tail label-next)
        (match tail
            [(if (,relop ,tr1 ,tr2) (,lb1) (,lb2))
                (cond 
                    [(eq? label-next lb2) `((if (,relop ,tr1 ,tr2) (jump ,lb1)))]
                    [(eq? label-next lb1) `((if (not (,relop ,tr1 ,tr2)) (jump ,lb2)))]
                    [else `((if (,relop ,tr1 ,tr2) (jump ,lb1)) (jump ,lb2))])
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
                        (flat-lambdas (cdr label*) (cdr tail*))))
            ))
        
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
            [(eq? binop `<=) `jg]))
    (define (which-relop relop)
        (cond
            [(eq? relop `=) `je]
            [(eq? relop `>) `jg]
            [(eq? relop `<) `jl]
            [(eq? relop `>=) `jge]
            [(eq? binop `<=) `jle]))

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
