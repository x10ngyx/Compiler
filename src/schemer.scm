(load "lib/match.scm")
(load "lib/helpers.scm")

;   helper functions
;   my-map

(define (my-map f lst)
  (if (null? lst) 
        '()
        (append `(,(f (car lst)))
            (my-map f (cdr lst)))))


;   verify-scheme
;   do nothing

(define verify-scheme 
    (lambda (x) x))

;   expose-frame-var
;   fvn -> #<disp rbp 8 * n>

(define expose-frame-var
    (lambda (program)
        (define expose-var
            (lambda (var)
                (if (frame-var? var)
                    (make-disp-opnd `rbp (* 8 (frame-var->index var)))
                    var
                    )))

        (define expose-triv
            (lambda (triv)
                (if (frame-var? triv)
                    (make-disp-opnd `rbp (* 8 (frame-var->index triv)))
                    triv
                    )))

        (define expose-effect
            (lambda (effect)
                (match effect
                    [(set! ,var ,triv) (guard (not (list? triv)))
                        `(set! ,(expose-var var) ,(expose-triv triv))]
                    [(set! ,var (,binop ,triv1 ,triv2))
                        `(set! ,(expose-var var) (,binop ,(expose-triv triv1) ,(expose-triv triv2)))])))

        (define expose-tail
            (lambda (tail)
                (match tail
                    [(,triv)
                        `(,(expose-triv triv))]
                    [(begin ,effect* ... ,tail1)
                        (append `(begin) (my-map expose-effect effect*) `(,(expose-tail tail1)))])))

        ; helper function: zip two list together
        (define (zip label* tail*) 
            (if (or (null? label*) (null? tail*))
                `()
                (cons 
                    (list (car label*) `(lambda () ,(car tail*)))
                    (zip (cdr label*) (cdr tail*)))))

        (define expose-program
            (lambda (program)
                (match program
                    [(letrec ([,label* (lambda () ,tail1*)] ...) ,tail2)
                        `(letrec ,(zip label* (my-map expose-tail tail1*)) ,(expose-tail tail2))])))

        (expose-program program)))

;   flatten-program
;   no begin& letrec; add jump

(define flatten-program
    (lambda (program)     
        (define flat-tail
            (lambda (tail)
                (match tail
                    [(,triv)
                        (begin
                            ; triv -> jump
                            `((jump ,triv)))]
                    [(begin ,effect* ... ,tail1)
                        (begin
                            ; no need to modify effect, flatten tail1 recursively
                            (append effect* (flat-tail tail1)))])))

        ; helper function
        (define (flat-lambdas label* tail*) 
            (if (or (null? label*) (null? tail*))
                `()
                (append 
                    `(,(car label*))
                    (flat-tail (car tail*))
                    (flat-lambdas (cdr label*) (cdr tail*)))))

        (define flat-program
            (lambda (program)
                (match program
                    [(letrec ([,label* (lambda () ,tail1*)] ...) ,tail2)
                        (append `(code) (flat-tail tail2) (flat-lambdas label* tail1*))])))
        
        (flat-program program)
    ))


(define generate-statement
    (lambda (statement)
        (match statement
            [(set! ,var1 ,int64) (guard (int64? int64))
                (emit `movq int64 var1)]
            [(set! ,var1 ,var2) (guard (register? var2))
                (emit `movq var2 var1)]
            [(set! ,var1 (,binop ,var1_ ,int32)) (guard (int32? int32))
                (cond 
                    [(eq? binop `+) (emit `addq int32 var1)]
                    [(eq? binop `-) (emit `subq int32 var1)]
                    [(eq? binop `*) (emit `imulq int32 var1)])]
            [(set! ,var1 (,binop ,var1_ ,var2)) (guard (register? var2))
                (cond 
                    [(eq? binop `+) (emit `addq var2 var1)]
                    [(eq? binop `-) (emit `subq var2 var1)]
                    [(eq? binop `*) (emit `imulq var2 var1)])])))


;   generate-x86-64
;   statements -> x86-64 instructions

(define generate-x86-64
    (lambda (program)
        (define which-binop
			(lambda (binop)
                (cond
                    [(eq? binop `+) 'addq]
                    [(eq? binop `-) 'subq]
                    [(eq? binop `*) `imulq]
                    [(eq? binop `logand) `andq]
                    [(eq? binop `logor) `orq]
                    [(eq? binop `sra) `sarq])))
        
        (define generate-statement
            (lambda (statement)
                (match statement
                    [(jump ,opnd) (emit-jump 'jmp opnd)] ; jmp
                    [(set! ,reg ,label) (guard (label? label)) ; leaq
                        (emit 'leaq label reg)]
                    [,label (guard (label? label)) ; label
                        (emit-label label)]
                    [(set! ,var ,opnd) (guard (not (list? opnd))) ; movq
                        (emit 'movq opnd var)]
                    [(set! ,var1 (,binop ,var1_ ,opnd)) ; binops
                        (emit (which-binop binop) opnd var1)])))
                        
        (define generate-program
            (lambda (program)
                (match program
                    [(code ,statement+ ...)
                        (for-each generate-statement statement+)])))

        (emit-program (generate-program program))))