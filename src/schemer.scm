(load "lib/match.scm")
(load "lib/helpers.scm")

(define verify-scheme 
    (lambda (x) x))

;;; translate-statement: accept a statement, return the code

(define translate-statement
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

;;; generate-x86-64: accept a program, return the code

(define generate-x86-64
    (lambda (program) 
        (match program
            [(begin ,statement+ ...)
                (emit-program (for-each translate-statement statement+))]
            )))