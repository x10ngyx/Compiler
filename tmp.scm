(define (deep-copy obj)
    (cond
        ((null? obj) '())
        ((pair? obj) (cons (deep-copy (car obj)) (deep-copy (cdr obj))))
        (else obj)))

;   verify-scheme
;   do nothing

(define (verify-scheme x) x) 

;   remove-complect-opera*
;   using set!, make all occurrences of value -> triv

(define (remove-complex-opera* program)
    (define (remove-program program)
        (match program
            [(letrec ([,lb* (lambda ,uv** ,[remove-body -> bd1*])] ...) ,[remove-body -> bd2])
                `(letrec ([,lb* (lambda ,uv** ,bd1*)] ...) ,bd2)]))

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
                (remove-helper binop val1 val2)]
            [(,val1 ,val2* ...)
                (let-values ([(set* call uv*) (remove-helper2 (cons val1 val2*))])
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
                (remove-helper relop val1 val2)]))
    
    (define (remove-effect effect)
        (match effect
            [(nop) (values `(nop) `())]
            [(begin ,[remove-effect -> ef1* uv*-ef1*] ... ,[remove-effect -> ef2 uv*-ef2])
                (values (make-begin `(,ef1* ... ,ef2)) (apply append uv*-ef2 uv*-ef1*))]
            [(if ,[remove-pred -> pr uv*-pr] ,[remove-effect -> ef1 uv*-ef1] ,[remove-effect -> ef2 uv*-ef2])
                (values `(if ,pr ,ef1 ,ef2) (append uv*-pr uv*-ef1 uv*-ef2))]
            [(set! ,uv ,[remove-value -> val uv*-val])
                (values `(set! ,uv ,val) uv*-val)]
            [(,val1 ,val2* ...)
                (let-values ([(set* call uv*) (remove-helper2 (cons val1 val2*))])
                    (values (make-begin `(,set* ... ,call)) uv*))]))
    
    (define (remove-value value)
        (match value
            [(if ,[remove-pred -> pr uv*-pr] ,[remove-value -> val1 uv*-val1] ,[remove-value -> val2 uv*-val2])
                (values `(if ,pr ,val1 ,val2) (append uv*-pr uv*-val1 uv*-val2))]
            [(begin ,[remove-effect -> ef* uv*-ef*] ... ,[remove-value -> val uv*-val])
                (values (make-begin `(,ef* ... ,val)) (apply append uv*-val uv*-ef*))]
            [(,binop ,val1 ,val2) (guard (memq binop `(+ - * logand logor sra)))
                (remove-helper binop val1 val2)]
            [(,val1 ,val2* ...)
                (let-values ([(set* call uv*) (remove-helper2 (cons val1 val2*))])
                    (values (make-begin `(,set* ... ,call)) uv*))]
            [,tr (values tr `())]))
    
    (define (remove-helper op val1 val2)
        (cond
            [(and (not (list? val1)) (not (list? val2)))
                (values `(,op ,val1 ,val2) `())]
            [(and (not (list? val1)) (list? val2))
                (let-values ([(new-val2 uv*-val2) (remove-value val2)])
                    (let ([uv2 (unique-name 'rco)])
                        (values `(begin (set! ,uv2 ,new-val2)
                                        (,op ,val1 ,uv2))
                                (cons uv2 uv*-val2))))]
            [(and (list? val1) (not (list? val2)))
                (let-values ([(new-val1 uv*-val1) (remove-value val1)])
                    (let ([uv1 (unique-name 'rco)])
                        (values `(begin (set! ,uv1 ,new-val1)
                                        (,op ,uv1 ,val2))
                                (cons uv1 uv*-val1))))]
            [(and (list? val1) (list? val2))
                (let-values ([(new-val1 uv*-val1) (remove-value val1)]
                             [(new-val2 uv*-val2) (remove-value val2)])
                    (let ([uv1 (unique-name 'rco)]
                          [uv2 (unique-name 'rco)])
                        (values `(begin (set! ,uv1 ,new-val1)
                                        (set! ,uv2 ,new-val2)
                                        (,op ,uv1 ,uv2))
                                (append (list uv1 uv2) uv*-val1 uv*-val2))))]))

    (define (remove-helper2 value*)
        (if (null? value*)
            (values `() `() `())
            (let-values ([(set* call uv*) (remove-helper2 (cdr value*))])
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
;   (set! uvar value) -> (set! uvar triv) / (set! uvar (binop triv1 triv2))

(define (flatten-set! program)
    (define (flat-program program)
        (match program
            [(letrec ([,lb* (lambda ,uv** ,[flat-body -> bd1*])] ...) ,[flat-body -> bd2])
                `(letrec ([,lb* (lambda ,uv** ,bd1*)] ...) ,bd2)]))

    (define (flat-body body)
        (match body
            [(locals ,uv* ,[flat-tail -> tl])
                `(locals ,uv* ,tl)]))
    
    (define (flat-tail tail)
        (match tail
            [(if ,[flat-pred -> pr] ,[flat-tail -> tl1] ,[flat-tail -> tl2])
                `(if ,pr ,tl1 ,tl2)]
            [(begin ,[flat-effect -> ef*] ... ,[flat-tail -> tl])
                (make-begin `(,ef* ... ,tl))]
            [(,binop ,tr1 ,tr2) (guard (memq binop `(+ - * logand logor sra))) tail]
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
            [(,tr1 ,tr2* ...) effect]))
    
    (define (flat-value value uvar)
        (match value
            [(if ,[flat-pred -> pr] ,val1 ,val2)
                `(if ,pr ,(flat-value val1 uvar) ,(flat-value val2 uvar))]
            [(begin ,[flat-effect -> ef*] ... ,val)
                (make-begin `(,ef* ... ,(flat-value val uvar)))]
            [(,binop ,tr1 ,tr2) (guard (memq binop `(+ - * logand logor sra)))
                `(set! ,uvar (,binop ,tr1 ,tr2))]
            [(,tr1 ,tr2* ...)
                `(set! ,uvar (,tr1 ,tr2* ...))]
            [,tr `(set! ,uvar ,tr)]))

    (flat-program program))

;   impose-calling-conventions
;   add set!* for caller and callee

(define (impose-calling-conventions program)
    (define (impose-program program)
        (match program
            [(letrec ([,lb* (lambda ,uv** ,bd1*)] ...) ,bd2)
                (let* ([new-bd1* (map impose-body bd1* uv**)]
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
                              (,uv-rp ,frame-pointer-register ,return-value-register)))]
            [(,tr1 ,tr2* ...) 
                (let* ([loc* (para->loc tr2* parameter-registers 0)]
                       [set* `((set! ,loc* ,tr2*) ...)]
                       [new-set* (fv-first set*)]
                       [new-tl (make-begin `(,new-set* ...
                                             (set! ,return-address-register ,uv-rp)
                                             (,tr1 ,frame-pointer-register ,return-address-register ,loc* ...)))])
                    new-tl)]
            [,tr 
                (make-begin `((set! ,return-value-register ,tr)
                              (,uv-rp ,frame-pointer-register ,return-value-register)))]))
    
    (define (impose-pred pred)
        (match pred
            [(true) pred]
            [(false) pred]
            [(if ,[impose-pred -> pr1] ,[impose-pred -> pr2] ,[impose-pred -> pr3])
                `(if ,pr1 ,pr2 ,pr3)]
            [(begin ,[impose-effect -> ef*] ... ,[impose-pred -> pr])
                (make-begin `(,ef* ... ,pr))]
            [(,relop ,tr1 ,tr2) pred]))
    
    (define (impose-effect effect)
        (match effect
            [(nop) effect]
            [(begin ,[impose-effect -> ef1*] ... ,[impose-effect -> ef2])
                (make-begin `(,ef1* ... ,ef2))]
            [(if ,[impose-pred -> pr] ,[impose-effect -> ef1] ,[impose-effect -> ef2])
                `(if ,pr ,ef1 ,ef2)]
            [(set! ,uv (,binop ,tr1 ,tr2)) (guard (memq binop `(+ - * logand logor sra)))
                effect]
            [(set! ,uv (,tr1 ,tr2* ...))
                (make-begin (list (non-tail-call tr1 tr2*) `(set! ,uv ,return-value-register)))]
            [(set! ,uv ,tr) effect]
            [(,tr1 ,tr2* ...) (non-tail-call tr1 tr2*)]))

    (define (non-tail-call func para*) (match func [,x ; in order to use ...
        (let* ([rp-label (unique-label `return-label)]
               [loc* (non-tail-para->loc para* parameter-registers)]
               [nfv* (difference loc* registers)]
               [set* `((set! ,loc* ,para*) ...)]
               [new-set* (fv-first set*)]
               [call (make-begin `(,new-set* ...
                                   (set! ,return-address-register ,rp-label)
                                   (,func ,frame-pointer-register ,return-address-register ,loc* ...)))])
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

;   uncover-frame-conflict
;   add frame-conflict-graph for each body

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
            [(set! ,v (,binop ,tr1 ,tr2))
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (frame-var? v) (uvar? v)) (add-conflict v ls) `())
                        (try-to-add tr1 (try-to-add tr2 ls))))]
            [(set! ,v ,tr)
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (frame-var? v) (uvar? v)) (add-conflict v (difference ls `(,tr))) `())
                        (try-to-add tr ls)))]
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
;   assign frame location for uv-nfv.x

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
            (cons (list (car nfv*) (index->frame-var (+ n 1 cnt)))
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
            [(if ,pr ,[assign-tail -> tl1] ,[assign-tail -> tl2]) `(if ,pr ,tl1 ,tl2)]
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
            [(set! ,v (,binop ,tr1 ,tr2)) `(set! ,v (,binop ,tr1 ,tr2))]
            [(set! ,v ,tr) `(set! ,v ,tr)]
            [(return-point ,lb ,tl)
                (make-begin
					`((set! ,frame-pointer-register (+ ,frame-pointer-register ,(ash (+ 1 n) align-shift)))
					  (return-point ,lb ,tl)
					  (set! ,frame-pointer-register (- ,frame-pointer-register ,(ash (+ 1 n) align-shift)))))]))
    
    (assign-program program))

;   finalize-frame-locations
;   discard location, r.8 -> fv10, locate form remains

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
                [(set! ,v (,binop ,tr1 ,tr2))
                    `(set! ,((f env) v) (,binop ,((f env) tr1) ,((f env) tr2)))]
                [(set! ,v ,tr)
                    (if (eq? ((f env) v) ((f env) tr))
                        `(nop)
                        `(set! ,((f env) v) ,((f env) tr)))]
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
;   rewrite set! & (triv) 

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
            [(set! ,v (,binop ,tr1 ,tr2))
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (register? v) (uvar? v)) (add-conflict v ls) `())
                        (try-to-add tr1 (try-to-add tr2 ls))))]
            [(set! ,v ,tr)
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (register? v) (uvar? v)) (add-conflict v (difference ls `(,tr))) `())
                        (try-to-add tr ls)))]
            [(return-point ,lb ,tl) (uncover-tail tl)]))
    
    (uncover-program program))

;   assign-registers
;   based on the register-conflict-graph, assign uvars to registers

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
            [(return-point ,lb ,[discard-tail -> tl]) `(return-point ,lb ,tl)]))
    
    (discard-program program))

;   finalize-locations
;   discard location, r.8 -> rax

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
                [(set! ,v (,binop ,tr1 ,tr2))
                    `(set! ,((f env) v) (,binop ,((f env) tr1) ,((f env) tr2)))]
                [(set! ,v ,tr)
                    (if (eq? ((f env) v) ((f env) tr))
                        `(nop)
                        `(set! ,((f env) v) ,((f env) tr)))]
                [(return-point ,lb ,[(makefunc-tail env) -> tl])
                    `(return-point ,lb ,tl)])))
    
    ; helper function: find x in env
    (define (f env)
        (lambda (x)
            (if (and (uvar? x) (assq x env))
                (cadr (assq x env))
                x)))
    
    (finalize-program program));   expose-frame-var

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
                (values `(set! ,loc (,binop ,tr1 ,tr2)) offset)]
            [(set! ,[(expose-triv offset) -> loc] ,[(expose-triv offset) -> tr])
                (values `(set! ,loc ,tr) offset)]
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

;   expose-basic-blocks
;   'basic' blocks and 'jump' at the end of each block

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