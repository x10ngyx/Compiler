(define (deep-copy obj)
    (cond
        ((null? obj) '())
        ((pair? obj) (cons (deep-copy (car obj)) (deep-copy (cdr obj))))
        (else obj)))

;   verify-scheme
;   do nothing

(define (verify-scheme x) x) 

;   uncover-frame-conflict
;   add frame-conflict-graph for each body

(define (uncover-frame-conflict program)
    ; dangerous variable
    ; deep-copy before used
    (define fcg `())

    (define (uncover-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[uncover-body -> bd1*])] ...) ,[uncover-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (uncover-body body)
        (match body
            [(locals ,local* ,tl)
                (begin
                    (set! fcg `((,local*) ...))
                    (uncover-tail tl)
                    `(locals ,local* (frame-conflict ,(deep-copy fcg) ,tl)))]))

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
            [(if ,pr ,[uncover-tail -> ls_tl1] ,[uncover-tail -> ls_tl2])
                (uncover-pred pr (union ls_tl1 ls_tl2))]
            [(begin ,ef* ... ,[uncover-tail -> ls_tl])
                (uncover-effect* ef* ls_tl)]
            [(,tr ,loc* ...)
                (try-to-add tr (filter loc*))]))

    ; (pred live-set) -> (ls)
    (define (uncover-pred pred live-set)
        (match pred
            [(true) live-set]
            [(false) live-set]
            [(if ,pr1 ,pr2 ,pr3)
                (let ([ls_pr2 (uncover-pred pr2 live-set)]
                      [ls_pr3 (uncover-pred pr3 live-set)])
                    (uncover-pred pr1 (union ls_pr2 ls_pr3)))]
            [(begin ,ef* ... ,pr)
                (let ([ls_pr (uncover-pred pr live-set)])
                    (uncover-effect* ef* ls_pr))]
            [(,relop ,tr1 ,tr2)
                (try-to-add tr1 (try-to-add tr2 live-set))]))
    
    ; (effect live-set) -> (ls)
    (define (uncover-effect effect live-set)
        (match effect
            [(nop) live-set]
            [(begin ,ef1* ... ,ef2)
                (let ([ls_ef2 (uncover-effect ef2 live-set)])
                    (uncover-effect* ef1* ls_ef2))]
            [(if ,pr ,ef1 ,ef2)
                (let ([ls_ef1 (uncover-effect ef1 live-set)]
                      [ls_ef2 (uncover-effect ef2 live-set)])
                    (uncover-pred pr (union ls_ef1 ls_ef2)))]
            [(set! ,v (,binop ,tr1 ,tr2))
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (frame-var? v) (uvar? v)) (add-conflict v ls) `())
                        (try-to-add tr1 (try-to-add tr2 ls))))]
            [(set! ,v ,tr)
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (frame-var? v) (uvar? v)) (add-conflict v (difference ls `(,tr))) `())
                        (try-to-add tr ls)))]))
    
    (uncover-program program))

;   introduce-allocation-forms
;   add ulocals & locate

(define (introduce-allocation-forms program)
    (define (introduce-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[introduce-body -> bd1*])] ...) ,[introduce-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (introduce-body body)
        (match body
            [(locals ,local* ,tl)
                `(locals ,local*
                    (ulocals ()
                        (locate () ,tl)))]))   
    
    (introduce-program program))

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
                        (values `(set! ,v ,tr) `())])]))

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
            [(if ,pr ,[uncover-tail -> ls_tl1] ,[uncover-tail -> ls_tl2])
                (uncover-pred pr (union ls_tl1 ls_tl2))]
            [(begin ,ef* ... ,[uncover-tail -> ls_tl])
                (uncover-effect* ef* ls_tl)]
            [(,tr ,loc* ...)
                (try-to-add tr (filter loc*))]))

    ; (pred live-set) -> (ls)
    (define (uncover-pred pred live-set)
        (match pred
            [(true) live-set]
            [(false) live-set]
            [(if ,pr1 ,pr2 ,pr3)
                (let ([ls_pr2 (uncover-pred pr2 live-set)]
                      [ls_pr3 (uncover-pred pr3 live-set)])
                    (uncover-pred pr1 (union ls_pr2 ls_pr3)))]
            [(begin ,ef* ... ,pr)
                (let ([ls_pr (uncover-pred pr live-set)])
                    (uncover-effect* ef* ls_pr))]
            [(,relop ,tr1 ,tr2)
                (try-to-add tr1 (try-to-add tr2 live-set))]))
    
    ; (effect live-set) -> (ls)
    (define (uncover-effect effect live-set)
        (match effect
            [(nop) live-set]
            [(begin ,ef1* ... ,ef2)
                (let ([ls_ef2 (uncover-effect ef2 live-set)])
                    (uncover-effect* ef1* ls_ef2))]
            [(if ,pr ,ef1 ,ef2)
                (let ([ls_ef1 (uncover-effect ef1 live-set)]
                      [ls_ef2 (uncover-effect ef2 live-set)])
                    (uncover-pred pr (union ls_ef1 ls_ef2)))]
            [(set! ,v (,binop ,tr1 ,tr2))
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (register? v) (uvar? v)) (add-conflict v ls) `())
                        (try-to-add tr1 (try-to-add tr2 ls))))]
            [(set! ,v ,tr)
                (let ([ls (try-to-delete v live-set)])
                    (begin
                        (if (or (register? v) (uvar? v)) (add-conflict v (difference ls `(,tr))) `())
                        (try-to-add tr ls)))]))
    
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
                [(,tr ,loc* ...) `(,(f tr env) ,loc* ...)])))

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
                    (if (eq? (f v env) (f tr env))
                        `(nop)
                        `(set! ,(f v env) ,(f tr env)))])))
                    
    
    ; helper function: find x in env
    (define (f x env)
        (if (and (uvar? x) (assq x env))
            (cadr (assq x env))
            x))
    
    (finalize-program program));   discard-call-live
;   in tail: (triv loc*) -> (triv)

(define (discard-call-live program)
    (define (discard-program program)
        (match program
            [(letrec ([,lb* (lambda () ,[discard-body -> bd1*])] ...) ,[discard-body -> bd2])
                `(letrec ([,lb* (lambda () ,bd1*)] ...) ,bd2)]))

    (define (discard-body body)
        (match body
            [(locate ([,uv* ,reg*] ...) ,[discard-tail -> tl])
                `(locate ([,uv* ,reg*] ...) ,tl)]))   

    (define (discard-tail tail)
        (match tail
            [(begin ,ef* ... ,[discard-tail -> tl])
                `(begin ,ef* ... ,tl)]
	        [(if ,pr ,[discard-tail -> tl1] ,[discard-tail -> tl2])
	             `(if ,pr ,tl1 ,tl2)]
	        [(,tr ,loc* ...)  `(,tr)]))    
    
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
                    (if (eq? (f v env) (f tr env))
                        `(nop)
                        `(set! ,(f v env) ,(f tr env)))])))
    
    ; helper function: find x in env
    (define (f x env)
        (if (and (uvar? x) (assq x env))
            (cadr (assq x env))
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


