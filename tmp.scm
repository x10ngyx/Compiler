(define op->inst
  (lambda (op)
    (case op
      [(+) 'addq]
      [(-) 'subq]
      [(*) 'imulq]
      [(logand) 'andq]
      [(logor) 'orq]
      [(sra) 'sarq]
      [(=) 'je]
      [(<) 'jl]
      [(<=) 'jle]
      [(>) 'jg]
      [(>=) 'jge]
      [else (error who "unexpected binop ~s" op)])))


;;; Takes assembly instruction and returns the opposite of it

(define inst->inst^
				  (lambda (inst)
				    (case inst
				      [(je) 'jne]
				      [(jl) 'jge]
				      [(jle) 'jg]
				      [(jg) 'jle]
				      [(jge) 'jl]
				)))


;;; Same as assignment 2 except modified to handle conditional jumps

(define-who generate-x86-64
  (lambda (x)
    (define Program
      (lambda (x)
        (match x
          [(code ,st* ...)
           (emit-program (for-each Stmt st*))])))
    (define Stmt
      (lambda (x)
        (match x
          [(jump ,target) (emit-jump 'jmp target)]
          [(if (,op ,x ,y) (jump ,lbl)) (begin (emit 'cmpq y x) (emit-jump (op->inst op) lbl))]
          [(if (not (,op ,x ,y)) (jump ,lbl)) (begin (emit 'cmpq y x) (emit-jump (inst->inst^ (op->inst op)) lbl))]
          [(set! ,v1 (,op ,v1 ,v2)) (emit (op->inst op) v2 v1)]
          [(set! ,v1 ,v2) (guard (label? v2)) (emit 'leaq v2 v1)]
					[(set! ,v1 ,v2) (emit 'movq v2 v1)]
          [,label (emit-label label)])))
    (Program x)))