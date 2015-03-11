
;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("//" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit "_" "-" "?")))
      make-symbol)
    (number (digit (arbno digit)) make-number)))

(define the-grammar
  '((program ((arbno class-decl) expression) a-program)

;;;;;;;;;;;;;;; Class declarations ;;;;;;;;;;;;;;;;;;;

    (class-decl                         
      ("class" identifier
         (arbno "member" identifier)
         (arbno method-decl)
         ";")
      class-declaration)

    (method-decl
      ("method" identifier 
        "("  (separated-list identifier ",") ")" ; method ids
        expression 
        )
      a-method-decl)

    ;; Expressions using classes ;;

    (expression 
      ("new" identifier "(" (separated-list expression ",") ")")
      new-object-exp)

    (expression
      ("send" expression identifier
        "("  (separated-list expression ",") ")")
      method-app)


    ;; Basic expressions and primitives ;;

    (expression (number) lit-exp)
    (expression (identifier) var-exp)   
    (expression
      (primitive "(" (separated-list expression ",") ")")
      primapp-exp)
    (expression
      ("if" expression "then" expression "else" expression)
      if-exp)
   (expression
      ("let" (arbno  identifier "=" expression) "in" expression)
      let-exp)
    (expression
      ("proc" "(" (separated-list identifier ",") ")" expression)
      proc-exp)
    (expression
      ("(" expression (arbno expression) ")")
      call-exp)
    (expression
      ("letrec"
        (arbno identifier "(" (separated-list identifier ",") ")"
          "=" expression)
        "in" expression)
      letrec-exp)
    
    (expression ("set" identifier "=" expression) varassign-exp)
    (expression
      ("begin" expression (arbno ";" expression) "end")
      begin-exp)

    (primitive ("+")     add-prim)
    (primitive ("-")     subtract-prim)
    (primitive ("*")     mult-prim)
    (primitive ("add1")  incr-prim)
    (primitive ("sub1")  decr-prim)
    (primitive ("zero?") zero-prim)
    (primitive ("list") list-prim)
    (primitive ("cons") cons-prim)
    (primitive ("null")  null-prim)
    (primitive ("car")  car-prim)
    (primitive ("cdr")  cdr-prim)
    (primitive ("null?") null?-prim)))

(sllgen:make-define-datatypes 
 the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser 
   the-lexical-spec the-grammar))

;;; Init Env;;;
(define init-env 
    (lambda ()
      (extend-env '(i v x) '(1 5 10) (empty-env))))

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : program -> expval;;
(define value-of-program 
  (lambda (pgm)
    (cases program pgm
      (a-program (c-decls exp)
        (init-class-declaration c-decls)
        (value-of exp (init-env))))))

;; value-of : expression env -> expval;;

(define value-of
  (lambda (exp env)
    (cases expression exp
      (lit-exp (datum) datum)
      (var-exp (id) (apply-env env id))
      (primapp-exp (prim rands)
        (let ((args (eval-rands rands env)))
          (apply-primitive prim args)))
      (if-exp (test-exp true-exp false-exp)
        (if (true-value? (value-of test-exp env))
          (value-of true-exp env)
          (value-of false-exp env)))
      
      (let-exp (ids rands body)
        (let ((args (eval-rands rands env)))
          (value-of body (extend-env ids args env))))
      
      (proc-exp (ids body)
        (proc-val ids body env))
      
      (call-exp (rator rands)
        (let ((proc (value-of rator env))
              (args (eval-rands      rands env)))
          (if (procval? proc)
            (apply-procedure proc args)
            (eopl:error 'value-of 
              "Attempt to apply non-procedure ~s" proc))))
      
      (letrec-exp (proc-names idss bodies letrec-body)
        (value-of letrec-body
          (extend-env-rec proc-names idss bodies env)))
      
      (varassign-exp (id rhs-exp)
        (setref!
          (apply-env-ref env id)
          (value-of rhs-exp env))
        8812)
      
      (begin-exp (exp1 exps)
        (let loop ((acc (value-of exp1 env))
                   (exps exps))
          (cond ((null? exps) acc)
            (else (value-of (begin-exp (car exps) (cdr exps)) env)))))

      ;; Expressions using classes;;
      
      (new-object-exp (class-name rands)
        (let ((args (eval-rands rands env))
              (obj (new-object class-name)))
          (method-apply
            'initialize obj args)
          obj))
      
      (method-app (obj-exp method-name rands)
        (let ((args (eval-rands rands env))
              (obj (value-of obj-exp env)))
          (method-apply
            method-name obj args)))

      )))
      
;;;;; Helper Functions ;;;;;;;;;
(define eval-rands
  (lambda (exps env)
    (map
      (lambda (exp) (value-of exp env))
      exps)))

(define apply-primitive
  (lambda (prim args)
    (cases primitive prim
      (add-prim  () (+ (car args) (cadr args)))
      (subtract-prim () (- (car args) (cadr args)))
      (mult-prim  () (* (car args) (cadr args)))
      (incr-prim  () (+ (car args) 1))
      (decr-prim  () (- (car args) 1))
      (zero-prim () (if (zero? (car args)) 1 0))
      (list-prim () args)
      (null-prim () '())
      (car-prim () (car (car args)))
      (cdr-prim () (cdr (car args)))
      (cons-prim () (cons (car args) (cadr args)))
      (null?-prim () (if (null? (car args)) 1 0)))))

;;;;;;;;;;;;;;;; booleans ;;;;;;;;;;;;;;;;

;; true-value? : number -> bool
(define true-value?
  (lambda (x)
    (not (zero? x))))

        
;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

(define-datatype procval procval?
  (proc-val 
    (ids (list-of symbol?)) 
    (body expression?)
    (env environment?)))

;; apply-procedure : procval list-of-expval -> expval
;;  Evaluates the body of a procedure given the actual arguments

(define apply-procedure
  (lambda (proc args)
    (cases procval proc
      (proc-val (ids body env)
        (value-of body (extend-env ids args env))))))
               
;;;;;;;;;;;;;;;; references ;;;;;;;;;;;;;;;;

(define-datatype reference reference?
  (a-ref
    (position integer?)
    (vec vector?)))

;; deref : reference -> expval
;;  Returns the content of a variable reference


(define deref 
  (lambda (ref)
    (cases reference ref
      (a-ref (pos vec)
             (vector-ref vec pos)))))

;; setref! : reference expval -> number
;; Creating the reference to a varible.


(define setref! 
  (lambda (ref val)
    (cases reference ref
      (a-ref (pos vec)
        (vector-set! vec pos val)))
    1))

;;;;;;;;;;;;;;;; environments ;;;;;;;;;;;;;;;;


(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
    (syms (list-of symbol?))
    (vec vector?)
    (env environment?)))

;; empty-env : -> env
;;  Creates an empty environment


(define empty-env
  (lambda ()
    (empty-env-record)))

;; extend-env : list-of-sym list-of-expval env -> env
;;  Creates an extended environment


(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (list->vector vals) env)))


;; extend-env-recursively : list-of-sym list-of-list-of-sym
;;                          list-of-expresssion env -> env


(define extend-env-rec (lambda (
         proc-name id body old-env)
  (letrec
      ((rec-env
        (lambda (sym)
          (if (eqv? proc-name sym)
              (procedure
               id
               body
               rec-env)
(apply-env old-env sym)))))
rec-env)
))

;;; Extend-env-refs :
;;; List-of-symbol vector env -> env


(define extend-env-refs
  (lambda (syms vec env)
    (extended-env-record syms vec env)))

;; Apply-env-ref : env sym -> reference
;; Extracts a variable's reference from an environment

(define apply-env-ref
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
        (eopl:error 'apply-env-ref "No binding for ~s" sym))
      (extended-env-record (syms vals env)
        (let ((pos (find-pos sym syms)))
          (if (number? pos)
              (a-ref pos vals)
              (apply-env-ref env sym)))))))

;; apply-env : env sym -> expval
;;  Extracts a variable's value (the on in the variable's reference) from an environment

(define apply-env
  (lambda (env sym)
    (deref (apply-env-ref env sym))))

;;;;;;;;;;;Environment helper functions;;;;;;;;;;;;;

(define find-pos 
  (lambda (sym los)
    (l-find-pos sym los)))

(define l-find-pos
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pdc list)
    (cond
      ((null? list) #f)
      ((pdc (car list)) 0)
      (else (let ((list-index-r (list-index pdc (cdr list))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))



;;;;;;;;;;;;;;;; objects ;;;;;;;;;;;;;;;;

(define-datatype object object? 
  (an-object
    (class-name symbol?)
    (fields vector?)))

;; new-object : sym -> object
;;  Given a class name, creates an instance of the class
(define new-object                      
  (lambda (class-name)
    (an-object
      class-name
      (make-vector (length (helper_classmemberid (lookupclass-inenvironment class-name)))))))


;;;;;;;;;;;;;;;; classes ;;;;;;;;;;;;;;;;

;; Now we distinguish *classes* from *class declarations*.
;; Elaboration constructs class record from the tree of class
;; declarations in the original program.

(define-datatype class class?
  (a-class
    (class-name symbol?)  
    (members (list-of symbol?))
    (methods method-environment?)))

(define init-class-declaration
  (lambda (class-declarations)
    (for-each class-declare class-declarations)))

;; class-declare : class-decl -> 
;; Register one class from one class declaration.
(define class-declare
  (lambda (c-decl)
          (let ((members  (helper_members-id c-decl))) 
          (add-class-in-env
          (a-class
            (helper_class-name c-decl)
             members
            (map
             (lambda (m-decl)
             (a-method m-decl members))
             (helper_method-decls c-decl)))))))


;;;;;;;;;;;;;;;; methods ;;;;;;;;;;;;;;;;

;; We also distinguish *methods* from *method declarations*.

(define-datatype method method?
  (a-method
    (m-decl method-decl?)
    (field-ids (list-of symbol?))))

;;;;;;;;;;;; Find method in from the class declaration and apply ;;;;;;;;;
(define method-apply           
  (lambda (m-name self args)
    (let ((method (lookup-method m-name 
                    (length args)
                    (helper_classmethod (lookupclass-inenvironment (helper_classname self))))))
      (if (method? method)
          (apply-method method self args)
          (eopl:error 'method-apply
                      "No method for name ~s and argcount ~s" m-name (length args))))))

(define apply-method                    
  (lambda (method self args)
    (value-of 
     (helper_body (helper_methoddecl method)) 
     (extend-env
      (helper_methodid method) 
      args
      (extend-env-refs         
       (helper_methodmemberids method) 
       (helper_objectmembers self)
       (empty-env))))))



;;;;;;;;;;;;;;;; method environments ;;;;;;;;;;;;;;;;

(define method-environment? (list-of method?)) 

(define lookup-method
  (lambda (m-name num-args methods)
    (cond
      ((null? methods) #f)
      ((and (eqv? m-name (helper_methodname (car methods)))
            (= num-args (length (helper_methodid (car methods)))))
       (car methods))
      (else (lookup-method m-name num-args (cdr methods))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Class Environments ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define class-env '())

(define add-class-in-env
  (lambda (class)
    (set! class-env (cons class class-env)))) ;;Adds new class to the previous class environment;;

(define lookupclass-inenvironment                    
  (lambda (name)
      (helper_lookupclass-inenvironment name class-env)))

;;;;;;;;;;;;;;;;;;;;; Helper Funbctions for Class Environemnt ;;;;;;;;;;;;;;;;;;;;;;;;;

(define helper_lookupclass-inenvironment (lambda (name env)  
  (cond
        ((null? env) (eopl:error 'look-up-class
                       "Unknown class ~s" name))
        ((eqv? (helper_lookupclass (car env)) name) (car env))
        (else ( helper_lookupclass-inenvironment name (cdr env))))))
(define helper_lookupclass
  (lambda (c-struct)
    (cases class c-struct
      (a-class (class-name  members methods)
        class-name))))

(define helper_classmemberid
  (lambda (c-struct)
    (cases class c-struct
      (a-class (class-name  members methods)
        members))))

(define helper_classmethod
  (lambda (c-struct)
    (cases class c-struct
      (a-class (class-name  field-ids methods)
        methods))))

(define helper_classname
  (lambda (obj)
    (cases object obj
      (an-object (class-name fields)
        class-name))))

(define helper_objectmembers
  (lambda (obj)
    (cases object obj
      (an-object (class-decl fields)
        fields))))


(define helper_class-name
  (lambda (c-decl)
    (cases class-decl c-decl
      (class-declaration (class-name members method-decls)
        class-name))))

(define helper_members-id
  (lambda (c-decl)
    (cases class-decl c-decl
      (class-declaration (class-name members method-decls)
        members))))

(define helper_method-decls
  (lambda (c-decl)
    (cases class-decl c-decl
      (class-declaration (class-name members method-decls)
        method-decls))))

(define helper_method-name
  (lambda (m)
    (cases method-decl m
      (a-method-decl (method-name ids body) method-name))))

(define helper_id
  (lambda (m)
    (cases method-decl m
      (a-method-decl (method-name ids body) ids))))

(define helper_body
  (lambda (m)
    (cases method-decl m
      (a-method-decl (method-name ids body) body))))

(define helper_method-names
  (lambda (mds)
    (map helper_method-name mds)))


(define helper_methoddecl
  (lambda (m)
    (cases method m
      (a-method (meth-decl  members) meth-decl))))


(define helper_methodmemberids
  (lambda (m)
    (cases method m
      (a-method (method-decl  field-ids) field-ids))))

(define helper_methodname
  (lambda (method)
    (helper_method-name (helper_methoddecl method))))



(define helper_methodid
  (lambda (method)
    (helper_id (helper_methoddecl method))))

;;;;;;;;;;;;;;;;;;;;;;;; Run the program ;;;;;;;;;;;;;;;;;;;
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))
