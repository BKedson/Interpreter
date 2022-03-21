#lang racket

(require "simpleParser.rkt")

;;;; ********************************************************
;;;;   Aracelli Doescher (ahd47) and Brandon Kedson (bjk118)
;;;;   CSDS 345
;;;;   Simple Language Interpreter Part 2
;;;; ********************************************************

;; interpret reads in an input file consisting of a java-like language, parses it, and returns a specified return value
(define interpret
  (lambda (filename)
    (evaluate (parser filename)
              (newstate)
              (newbreaklambda)
              (newcontinuelambda)
              (newreturnlambda)
              (newthrowlambda))))

;; evaluate searches a parse tree and returns the return value
(define evaluate
  (lambda (tree state break continue return throw)
          (returnvalue (Mstate (firstexp tree) state
                       (newnextlambda tree break continue return throw) break continue return throw)))) ; (evaluate (restof tree) 

;;;; Mappings-------------------------------------------------------------

;; Mvalue takes an expression and finds the value of that expression
(define Mvalue
  (lambda (exp state next break continue return throw)
    (cond
      [(number? exp) exp]
      [(eq? 'true exp) #t]
      [(eq? 'false exp) #f]
      [(and (not (list? exp)) (var? exp (vars-list-all state)))
            (valueof exp (vars-list-all state) (values-list-all state))] ; checks if expression is a variable
      [(not (list? exp)) (error 'novar "Variable not declared")]
      [(null? exp) exp]
      [(and (eq? (operator exp) '-) (null? (rightoperand exp)))
            (- (Mvalue (leftoperand exp) state next break continue return throw))] ; unary minus
      [(eq? (operator exp) '-) (- (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '+) (+ (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '*) (* (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '/) (quotient (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '%) (remainder (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '==) (eq? (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '!=) (not (eq? (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw)))]
      [(eq? (operator exp) '<) (< (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '>) (> (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '<=) (<= (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '>=) (>= (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(and (eq? (operator exp) '&&) (boolean? (Mvalue (leftoperand exp) state next break continue return throw))
            (boolean? (Mvalue (rightoperand exp) state next break continue return throw)))
       (and (Mvalue (leftoperand exp) state next break continue return throw)
            (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(and (eq? (operator exp) '||) (boolean? (Mvalue (leftoperand exp) state next break continue return throw))
            (boolean? (Mvalue (rightoperand exp) state next break continue return throw)))
       (or (Mvalue (leftoperand exp) state next break continue return throw)
           (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(and (eq? (operator exp) '!) (boolean? (Mvalue (leftoperand exp) state next break continue return throw)))
       (not (Mvalue (leftoperand exp) state next break continue return throw))]
      [(eq? (operator exp) '=) (valueof (leftoperand exp) (vars-list (Mstate exp state next break continue return throw))
            (values-list (Mstate exp state next break continue return throw)) next break continue return throw)] ; returns the value that was assigned to the specified variable
      [else (error 'badexp "Bad expression")])))

;; Mstate takes an expression and modifies the state accordingly
(define Mstate
  (lambda (exp state next break continue return throw)
    (cond
      [(number? exp) state]
      [(eq? 'true exp) state]
      [(eq? 'false exp) state]
      [(and (not (list? exp)) (var? exp (vars-list-all state))) state] ; checks if expression is a variable
      [(not (list? exp)) (error 'novar "Variable not declared")]
      [(null? exp) (next state)]
      [(and (eq? (operator exp) 'var) (null? (Mvalue (val exp) state next break continue return throw)))
            (next (declare (varname exp) state))] ; no value specified (only varname)
      [(eq? (operator exp) 'var) (next (assign (varname exp)
            (Mvalue (val exp) state next break continue return throw) (declare (varname exp) (updatedstate exp state next break continue return throw))))]
      [(eq? (operator exp) '=) (next (assign (varname exp)
            (Mvalue (val exp) state next break continue return throw) (updatedstate exp state next break continue return throw)))]
      ; block
      [(eq? (operator exp) 'begin) (Mstate (firstexp (restof exp)) (addnewlayer state)
            (blocknextlambda (restof exp) next break continue return throw) (newblockbreaklambda break) (newblockcontinuelambda continue) return throw)]
      ; if
      [(and (eq? (operator exp) 'if) (Mvalue (condition exp) state next break continue return throw))
       (Mstate (then exp) (Mstate (condition exp) state next break continue return throw) next break continue return throw)]
      [(and (eq? (operator exp) 'if) (null? (else-statement exp))) (next state)]
      [(eq? (operator exp) 'if) (Mstate (else-statement exp)
            (Mstate (condition exp) state next break continue return throw) next break continue return throw)]
      ; while
      [(eq? (operator exp) 'while)  (loop exp state next (lambda (s) (next s))
            (whilecontinuelambda exp next break continue return throw) return throw)]
      ;try
      [(eq? (operator exp) 'try)
            (Mstate (tryblock exp) state
               (trynext exp next break continue return throw)
               (trybreak exp break continue return throw)
               (trycontinue exp break continue return throw)
               (tryreturn exp next break continue return throw)
               (trythrow exp next break continue return throw))]
      ; break
      [(eq? (operator exp) 'break) (break (removelayer state))]
      ; continue
      [(eq? (operator exp) 'continue) (continue (removelayer state))]
      ; return
      [(eq? (operator exp) 'return) (return (returnstate (returnexp exp) state next break continue return throw))]
      ; throw
      [(eq? (operator exp) 'throw) (throw state (throwval exp))]
      ; values
      [(and (eq? (operator exp) '-) (null? (rightoperand exp))) (updatedstate exp state next break continue return throw)] ; unary minus
      [(eq? (operator exp) '-) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '+) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '*) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '/) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '%) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '==) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '!=) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '<) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '>) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '<=) (updatedstate exp state next break continue return throw)]
      [(eq? (operator exp) '>=) (updatedstate exp state next break continue return throw)]
      [(and (eq? (operator exp) '&&) (boolean? (Mvalue (leftoperand exp) state next break continue return throw))
            (boolean? (Mvalue (rightoperand exp) state next break continue return throw)))
       (updatedstate exp state next break continue return throw)]
      [(and (eq? (operator exp) '||) (boolean? (Mvalue (leftoperand exp) state next break continue return throw))
            (boolean? (Mvalue (rightoperand exp) state next break continue return throw)))
       (updatedstate exp state next break continue return throw)]
      [(and (eq? (operator exp) '!) (boolean? (Mvalue (leftoperand exp) state next break continue return throw)))
       (updatedstate exp state next break continue return throw)]
      [else (error 'badstate "Bad state")])))

;;;; Helper Functions--------------------------------------------------

;; declare adds a new variable to the list of variables stored in the current scope of the state and sets its value to
;; null; if the variable is already declared in the current layer, it will overwrite the value
(define declare
 (lambda (var state)
   (if (var? var (vars-list state))
     (assign var (declaredval) state)
     (newdeclarestate var state))))

;; assign adds a value to the values-list in the state for a corresponding variable; if the variable
;; is already assigned, it will overwrite the value
(define assign
  (lambda (var val state)
    (if (var? var (vars-list-all state))
        (newassignstate var val state)
        (error 'badassign "Bad assignment"))))
      
;; var? searches through the given vars-list and returns #t if the variable has been declared
(define var?
  (lambda (exp vars-list)
    (cond
      [(null? exp) (error 'badexp "Bad expression")]
      [(null? vars-list) #f]
      [(eq? (first-variable vars-list) exp) #t]
      [else (var? exp (restof vars-list))])))
    

;; valueof searches through the current scope and returns the associated value of a given var
(define valueof
  (lambda (exp vars-list values-list)
    (cond
      [(null? exp) (error 'badexp "Bad expression")]
      [(or (null? vars-list) (null? values-list)) (error 'novar "Variable not declared")]
      [(and(eq? (first-variable vars-list) exp) (null? (first-value values-list))) (error 'noinit "Variable was never initialized")]
      [(eq? (first-variable vars-list) exp) (first-value values-list)]
      [else (valueof exp (restof vars-list) (restof values-list))])))

;; setvalue assigns a value to a given var and returns the updated values-list; returns an error if the var has not been declared
(define setvalue
  (lambda (var val vars-list values-list)
    (cond
      [(null? var) (error 'badexp "Bad expression")]
      [(null? vars-list) (error 'novar "Variable not declared")]
      [(eq? (first-variable vars-list) var) (cons val (restof values-list))]
      [else (cons (first-value values-list) (setvalue var val (restof vars-list) (restof values-list)))])))

;;;; Abstractions----------------------------------------------------------

;; newnextlambda returns a base lambda function for the next continuation
(define newnextlambda
  (lambda (tree break continue return throw)
    (lambda (s)
      (if (null? (restof tree))
                    (removelayer s)
                    (Mstate (firstexp (restof tree)) s
                            (newnextlambda (restof tree) break continue return throw) break continue return throw)))))

;; newbreaklambda returns a base lambda function for the break continuation
(define newbreaklambda
  (lambda ()
    (lambda (s) (error 'noloop "Break cannot be run outside of a loop"))))

;; newcontinuelambda returns a base lambda function for the continue continuation
(define newcontinuelambda
  (lambda ()
    (lambda (s) (error 'noloop "Break cannot be run outside of a loop"))))

;; newreturnlambda returns a base lambda function for the return continuation
(define newreturnlambda
  (lambda ()
    (lambda (v)
      (cond
        [(and (boolean? (returnvalue v)) (returnvalue v)) 'true]
        [(and (boolean? (returnvalue v)) (not (returnvalue v))) 'false]
        [else v]))))

;; newthrowlambda returns a base lambda function for the throw continuation
(define newthrowlambda
  (lambda  ()
    (lambda (s e) (error 'throwwithoutcatch "Error thrown without catch"))))

;; blocknextlambda returns the base lambda function for when the program is inside a block
;; If the code inside the block has already executed, or something has broken out of a block,
;; then it runs the next continuation from outside the block. Otherwise, its next line is the
;; next line of code inside the block
(define blocknextlambda
  (lambda (exp next break continue return throw)
    (lambda (s)
      (if (null? (restof exp))
        (next (removelayer s))
        (Mstate (firstexp (restof exp)) s
                (blocknextlambda (restof exp) next break continue return throw) break continue return throw)))))

;; newblockbreaklambda removes the current layer when we call break inside a block
(define newblockbreaklambda
  (lambda (break)
    (lambda (s)
      (break (removelayer s)))))

;; newblockcontinuelambda removes the current layer when we call continue inside a block
(define newblockcontinuelambda
  (lambda (continue)
    (lambda (s)
      (continue (removelayer s)))))

;; whilecontinuelambda is the base lambda function for when inside a while loop
(define whilecontinuelambda
  (lambda (exp next break continue return throw)
    (lambda (s)
      (Mstate exp s next break continue return throw))))

;; removelayer removes the top layer from the state
(define removelayer
  (lambda (s)
    (cdr s)))

;; currentlayer returns the top layer of the state
(define currentlayer
  (lambda (state)
    (car state)))

;; throwval returns the value being thrown
(define throwval
  (lambda (exp)
    (if (null? (restof exp))
        '()
        (cadr exp))))

;; trynext returns the lambda function used for the next continuation when inside a try block
(define trynext
  (lambda (exp next break continue return throw)
    (lambda (s)
      (if (null? (finallyblock exp))
          (next s)
          (Mstate (finallyblock exp) s next break continue return throw)))))

;; trybreak returns the lambda function used for the break continuation when inside a try block
(define trybreak
  (lambda (exp break continue return throw)
    (lambda (s)
      (if (null? (finallyblock exp))
          s
          (Mstate (finallyblock exp) s break break continue return throw)))))

;; trycontinue returns the lambda function used for the continue continuation when inside a try block
(define trycontinue
  (lambda (exp break continue return throw)
    (lambda (s)
       (if (null? (finallyblock exp))
           s
           (Mstate (finallyblock exp) s continue break continue return throw)))))

;; tryreturn returns the lambda function used for the return continuation when inside a try block
(define tryreturn
  (lambda (exp next break continue return throw)
    (lambda (v)
      (if (null? (finallyblock exp))
          v
          (Mstate (finallyblock exp) v next break continue return throw)))))

;; trythrow returns the lambda function used for the throw continuation when inside a try block
(define trythrow
  (lambda (exp next break continue return throw)
    (lambda (s e)
      (cond
        [(and (null? (catchblock exp)) (null? (finallyblock exp)))
         (throw s e)]
        [(null? (catchblock exp))
         (Mstate (finallyblock exp) s
              (lambda (s1) (throw s1 e)) (lambda (s1) (throw s1 e)) (lambda (s1) (throw s1 e))
              (lambda (v) (throw s e)) throw)]
        [(null? (finallyblock exp))
         (Mstate (catchblock exp) (assign (catchvar exp) e
         (declare (catchvar exp) s)) (trynext exp next break continue return throw)
         (trybreak exp break continue return throw) (trycontinue exp break continue return throw)
         (tryreturn exp next break continue return throw) throw)]
        [else (Mstate (catchblock exp) (assign (catchvar exp) e
              (declare (catchvar exp) s)) (trynext exp next break continue return throw)
              (trybreak exp break continue return throw) (trycontinue exp break continue return throw)
              (tryreturn exp next break continue return throw)
              (lambda (s1 e1) (Mstate (finallyblock exp) s1
              (lambda (s2) (throw s2 e1)) (lambda (s2) (throw s2 e1)) (lambda (s2) (throw s2 e1))
              (lambda (v) (throw s1 e1)) throw)))]))))

;; returns the "try" block of code from a try-catch-finally expression
(define tryblock
  (lambda (exp)
    (cons 'begin (cadr exp))))

;; returns the "catch" block of code from a try-catch-finally expression
(define catchblock
  (lambda (exp)
    (if (null? (cdaddr exp))
        '()
        (cons 'begin (cadr (cdaddr exp))))))

;; returns the "finally" block of code from a try-catch-finally expression
(define finallyblock
  (lambda (exp)
    (if (null? (cadddr exp))
    '()
    (cons 'begin (cadr (cadddr exp))))))

;; returns the name of the exception passed to the catch block
(define catchvar
  (lambda (block)
    (caar (cdaddr block))))

;; addnewlayer adds a new layer onto the state
(define addnewlayer
  (lambda (state)
    (cons '(() ()) state)))

;; loop runs each iteration of a while loop
(define loop
  (lambda (exp state next break continue return throw)
    (if (Mvalue (condition exp) state next break continue return throw)
        (Mstate (body exp) state (lambda (s) (Mstate exp s next break continue return throw)) break continue return throw)
        (next state))))

;; updatedstate returns the modified state and accounts for side effects (Part 1 only. Side effects were not implemented in Part 2)
(define updatedstate
  (lambda (exp state next break continue return throw)
    (cond
      [(or (eq? 'var (operator exp)) (eq? '= (operator exp))) (Mstate (rightoperand exp) state next break continue return throw)]
      [(null? (rightoperand exp)) (Mstate (leftoperand exp) state next break continue return throw)]
      [else (Mstate (rightoperand exp) state (lambda (s) (Mstate (leftoperand exp) s next break continue return throw)) break continue return throw)])))

;; restof finds the rest of a given list
(define restof
  (lambda (lis)
    (cdr lis)))

;; firstexp finds the first expression in the parse tree
(define firstexp
  (lambda (tree)
    (car tree)))

;; newstate generates an initial state for the program
(define newstate
  (lambda ()
      '((() ()))))

;; returnstate returns the state with an added return component
(define returnstate
  (lambda (exp state next break continue return throw)
    (cons state (cons (Mvalue exp state next break continue return throw) '()))))

;; operator finds the operator of an expression
(define operator
  (lambda (exp)
    (if (null? exp)
        '()
        (car exp))))

;; leftoperand finds the left operand of a given expression
(define leftoperand
  (lambda (exp)
    (if (null? (cdr exp))
        '()
        (cadr exp))))

;; rightoperand finds the right operand of a given expression
(define rightoperand
  (lambda (exp)
    (if (null? (cdr (cdr exp)))
        '()
        (caddr exp))))

;; varname finds the variable name in a given expression
(define varname
  (lambda (exp)
    (if (null? (cdr exp))
        '()
        (cadr exp))))

;; val finds the value expression in an assignment statement
(define val
  (lambda (exp)
    (if (null? (cdr (cdr exp)))
        '()
        (caddr exp))))

;; returnexp finds the return expression of a given expression
(define returnexp
  (lambda (exp)
    (if (null? (cdr exp))
        '()
        (cadr exp))))

;; returnvalue finds the return component of the state
(define returnvalue
  (lambda (state)
    (cond
      [(null? state) '()]
      [(and (not (list? state)) (boolean? state) state) 'true]
      [(and (not (list? state)) (boolean? state)) 'false]
      [(not (list? state)) state]
      [(list? (currentlayer state)) (returnvalue (restof state))]
      [else (car state)])))

;; declaredval returns the initial value of a declared var
(define declaredval
  (lambda ()
    '()))

;; newdeclarestate generates a new state based on a declaration
(define newdeclarestate
  (lambda (var state)
     (if (null? (restof state))
        (cons (list (cons var (vars-list state)) (cons (declaredval) (values-list state))) '())
        (cons (list (cons var (vars-list state)) (cons (declaredval) (values-list state))) (restof state)))))

;; newassignstate generates a new state based on an assignment
(define newassignstate
  (lambda (var val state)
    (cond
      [(null? var) (error 'badexp "Bad expression")]
      [(null? state) (error 'novar "Variable not declared")]
      [(not (list? (car state))) (error 'novar "Variable not declared")]
      [(var? var (vars-list state)) (cons (list (vars-list state) (setvalue var val (vars-list state) (values-list state))) (restof state))]
      [else (cons (currentlayer state) (newassignstate var val (restof state)))])))

;; condition finds the condition of an if or while expression
(define condition
  (lambda (exp)
    (if (null? (cdr exp))
        '()
        (cadr exp))))

;; then finds the statement that is executed if the condition is true
(define then
  (lambda (exp)
    (if (null? (cdr (cdr exp)))
        '()
        (caddr exp))))

;; else-statement finds the statement that is executed if the condition is false
(define else-statement
  (lambda (exp)
    (if (null? (cdr (cdr (cdr exp))))
        '()
        (cadddr exp))))

;; body finds the body of the loop to be executed
(define body
  (lambda (exp)
    (if (null? (cdr (cdr exp)))
        '()
        (caddr exp))))

;; vars-list finds the list of variables in the current layer of the state
(define vars-list
  (lambda (state)
    (if (null? state)
        state
        (caar state))))

;; vars-list-all finds a list of all the variables on all layers in scope in the state
(define vars-list-all
  (lambda (state)
    (if (null? state)
        state
        (append (vars-list state) (vars-list-all (removelayer state))))))

;; first-variable finds the first variable in the variables list from the given vars-list
(define first-variable
  (lambda (vars-list)
    (if (null? vars-list)
        '()
        (car vars-list))))

;; values-list finds the list of values in the current layer of the state
(define values-list
  (lambda (state)
    (if (null? vars-list)
        state
        (cadar state))))

;; values-list-all finds all the values on all layers in scope in the state
(define values-list-all
  (lambda (state)
    (if (null? state)
        state
        (append (values-list state) (values-list-all (removelayer state))))))

;; first-value finds the first value in the values list from the from the given values-list
(define first-value
  (lambda (values-list)
    (if (null? values-list)
        '()
        (car values-list))))
