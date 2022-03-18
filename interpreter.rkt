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

;; evaluate generates a state based on a parse tree and returns the return value
(define evaluate
  (lambda (tree state break continue return throw)
      (if (null? tree)
          '() ; (returnvalue state)
          (Mstate (firstexp tree) state (newnextlambda tree break continue return throw) break continue return throw)))) ; (evaluate (restof tree) 

;;;; Mappings-------------------------------------------------------------

;; Mvalue takes an expression and finds the value of that expression
(define Mvalue
  (lambda (exp state next break continue return throw)
    (cond
      [(number? exp) exp]
      [(eq? 'true exp) #t]
      [(eq? 'false exp) #f]
      [(and (not (list? exp)) (var? exp (vars-list state))) (valueof exp (vars-list state) (values-list state))] ; checks if expression is a variable
      [(not (list? exp)) (error 'novar "Variable not declared")]
      [(null? exp) exp]
      [(and (eq? (operator exp) '-) (null? (rightoperand exp))) (- (Mvalue (leftoperand exp) state next break continue return throw))] ; unary minus
      [(eq? (operator exp) '-) (- (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '+) (+ (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '*) (* (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '/) (quotient (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '%) (remainder (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '==) (eq? (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '!=) (not (eq? (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw)))]
      [(eq? (operator exp) '<) (< (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '>) (> (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '<=) (<= (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(eq? (operator exp) '>=) (>= (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(and (eq? (operator exp) '&&) (boolean? (Mvalue (leftoperand exp) state next break continue return throw)) (boolean? (Mvalue (rightoperand exp) state next break continue return throw)))
       (and (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(and (eq? (operator exp) '||) (boolean? (Mvalue (leftoperand exp) state next break continue return throw)) (boolean? (Mvalue (rightoperand exp) state next break continue return throw)))
       (or (Mvalue (leftoperand exp) state next break continue return throw) (Mvalue (rightoperand exp) (Mstate (leftoperand exp) state next break continue return throw) next break continue return throw))]
      [(and (eq? (operator exp) '!) (boolean? (Mvalue (leftoperand exp) state next break continue return throw))) (not (Mvalue (leftoperand exp) state next break continue return throw))]
      [(eq? (operator exp) '=) (valueof (leftoperand exp) (vars-list (Mstate exp state next break continue return throw)) (values-list (Mstate exp state next break continue return throw) next break continue return throw))] ; returns the value that was assigned to the specified variable
      [else (error 'badexp "Bad expression")])))

;; Mstate takes an expression and modifies the state accordingly
(define Mstate
  (lambda (exp state next break continue return throw)
    (cond
      [(number? exp) state] ; return? next? what?
      [(eq? 'true exp) state]
      [(eq? 'false exp) state]
      [(and (not (list? exp)) (var? exp (vars-list state))) state] ; checks if expression is a variable
      [(not (list? exp)) (error 'novar "Variable not declared")]
      [(null? exp) (next state)]
      [(and (eq? (operator exp) 'var) (null? (Mvalue (val exp) state next break continue return throw))) (next (declare (varname exp) state))] ; no value specified (only varname)
      [(eq? (operator exp) 'var) (next (assign (varname exp) (Mvalue (val exp) state next break continue return throw) (declare (varname exp) (updatedstate exp state next break continue return throw))))]
      [(eq? (operator exp) '=) (next (assign (varname exp) (Mvalue (val exp) state next break continue return throw) (updatedstate exp state next break continue return throw)))]

      ; if
      [(and (eq? (operator exp) 'if) (Mvalue (condition exp) state next break continue return throw))
       (Mstate (then exp) (Mstate (condition exp) state next break continue return throw) next break continue return throw)]
      [(eq? (operator exp) 'if) (Mstate (else-statement exp)  (Mstate (condition exp) state next break continue return throw) next break continue return throw)]

      ;(Mstate exp (Mstate (body exp)  (Mstate (condition exp) state)))]
      ; while
      ;[(and (eq? (operator exp) 'while) (Mvalue (condition exp) state))]
      [(eq? (operator exp) 'while)  (loop exp state next (lambda (s) (next s)) continue return throw)]
      ;(Mstate (condition exp) state

      ; break
      [(eq? (operator exp) 'break) (break state)]
      ; continue
      [(eq? (operator exp) 'continue) (continue state)]
      ; return
      [(eq? (operator exp) 'return) (return (returnvalue (returnexp exp) state next break continue return throw))]
      ; throw
      [(eq? (operator exp) 'throw) (throw state)]
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
      [(and (eq? (operator exp) '&&) (boolean? (Mvalue (leftoperand exp) state next break continue return throw)) (boolean? (Mvalue (rightoperand exp) state next break continue return throw)))
       (updatedstate exp state next break continue return throw)]
      [(and (eq? (operator exp) '||) (boolean? (Mvalue (leftoperand exp) state next break continue return throw)) (boolean? (Mvalue (rightoperand exp) state next break continue return throw)))
       (updatedstate exp state next break continue return throw)]
      [(and (eq? (operator exp) '!) (boolean? (Mvalue (leftoperand exp) state next break continue return throw))) (updatedstate exp state next break continue return throw)]
      [else (error 'badstate "Bad state")])))

;;;; Helper Functions--------------------------------------------------

;; declare adds a new variable to the list of variables stored in the state and sets its value to
;; null; if the variable is already declared, it will overwrite the value
(define declare
 (lambda (var state)
   (if (var? var (vars-list state))
     (assign var (declaredval) state)
     (newdeclarestate var state))))

;; assign adds a value to the values-list in the state for a corresponding variable; if the variable
;; is already assigned, it will overwrite the value
(define assign
  (lambda (var val state)
    (if (var? var (vars-list state))
        (newassignstate var val state)
        (error 'badassign "Bad assignment"))))
      
;; var? searches through the vars-list in the state and returns #t if the variable has been declared
(define var?
  (lambda (exp vars-list)
    (cond
      [(null? exp) (error 'badexp "Bad expression")]
      [(null? vars-list) #f]
      [(eq? (first-variable vars-list) exp) #t]
      [else (var? exp (restof vars-list))])))

;; valueof searches through the state and returns the associated value of a given var
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

;; newlambda returns a new function
(define newnextlambda
  (lambda (tree break continue return throw)
    (lambda (s)
      (if (null? (restof tree))
                    '()
                    (Mstate (car (restof tree)) s (newnextlambda (cdr tree) break continue return throw) break continue return throw)))))

(define newbreaklambda
  (lambda ()
    (lambda (s) s)))

(define newcontinuelambda
  (lambda ()
    (lambda (s) s)))

(define newreturnlambda
  (lambda ()
    (lambda (v)
      (cond
        [(and (boolean? v) v) 'true]
        [(and (boolean? v) (not v)) 'false]
        [else v]))))

(define newthrowlambda
  (lambda  ()
    (lambda (s) s)))

;; loop does something
(define loop
  (lambda (exp state next break continue return throw)
    (if (Mvalue (condition exp) state next break continue return throw)
        (Mstate (body exp) state (lambda (s) (Mstate exp s next break continue return throw)) break continue return throw)
        (next state))))

;; updatedstate returns the modified state and accounts for side effects
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
      '(() ())))

;; returnstate returns the state with an added return component
(define returnstate
  (lambda (exp state next break continue return throw)
    (cons (vars-list state) (cons (cons (values-list state) '()) (cons (cons (Mvalue (returnexp exp) state next break continue return throw) '()) '())))))

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
  (lambda (exp state next break continue return throw)
    (Mvalue exp state next break continue return throw)))

;; declaredval returns the initial value of a declared var
(define declaredval
  (lambda ()
    '()))

;; newdeclarestate generates a new state based on a declaration
(define newdeclarestate
  (lambda (var state)
    (list (cons var (vars-list state)) (cons (declaredval) (values-list state)))))

;; newassignstate generates a new state based on an assignment
(define newassignstate
  (lambda (var val state)
    (list (vars-list state) (setvalue var val (vars-list state) (values-list state)))))

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

;; vars-list finds the list of variables in the state
(define vars-list
  (lambda (state)
    (if (null? state)
        state
        (car state))))

;; first-variable finds the first variable in the variables list from the state
(define first-variable
  (lambda (vars-list)
    (if (null? vars-list)
        '()
        (car vars-list))))

;; values-list finds the list of values in the state
(define values-list
  (lambda (state)
    (if (null? vars-list)
        state
        (cadr state))))

;; first-value finds the first value in the values list from the state
(define first-value
  (lambda (values-list)
    (if (null? values-list)
        '()
        (car values-list))))
