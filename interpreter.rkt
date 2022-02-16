#lang racket

(require "simpleParser.rkt")

;;;; ********************************************************
;;;;   Aracelli Doescher (ahd47) and Brandon Kedson (bjk118)
;;;;   CSDS 345
;;;;   Simple Language Interpreter 1
;;;; ********************************************************

;; interpret reads in an input file consisting of a java-like language, parses it, and returns a specified value
(define interpret
  (lambda (filename)
    (evaluate (parser filename) '(() ()))))

;; evaluate generates a state based on a parse tree
(define evaluate
  (lambda (tree state)
      (if (null? tree)
          state
          (evaluate (cdr tree) (Mstate (car tree) state)))))

; do the thing whereby you only return return
; also make return return true and false, not #t and #f

;;;; Mappings-------------------------------------------------------------

;; Mvalue takes an expression and finds the value of that expression
(define Mvalue
  (lambda (exp state)
    (cond
      ((number? exp) exp)
      ((eq? 'true exp) #t)
      ((eq? 'false exp) #f)
      ((and (not (list? exp)) (var? exp (vars-list state))) (valueof exp (vars-list state) (values-list state)))
      ((null? exp) exp)
      ((and (eq? (operator exp) '-) (null? (rightoperand exp))) (- (Mvalue (leftoperand exp))))
      ((eq? (operator exp) '-) (- (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((eq? (operator exp) '+) (+ (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((eq? (operator exp) '*) (* (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((eq? (operator exp) '/) (quotient (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((eq? (operator exp) '%) (remainder (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((eq? (operator exp) '==) (eq? (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((eq? (operator exp) '!=) (not (eq? (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state))))
      ((eq? (operator exp) '<) (< (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((eq? (operator exp) '>) (> (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((eq? (operator exp) '<=) (<= (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((eq? (operator exp) '>=) (>= (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((and (eq? (operator exp) '&&) (boolean? (Mvalue (leftoperand exp) state)) (boolean? (Mvalue (rightoperand exp) state))) (and (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((and (eq? (operator exp) '||) (boolean? (Mvalue (leftoperand exp) state)) (boolean? (Mvalue (rightoperand exp) state))) (or (Mvalue (leftoperand exp) state) (Mvalue (rightoperand exp) state)))
      ((and (eq? (operator exp) '!) (boolean? (Mvalue (leftoperand exp) state))) (not (Mvalue (leftoperand exp) state)))
      ; ((eq? (operator exp) '=) (valueof (leftoperand exp) (vars-list (Mstate exp state)) (values-list (Mstate exp state)))) ; Maybe dumb, fix tomorrow?
      (else (error 'badexp "Bad expression")))))

;; Mstate takes an expression and modifies the state accordingly
(define Mstate
  (lambda (exp state)
    (cond
      [(null? exp) exp]
      [(and (eq? (operator exp) 'var) (null? (Mvalue (rightoperand exp) state))) (declare (leftoperand exp) state)]
      [(eq? (operator exp) 'var) (assign (leftoperand exp) (Mvalue (rightoperand exp) state) (declare (leftoperand exp) state))]
      [(eq? (operator exp) '=) (assign (leftoperand exp) (Mvalue (rightoperand exp) state) state)]
      [(and (eq? (operator exp) 'if) (Mvalue (condition exp) state)) (Mstate (then exp) state)]
      [(eq? (operator exp) 'if) (Mstate (else-statement exp) state)]
      [(and (eq? (operator exp) 'while) (Mvalue (condition exp) state)) (Mstate exp (Mstate (body exp) state))]
      [(eq? (operator exp) 'while) state]
      [(eq? (operator exp) 'return) (cons (vars-list state) (cons (cons (values-list state) '()) (cons (cons (Mvalue (leftoperand exp) state) '()) '())))]
      [else (error 'badstate "Bad state")])))

;;;; Abstractions----------------------------------------------------------

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

;; condition finds the conidition of an if or while expression
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

;; body finds the body of the loop to be executed
(define body
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

;;;; Helper Functions--------------------------------------------------

;; declare adds a new variable to the list of variables stored in the state and sets its value to
;; null; if the variable is already declared, it will overwrite the value
(define declare
 (lambda (var state)
   (if (var? var (vars-list state))
     (assign var '() state)
     (cons (cons var (vars-list state)) (cons (cons '() (values-list state)) '())))))

;; assign adds a value to the values-list in the state for a corresponding variable; if the variable
;; is already assigned, it will overwrite the value
(define assign
  (lambda (var val state)
    (if (var? var (vars-list state))
        (cons (vars-list state) (cons (setvalue var val (vars-list state) (values-list state)) '()))
        (error 'badassign "Bad assignment"))))
      
;; var? searches through the vars-list in the state and returns #t if the variable has been declared
(define var?
  (lambda (exp vars-list)
    (cond
      [(null? exp) (error 'badexp "Bad expression")]
      [(null? vars-list) #f]
      [(eq? (first-variable vars-list) exp) #t]
      [else (var? exp (cdr vars-list))]))) ; ask Connamacher?

;; valueof searches through the state and returns the associated value of a given var
(define valueof
  (lambda (exp vars-list values-list)
    (cond
      [(null? exp) (error 'badexp "Bad expression")]
      [(null? vars-list) (error 'novar "Variable not declared")]
      [(eq? (first-variable vars-list) exp) (first-value values-list)]
      [else (valueof exp (cdr vars-list) (cdr values-list))])))

;; setvalue assigns a value to a given var, and returns an error if the var has not been returned
(define setvalue
  (lambda (var val vars-list values-list)
    (cond
      [(null? var) (error 'badexp "Bad expression")]
      [(null? vars-list) (error 'novar "Variable not declared")]
      [(eq? (first-variable vars-list) var) (cons val (cdr values-list))]
      [else (cons (first-value values-list) (setvalue var val (cdr vars-list) (cdr values-list)))])))