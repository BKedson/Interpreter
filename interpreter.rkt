#lang racket

(require "simpleParser.rkt")

;;;; ********************************************************
;;;;   Aracelli Doescher (ahd47) and Brandon Kedson (bjk118)
;;;;   CSDS 345
;;;;   Simple Language Interpreter 1
;;;; ********************************************************

(define interpret
  (lambda (filename)
    (evaluate (parser filename))))

(define evaluate
  (lambda (tree state)
    (cond
      [(null? tree) state])))

;;;; Mappings-------------------------------------------------------------
(define Mvalue
  (lambda (exp state)
    (cond
      ((number? exp) exp)
      ((boolean? exp) exp)
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
      ((and (eq? (operator exp) '!) (boolean? (Mvalue (leftoperand) state))) (not (Mvalue (leftoperand exp) state)))
      (else (error 'badexp "Bad expression")))))

;; declare, assign, if, while, return
(define Mstate
  (lambda (exp state)
    (cond
      [(null? exp) exp]
      [(and (eq? (operator exp) 'var) (null? (Mvalue (rightoperand exp) state))) (declare (leftoperand exp) state)]
      [(eq? (operator exp) 'var) (assign (leftoperand exp) (Mvalue (rightoperand exp) state) (declare (leftoperand exp) state))]
      [else (error 'badstate "Bad state")])))

;;;; Abstractions----------------------------------------------------------
(define operator
  (lambda (exp)
    (if (null? exp)
        '()
        (car exp))))

(define leftoperand
  (lambda (exp)
    (if (null? (cdr exp))
        '()
        (cadr exp))))

(define rightoperand
  (lambda (exp)
    (if (null? (cdr (cdr exp)))
        '()
        (caddr exp))))

(define vars-list
  (lambda (state)
    (if (null? state)
        state
        (car state))))

(define first-variable
  (lambda (vars-list)
    (if (null? vars-list)
        '()
        (car vars-list))))

(define values-list
  (lambda (state)
    (if (null? vars-list)
        state
        (cadr state))))

  (define first-value
  (lambda (values-list)
    (if (null? values-list)
        '()
        (car values-list))))

;;;; Helper Functions--------------------------------------------------
(define declare
 (lambda (var state)
   (if (var? var (vars-list state))
     (assign var '() state)
     (cons (cons var (vars-list state)) (cons (cons '() (values-list state)) '())))))

(define assign
  (lambda (var val state)
    (if (var? var (vars-list state))
        (cons (vars-list state) (cons (setvalue var val (vars-list state) (values-list state)) '()))
        (error 'badassign "Bad assignment"))))
      

(define var?
  (lambda (exp vars-list)
    (cond
      [(null? exp) (error 'badexp "Bad expression")]
      [(null? vars-list) #f]
      [(eq? (first-variable vars-list) exp) #t]
      [else (var? exp (cdr vars-list))]))) ; ask Connamacher?

(define valueof
  (lambda (exp vars-list values-list)
    (cond
      [(null? exp) (error 'badexp "Bad expression")]
      [(null? vars-list) (error 'novar "Variable not declared")]
      [(eq? (first-variable vars-list) exp) (first-value values-list)]
      [else (valueof exp (cdr vars-list) (cdr values-list))])))

(define setvalue
  (lambda (var val vars-list values-list)
    (cond
      [(null? var) (error 'badexp "Bad expression")]
      [(null? vars-list) (error 'novar "Variable not declared")]
      [(eq? (first-variable vars-list) var) (cons val (cdr values-list))]
      [else (cons (first-value values-list) (setvalue var val (cdr vars-list) (cdr values-list)))])))

;; More functions
