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
  (lambda (tree)
    tree))

;;;; Mappings-------------------------------------------------------------
(define Mint
  (lambda (x)
    (cond
      ((number? x) x)
      ((null? x) x)
      ((and (eq? (operator x) '-) (null? (rightoperand x))) (- (Mint (leftoperand x))))
      ((eq? (operator x) '-) (- (Mint (leftoperand x)) (Mint (rightoperand x))))
      ((eq? (operator x) '+) (+ (Mint (leftoperand x)) (Mint (rightoperand x))))
      ((eq? (operator x) '*) (* (Mint (leftoperand x)) (Mint (rightoperand x))))
      ((eq? (operator x) '/) (quotient (Mint (leftoperand x)) (Mint (rightoperand x))))
      ((eq? (operator x) '%) (remainder (Mint (leftoperand x)) (Mint (rightoperand x))))
      (else (error 'badop "Bad operator")))))

(define Mboolean
  (lambda (exp)
    (cond
      ((boolean? exp) exp)
      ((null? exp) exp)
      ((eq? (operator exp) '==) (eq? (Mint (leftoperand exp)) (Mint (rightoperand exp))))
      ((eq? (operator exp) '!=) (not (eq? (Mint (leftoperand exp)) (Mint (rightoperand exp)))))
      ((eq? (operator exp) '<) (< (Mint (leftoperand exp)) (Mint (rightoperand exp))))
      ((eq? (operator exp) '>) (> (Mint (leftoperand exp)) (Mint (rightoperand exp))))
      ((eq? (operator exp) '<=) (<= (Mint (leftoperand exp)) (Mint (rightoperand exp))))
      ((eq? (operator exp) '>=) (>= (Mint (leftoperand exp)) (Mint (rightoperand exp))))
      ((eq? (operator exp) '&&) (and (Mboolean (leftoperand exp)) (Mboolean (rightoperand exp))))
      ((eq? (operator exp) '||) (or (Mboolean (leftoperand exp)) (Mboolean (rightoperand exp))))
      ((eq? (operator exp) '!) (not (Mboolean (leftoperand exp))))
      (else (error 'badop "Bad operator")))))

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

;;;; Helper Functions--------------------------------------------------

;; More functions
