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

;;;; Helper Functions--------------------------------------------------

;; More functions
