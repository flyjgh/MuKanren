#lang racket

(require "./relational-float/mk-float.rkt")
(require "./relational-float/mk.rkt")

(define one '(0 (1 1 1 1 1 1 1) (0 0 0 0 0 0 0 1)))
(run 3 (q) (== 2 q))
