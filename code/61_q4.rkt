#lang racket/base

;; (my-length lst) -> non-negative integer
;; Input: a proper list whose elements are atoms or nested lists.
;; Output: the number of top-level elements. A nested list counts as one
;; element, and its contents are never looked at.
;; Tail-recursive (named let):
;;   invariant: counted = number of elements already removed from lst,
;;              so counted + (length of remaining) = (length of lst)
;;   base case: remaining is '() -> counted is the answer (0 for '()).
(define (my-length lst)
  (let loop ((remaining lst) (counted 0))
    (if (null? remaining)
        counted
        (loop (cdr remaining) (+ counted 1)))))