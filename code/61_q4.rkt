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

;; (my-map f lst) -> new list
;; Input: f, a one-argument function; lst, a proper list.
;; Output: a new list holding (f e) for each top-level element e of lst,
;; in the original order. lst itself is not changed.
;; Two tail-recursive phases (named lets), so the stack stays constant:
;;   collect: invariant: reversed-result holds f applied to every element
;;            already removed from lst, newest first.
;;            base case: remaining is '() -> go to phase 2.
;;   restore: invariant: result holds the elements already moved out of
;;            rev, back in original order.
;;            base case: rev is '() -> result is the answer ('() for '()).
(define (my-map f lst)
  (let collect ((remaining lst) (reversed-result '()))
    (if (null? remaining)
        ;; Phase 2: undo the reversal caused by consing onto the accumulator
        (let restore ((rev reversed-result) (result '()))
          (if (null? rev)
              result
              (restore (cdr rev) (cons (car rev) result))))
        ;; Phase 1: apply f to the next element, push it onto the accumulator
        (collect (cdr remaining)
                 (cons (f (car remaining)) reversed-result)))))

;; (make-inserter x len-ok?) -> function of one list
;; Input: x, an atom; len-ok?, a predicate on one number.
;; Output: a closure that takes a (possibly nested) list. For every list at
;; every level, including the top-level list, it inserts x at the front if
;; (len-ok? L) holds, where L is that list's ORIGINAL top-level length.
;; Atoms are returned unchanged.
;; Recursion (letrec, mutually recursive local closures):
;;   process-list: measure lst once, rebuild its elements with my-map, then
;;                 optionally cons x on the front.
;;                 base case: '() -> my-map gives '(), so the result is
;;                 (x) or () depending on (len-ok? 0).
;;   process-element: a list ('() or a pair) is handed to process-list; an
;;                    atom is returned as it is.
(define (make-inserter x len-ok?)
  (letrec ((process-list
            (lambda (lst)
              (let* ((original-length (my-length lst))              ; measured before any insertion
                     (processed (my-map process-element lst)))      ; recurse into sublists
                (if (len-ok? original-length)
                    (cons x processed)
                    processed))))
           (process-element
            (lambda (e)
              (if (or (pair? e) (null? e))
                  (process-list e)
                  e))))
    process-list))

;; (insert-if-short x lst n) -> new list
;; Input: x, an atom; lst, a proper, possibly nested list; n, an integer >= 0.
;; Output: lst with x inserted at the front of every list, at every level and
;; including lst itself, whose ORIGINAL top-level length is strictly less than n.
;; Not recursive itself: it builds a "length < n" predicate, passes it to
;; make-inserter, and applies the resulting inserter to lst. All traversal
;; is done inside make-inserter.
(define (insert-if-short x lst n)
  ((make-inserter x (lambda (len) (< len n))) lst))