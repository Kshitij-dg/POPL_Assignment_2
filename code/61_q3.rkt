#lang racket/base

;; (inorder-values tree) -> list of the tree's values in inorder
;;                          (left subtree, node, right subtree).
;; tree is either '() or a three-element list (value left right).
;;
;; Base case:  '()  ->  '().
;; Case 1: left subtree is empty -> the root value comes first, followed
;;         by the inorder values of the right subtree.
;; Case 2: left subtree is non-empty -> do a right rotation
;;           (v (lv ll lr) r)  ==>  (lv ll (v lr r))
;;         and recurse on the rotated tree. A right rotation never changes
;;         the inorder sequence, and each one strictly shrinks the root's
;;         left subtree, so case 1 is eventually reached. This avoids
;;         needing append or an accumulator helper.
(define (inorder-values tree)
  (cond
    ((null? tree) '())
    ((null? (cadr tree))
     (cons (car tree) (inorder-values (caddr tree))))
    (else
     (let ((left (cadr tree)))
       (inorder-values
        (list (car left)              ; new root: the left child's value
              (cadr left)             ; the left child keeps its left subtree
              (list (car tree)        ; the old root moves down to the right
                    (caddr left)      ; it takes the left child's right subtree
                    (caddr tree)))))))) ; and keeps its own right subtree

;; (preorder-values tree) -> list of the tree's values in preorder
;;                           (node, left subtree, right subtree).
;; tree is either '() or a three-element list (value left right).
;;
;; Internally, a node whose value slot holds '() is a "visited" node: its
;; own value has already been output, so its preorder is just
;; preorder(left) followed by preorder(right). Real values are numbers or
;; symbols, never '(), so the marker cannot be confused with real data.
;;
;; Base case:  '()  ->  '().
;; Case 1: unvisited node (v l r) -> output v, then continue with the
;;         visited node ('() l r).
;; Case 2: visited node with empty left ('() () r) -> continue with r.
;; Case 3: visited node with non-empty left ('() (lv ll lr) r) -> rotate to
;;           (lv ll ('() lr r))
;;         Both trees give lv, ll, lr, r in that order, so the preorder
;;         is unchanged.
(define (preorder-values tree)
  (cond
    ((null? tree) '())
    ((not (null? (car tree)))
     (cons (car tree)
           (preorder-values (list '() (cadr tree) (caddr tree)))))
    ((null? (cadr tree))
     (preorder-values (caddr tree)))
    (else
     (let ((left (cadr tree)))
       (preorder-values
        (list (car left)              ; left child's value (or marker) becomes root
              (cadr left)             ; its left subtree is unchanged
              (list '()               ; a visited node holds what comes after:
                    (caddr left)      ;   the left child's right subtree, then
                    (caddr tree)))))))) ;   the original right subtree