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

;; (postorder-values tree) -> list of the tree's values in postorder
;;                            (left subtree, right subtree, node).
;; tree is either '() or a three-element list (value left right).
;;
;; Internally the function works on a "work list" written with the same
;; three-element shape: ('() item rest) means "first output the postorder of
;; item, then continue with rest". The '() in the value slot marks such a
;; work-list cell; real values are numbers or symbols, never '().
;;
;; Base case: '() (empty work list or empty tree) -> '().
;; A real tree is first wrapped as a one-item work list ('() tree '()).
;; For a work-list cell ('() item rest):
;;   - item is '()            -> skip it, continue with rest.
;;   - item is a work-list cell ('() a b)
;;                            -> flatten to ('() a ('() b rest)).
;;   - item is a leaf (v () ()) -> output v, continue with rest.
;;   - item is a node (v l r) -> replace it by three items in this order:
;;                               l, r, then the leaf (v () ()), so that v
;;                               is output after both subtrees.
(define (postorder-values tree)
  (cond
    ((null? tree) '())
    ((not (null? (car tree)))                 ; real tree: wrap it
     (postorder-values (list '() tree '())))
    (else
     (let ((item (cadr tree))
           (rest (caddr tree)))
       (cond
         ((null? item)
          (postorder-values rest))
         ((null? (car item))                  ; nested work-list cell: flatten
          (postorder-values
           (list '() (cadr item) (list '() (caddr item) rest))))
         ((and (null? (cadr item)) (null? (caddr item)))  ; leaf: output it
          (cons (car item) (postorder-values rest)))
         (else                                ; node: left, right, then root
          (postorder-values
           (list '() (cadr item)
                 (list '() (caddr item)
                       (list '() (list (car item) '() '()) rest))))))))))

;; (tree-height tree) -> height of tree.
;; tree is either '() or a three-element list (value left right).
;;
;; Base case: '()     -> 0  (the empty tree has height 0).
;; Recursive case: (v l r) -> 1 + the larger of the heights of l and r,
;;                            so a single node has height 1.
(define (tree-height tree)
  (if (null? tree)
      0
      (+ 1 (max (tree-height (cadr tree))
                (tree-height (caddr tree))))))

;; (leaf-count tree) -> number of leaves in tree.
;; tree is either '() or a three-element list (value left right).
;; A leaf is a node whose left and right subtrees are both '().
;;
;; Base case 1: '()            -> 0  (the empty tree has no leaves).
;; Base case 2: (v () ())      -> 1  (the node itself is a leaf).
;; Recursive case: (v l r)     -> leaves of l + leaves of r,
;;                                left subtree counted first.
(define (leaf-count tree)
  (cond
    ((null? tree) 0)
    ((and (null? (cadr tree)) (null? (caddr tree))) 1)
    (else
     (+ (leaf-count (cadr tree))
        (leaf-count (caddr tree))))))

;; (print-inorder tree) -> prints the inorder list of tree on one line.
;; tree is either '() or a three-element list (value left right).
;; Side effect: displays (inorder-values tree), e.g. (1 2 3 4 5 6 7),
;; followed by exactly one newline. An empty tree prints ().
(define (print-inorder tree)
  (begin
    (display (inorder-values tree))
    (newline)))

;; (print-all-traversals tree) -> prints three lines for tree:
;;   line 1: inorder list   (left, node, right)
;;   line 2: preorder list  (node, left, right)
;;   line 3: postorder list (left, right, node)
;; tree is either '() or a three-element list (value left right).
;; Each list is shown with display and followed by exactly one newline;
;; an empty tree prints () on all three lines.
(define (print-all-traversals tree)
  (begin
    (display (inorder-values tree))
    (newline)
    (display (preorder-values tree))
    (newline)
    (display (postorder-values tree))
    (newline)))

;; (print-height-and-leaves tree) -> prints (height leaf-count) on one line.
;; tree is either '() or a three-element list (value left right).
;; Height of '() is 0; a node's height is 1 + the larger subtree height.
;; Side effect: displays the two-element list (height leaves), followed by
;; exactly one newline. An empty tree prints (0 0); a single node (1 1).
(define (print-height-and-leaves tree)
  (begin
    (display (list (tree-height tree) (leaf-count tree)))
    (newline)))