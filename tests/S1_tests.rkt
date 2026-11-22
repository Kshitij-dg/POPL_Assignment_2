#lang racket/base
;; tests/S1_tests.rkt -- test suite for S1 (code/61_q3.rkt)
;; CS F301 Principles of Programming Languages, Assignment 2, Group 61.
;;
;; Run from the repository root:   racket tests/S1_tests.rkt
;; Exit code 0 when every test passes, 1 when any test fails.
;;
;; How it works (the solution file is never modified):
;;  1. The solution module is loaded into a fresh namespace with
;;     dynamic-require while stdout/stderr are captured, to check that
;;     loading the file prints nothing (the grader runs `racket 61_q3.rkt`).
;;  2. module->namespace gives access to the module's internal definitions
;;     without any `provide` (the same mechanism Racket's `enter!` uses).
;;  3. Each printing function is called with its output captured in a
;;     string and compared exactly: characters, line count, final newline,
;;     and a void return value (so a top-level call prints nothing extra).
;;  4. A static scan reads the solution's source and checks that it contains
;;     only definitions and uses only identifiers on the assignment's
;;     whitelist (plus its own function and variable names).
;;
;; This file is test infrastructure only. It may use racket/base features
;; (set!, printf, for/list, ...) that the solution itself must not use.

(require racket/runtime-path
         (for-syntax racket/base))   ; define-runtime-path needs phase-1 bindings

(define-runtime-path solution-path "../code/61_q3.rkt")

;; ---------------------------------------------------------------------------
;; Reporting
;; ---------------------------------------------------------------------------

(define passed 0)
(define failed 0)

(define (report! name ok? detail)
  (if ok?
      (begin (set! passed (+ passed 1))
             (printf "PASS  ~a\n" name))
      (begin (set! failed (+ failed 1))
             (printf "FAIL  ~a\n      ~a\n" name detail))))

(define (finish!)
  (printf "\nSummary: ~a passed, ~a failed\n" passed failed)
  (exit (if (= failed 0) 0 1)))

;; Check that (thunk) returns a value equal? to expected.
(define (check-value name thunk expected)
  (with-handlers ([exn:fail?
                   (lambda (e)
                     (report! name #f (format "raised an error: ~a" (exn-message e))))])
    (let ([actual (thunk)])
      (report! name (equal? actual expected)
               (format "expected ~s, got ~s" expected actual)))))

(define (count-newlines s)
  (let loop ([i 0] [n 0])
    (if (= i (string-length s))
        n
        (loop (+ i 1) (if (char=? (string-ref s i) #\newline) (+ n 1) n)))))

;; Check that (thunk) prints exactly expected-text, which has expected-lines
;; lines, every line ends with a newline, and the call returns void.
(define (check-output name thunk expected-text expected-lines)
  (with-handlers ([exn:fail?
                   (lambda (e)
                     (report! name #f (format "raised an error: ~a" (exn-message e))))])
    (let* ([port (open-output-string)]
           [result (parameterize ([current-output-port port]) (thunk))]
           [actual (get-output-string port)]
           [lines (count-newlines actual)]
           [ends-with-newline?
            (and (> (string-length actual) 0)
                 (char=? (string-ref actual (- (string-length actual) 1)) #\newline))])
      (report! name
               (and (string=? actual expected-text)
                    (= lines expected-lines)
                    ends-with-newline?
                    (void? result))
               (format "expected ~s (~a line(s)); got ~s (~a line(s), ends with newline: ~a, returns void: ~a)"
                       expected-text expected-lines actual lines
                       ends-with-newline? (void? result))))))

;; ---------------------------------------------------------------------------
;; 1. Load the solution and check that loading prints nothing
;; ---------------------------------------------------------------------------

(define base-ns (make-base-namespace))
(define load-out (open-output-string))
(define load-err (open-output-string))

(define loaded-ok?
  (with-handlers ([exn:fail?
                   (lambda (e)
                     (report! "solution file loads without error" #f (exn-message e))
                     #f)])
    (parameterize ([current-namespace base-ns]
                   [current-output-port load-out]
                   [current-error-port load-err])
      (dynamic-require solution-path #f))
    (report! "solution file loads without error" #t "")
    #t))

(unless loaded-ok? (finish!))

(report! "loading the solution prints nothing to stdout"
         (string=? (get-output-string load-out) "")
         (format "printed ~s" (get-output-string load-out)))
(report! "loading the solution prints nothing to stderr"
         (string=? (get-output-string load-err) "")
         (format "printed ~s" (get-output-string load-err)))

(define solution-ns
  (parameterize ([current-namespace base-ns])
    (module->namespace solution-path)))

;; Fetch a function from the solution; if it is missing, record a FAIL and
;; return a stub that raises an error, so the other tests still run.
(define (solution-function name)
  (with-handlers ([exn:fail?
                   (lambda (e)
                     (report! (format "solution defines ~a" name) #f (exn-message e))
                     (lambda args (error name "not defined in the solution")))])
    (let ([f (eval name solution-ns)])
      (report! (format "solution defines ~a" name) (procedure? f)
               (format "~a is not a procedure" name))
      f)))

(define inorder-values          (solution-function 'inorder-values))
(define preorder-values         (solution-function 'preorder-values))
(define postorder-values        (solution-function 'postorder-values))
(define tree-height             (solution-function 'tree-height))
(define leaf-count              (solution-function 'leaf-count))
(define print-inorder           (solution-function 'print-inorder))
(define print-all-traversals    (solution-function 'print-all-traversals))
(define print-height-and-leaves (solution-function 'print-height-and-leaves))

;; ---------------------------------------------------------------------------
;; 2. Static checks on the solution source
;; ---------------------------------------------------------------------------

;; Returns (cons first-line forms): the #lang line and every form after it.
(define (read-solution)
  (call-with-input-file solution-path
    (lambda (in)
      (let ([first-line (read-line in 'any)])
        (let loop ([forms '()])
          (let ([form (read in)])
            (if (eof-object? form)
                (cons first-line (reverse forms))
                (loop (cons form forms)))))))))

(define (elements x)                    ; elements of a (possibly improper) list
  (if (pair? x) (cons (car x) (elements (cdr x))) '()))

(define (param-names p)                 ; names in a parameter list
  (cond [(symbol? p) (list p)]
        [(pair? p) (append (param-names (car p)) (param-names (cdr p)))]
        [else '()]))

(define (binding-names bindings)        ; names in ((x e) ...)
  (for/list ([b (elements bindings)] #:when (and (pair? b) (symbol? (car b))))
    (car b)))

;; Every name the source binds with define, lambda, let, let* or letrec.
(define (binders-of form)
  (if (or (not (pair? form)) (eq? (car form) 'quote))
      '()
      (append
       (case (car form)
         [(define) (if (pair? (cadr form)) (param-names (cadr form)) (list (cadr form)))]
         [(lambda) (param-names (cadr form))]
         [(let let* letrec)
          (if (symbol? (cadr form))
              (cons (cadr form) (binding-names (caddr form)))   ; named let
              (binding-names (cadr form)))]
         [else '()])
       (apply append (map binders-of (elements form))))))

;; Every symbol used outside quoted data.
(define (symbols-used form)
  (cond [(symbol? form) (list form)]
        [(and (pair? form) (eq? (car form) 'quote)) '()]
        [(pair? form) (apply append (map symbols-used (elements form)))]
        [else '()]))

(define (dedupe xs)
  (let loop ([xs xs] [seen '()])
    (cond [(null? xs) (reverse seen)]
          [(memq (car xs) seen) (loop (cdr xs) seen)]
          [else (loop (cdr xs) (cons (car xs) seen))])))

;; car/cdr compositions up to four levels: car, cdr, caar, ..., cddddr.
(define (ad-strings n)
  (if (= n 0)
      '("")
      (for*/list ([rest (ad-strings (- n 1))] [c '("a" "d")])
        (string-append c rest))))

(define cxr-names
  (for*/list ([n '(1 2 3 4)] [s (ad-strings n)])
    (string->symbol (string-append "c" s "r"))))

;; The assignment's whitelist for S1 (S2's `read` is not allowed here).
(define allowed-names
  (append '(define lambda let let* letrec if cond else and or not begin quote
            cons list null? pair? eq? assq assoc
            + - * < > <= >= = max display newline)
          cxr-names))

(define public-names
  '(inorder-values preorder-values postorder-values tree-height leaf-count
    print-inorder print-all-traversals print-height-and-leaves))

(define source (read-solution))
(define source-forms (cdr source))

(report! "solution starts with #lang racket/base (no BOM)"
         (equal? (car source) "#lang racket/base")
         (format "first line is ~s" (car source)))

(report! "solution contains only definitions (no top-level calls)"
         (andmap (lambda (f) (and (pair? f) (eq? (car f) 'define))) source-forms)
         (format "non-definition forms: ~s"
                 (filter (lambda (f) (not (and (pair? f) (eq? (car f) 'define))))
                         source-forms)))

(define defined-names
  (for/list ([f source-forms] #:when (and (pair? f) (eq? (car f) 'define)))
    (if (pair? (cadr f)) (car (cadr f)) (cadr f))))

(for ([name public-names])
  (let ([count (length (filter (lambda (d) (eq? d name)) defined-names))])
    (report! (format "~a is defined exactly once" name)
             (= count 1)
             (format "defined ~a time(s)" count))))

(define bound-names (apply append (map binders-of source-forms)))

(define disallowed
  (dedupe (filter (lambda (s) (not (or (memq s allowed-names) (memq s bound-names))))
                  (apply append (map symbols-used source-forms)))))

(report! "solution uses only whitelisted built-ins"
         (null? disallowed)
         (format "identifiers not on the whitelist: ~s" disallowed))

;; ---------------------------------------------------------------------------
;; 3. Behaviour tests on example and edge-case trees
;; ---------------------------------------------------------------------------

(define (parse s) (read (open-input-string s)))

;; Each row: name, tree, then the exact expected printed lists for inorder,
;; preorder, postorder and (height leaves). Value functions are checked
;; against the same lists, read back from these strings.
(define cases
  (list
   (list "t1 balanced (PDF)"
         '(4 (2 (1 () ()) (3 () ())) (6 (5 () ()) (7 () ())))
         "(1 2 3 4 5 6 7)" "(4 2 1 3 6 5 7)" "(1 3 2 5 7 6 4)" "(3 4)")
   (list "t2 right-skewed (PDF)"
         '(1 () (2 () (3 () ())))
         "(1 2 3)" "(1 2 3)" "(3 2 1)" "(3 1)")
   (list "t3 symbols (PDF)"
         '(a (b () ()) (c () ()))
         "(b a c)" "(a b c)" "(b c a)" "(2 2)")
   (list "empty tree (PDF)"
         '()
         "()" "()" "()" "(0 0)")
   (list "single node"
         '(5 () ())
         "(5)" "(5)" "(5)" "(1 1)")
   (list "single symbol node"
         '(z () ())
         "(z)" "(z)" "(z)" "(1 1)")
   (list "left-skewed"
         '(3 (2 (1 () ()) ()) ())
         "(1 2 3)" "(3 2 1)" "(1 2 3)" "(3 1)")
   (list "node with one child is not a leaf"
         '(1 (2 () ()) ())
         "(2 1)" "(1 2)" "(2 1)" "(2 1)")
   (list "zig-zag"
         '(1 (2 () (3 (4 () ()) ())) ())
         "(2 4 3 1)" "(1 2 3 4)" "(4 3 2 1)" "(4 1)")
   (list "unbalanced"
         '(1 (2 (4 () ()) ()) (3 () (5 (6 () ()) ())))
         "(4 2 1 3 6 5)" "(1 2 4 3 5 6)" "(4 2 6 5 3 1)" "(4 2)")
   (list "repeated values"
         '(2 (1 () ()) (2 (1 () ()) ()))
         "(1 2 1 2)" "(2 1 2 1)" "(1 1 2 2)" "(3 2)")
   (list "mixed numbers and symbols"
         '(x (1 () ()) (y () (2 () ())))
         "(1 x y 2)" "(x 1 y 2)" "(1 2 y x)" "(3 2)")
   (list "deeper tree (height 5)"
         '(8 (4 (2 (1 () ()) (3 () ())) (6 (5 () ()) (7 () ())))
             (12 (10 (9 () ()) (11 () ())) (14 (13 () ()) (15 (16 () ()) ()))))
         "(1 2 3 4 5 6 7 8 9 10 11 12 13 14 16 15)"
         "(8 4 2 1 3 6 5 7 12 10 9 11 14 13 15 16)"
         "(1 3 2 5 7 6 4 9 11 10 13 16 15 14 12 8)"
         "(5 8)")))

(define (run-case row)
  (let* ([name (list-ref row 0)]
         [tree (list-ref row 1)]
         [in-s (list-ref row 2)]
         [pre-s (list-ref row 3)]
         [post-s (list-ref row 4)]
         [hl-s (list-ref row 5)]
         [hl (parse hl-s)])
    (check-value (format "~a: inorder-values" name)
                 (lambda () (inorder-values tree)) (parse in-s))
    (check-value (format "~a: preorder-values" name)
                 (lambda () (preorder-values tree)) (parse pre-s))
    (check-value (format "~a: postorder-values" name)
                 (lambda () (postorder-values tree)) (parse post-s))
    (check-value (format "~a: tree-height" name)
                 (lambda () (tree-height tree)) (car hl))
    (check-value (format "~a: leaf-count" name)
                 (lambda () (leaf-count tree)) (cadr hl))
    (check-output (format "~a: print-inorder (1 line)" name)
                  (lambda () (print-inorder tree))
                  (string-append in-s "\n") 1)
    (check-output (format "~a: print-all-traversals (3 lines)" name)
                  (lambda () (print-all-traversals tree))
                  (string-append in-s "\n" pre-s "\n" post-s "\n") 3)
    (check-output (format "~a: print-height-and-leaves (1 line)" name)
                  (lambda () (print-height-and-leaves tree))
                  (string-append hl-s "\n") 1)))

(for ([row cases]) (run-case row))

;; Two calls in a row must give two separate lines (nothing left over).
(check-output "two print-inorder calls give exactly two lines"
              (lambda ()
                (print-inorder '(a (b () ()) (c () ())))
                (print-inorder '()))
              "(b a c)\n()\n" 2)

;; ---------------------------------------------------------------------------
;; 4. Larger trees (performance and deep recursion)
;; ---------------------------------------------------------------------------

(define big-n 2000)

;; Left chain: root big-n, left child big-n - 1, ..., down to 1.
(define left-chain
  (let loop ([i 1] [t '()])
    (if (> i big-n) t (loop (+ i 1) (list i t '())))))

;; Right chain: root big-n, right child big-n - 1, ..., down to 1.
(define right-chain
  (let loop ([i 1] [t '()])
    (if (> i big-n) t (loop (+ i 1) (list i '() t)))))

(define ascending (build-list big-n (lambda (i) (+ i 1))))
(define descending (build-list big-n (lambda (i) (- big-n i))))
(define big-hl-line (format "(~a 1)\n" big-n))

(check-value "left chain of 2000: inorder-values"
             (lambda () (inorder-values left-chain)) ascending)
(check-value "left chain of 2000: preorder-values"
             (lambda () (preorder-values left-chain)) descending)
(check-value "left chain of 2000: postorder-values"
             (lambda () (postorder-values left-chain)) ascending)
(check-output "left chain of 2000: print-height-and-leaves"
              (lambda () (print-height-and-leaves left-chain)) big-hl-line 1)
(check-value "right chain of 2000: inorder-values"
             (lambda () (inorder-values right-chain)) descending)
(check-value "right chain of 2000: preorder-values"
             (lambda () (preorder-values right-chain)) descending)
(check-value "right chain of 2000: postorder-values"
             (lambda () (postorder-values right-chain)) ascending)
(check-output "right chain of 2000: print-height-and-leaves"
              (lambda () (print-height-and-leaves right-chain)) big-hl-line 1)

;; ---------------------------------------------------------------------------
;; Summary
;; ---------------------------------------------------------------------------

(finish!)