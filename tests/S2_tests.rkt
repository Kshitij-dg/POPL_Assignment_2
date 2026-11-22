#lang racket
;; tests/S2_tests.rkt -- CS F301 Assignment 2, Group 61, Problem S2 test suite.
;;
;; Run from the repository root:   racket tests/S2_tests.rkt
;; Exit code 0 if every test passes, 1 if any test fails.
;;
;; code/61_q4.rkt is never modified and needs no `provide`. The suite uses
;; three independent techniques:
;;   A. Static check  - reads the solution as data and checks that it starts
;;                      with #lang racket/base, contains only definitions, and
;;                      uses only the built-ins the PDF permits (plus names the
;;                      solution binds itself).
;;   B. Subprocesses  - runs `racket code/61_q4.rkt` (must print nothing), and
;;                      a temporary copy with (print-insert-result) appended,
;;                      fed through stdin exactly as the grader does. The
;;                      temporary copy is deleted afterwards.
;;   C. In-process    - loads the module into a fresh namespace and reaches its
;;                      unexported definitions with module->namespace.
;; Every test runs under a timeout; wrong results, exceptions and timeouts are
;; all reported as FAIL. This file may use full Racket: the PDF's built-in
;; restrictions apply to the solution only.

(require racket/runtime-path)

;; ---------------------------------------------------------------------------
;; Configuration
;; ---------------------------------------------------------------------------

(define-runtime-path solution-rel (build-path 'up "code" "61_q4.rkt"))
(define src (simplify-path solution-rel))
(define TIMEOUT-SECONDS 30)

;; ---------------------------------------------------------------------------
;; Reporting and guarded execution
;; ---------------------------------------------------------------------------

(define passed 0)
(define failed 0)

(define (section title)
  (printf "\n== ~a ==\n" title))

(define (pass! name)
  (set! passed (add1 passed))
  (printf "PASS  ~a\n" name))

(define (fail! name why)
  (set! failed (add1 failed))
  (printf "FAIL  ~a\n      ~a\n" name why))

;; Printed form of a value, cut to 300 characters so huge results stay readable.
(define (show v)
  (define s (format "~s" v))
  (if (> (string-length s) 300)
      (string-append (substring s 0 300) " ...")
      s))

(define (exn->text e)
  (if (exn? e)
      (exn-message e)
      (format "raised non-exception value ~s" e)))

;; Runs thunk in its own thread. Returns (list 'ok value), (list 'exn e) or
;; (list 'timeout). Catches every raised value, not only exn:fail.
(define (run-guarded thunk)
  (define ch (make-channel))
  (define worker
    (thread
     (lambda ()
       (channel-put ch
                    (with-handlers ([(lambda (_) #t) (lambda (e) (list 'exn e))])
                      (list 'ok (thunk)))))))
  (define result (sync/timeout TIMEOUT-SECONDS ch))
  (cond
    [result result]
    [else (kill-thread worker) (list 'timeout)]))

;; One test: PASS iff (thunk) returns a value equal? to expected.
(define (check name thunk expected)
  (match (run-guarded thunk)
    [(list 'ok v)
     (if (equal? v expected)
         (pass! name)
         (fail! name (string-append "expected " (show expected)
                                    "\n      got      " (show v))))]
    [(list 'exn e)
     (fail! name (string-append "exception: " (exn->text e)))]
    [(list 'timeout)
     (fail! name (format "timed out after ~a seconds" TIMEOUT-SECONDS))]))

(define (crlf->lf s) (string-replace s "\r\n" "\n"))

;; ---------------------------------------------------------------------------
;; A. Static checks on the solution source
;; ---------------------------------------------------------------------------

;; Built-ins and special forms listed in the PDF's Scheme rules (S2 adds read).
(define permitted-names
  '(define lambda let let* letrec if cond else and or not begin quote
    cons car cdr list null? pair? eq? assq assoc
    + - * < > <= >= = max display newline read))

;; Every car/cdr composition up to four levels: car, cdr, cadr, ..., cddddr.
(define (permitted? s)
  (or (memq s permitted-names)
      (regexp-match? #px"^c[ad]{1,4}r$" (symbol->string s))))

;; Returns (cons first-line forms): the #lang line and the remaining
;; s-expressions of the file, read as plain data (comments are skipped).
(define (read-source path)
  (call-with-input-file path
    (lambda (in)
      (define first-line (read-line in 'any))
      (define forms
        (parameterize ([read-accept-reader #f] [read-accept-lang #f])
          (let loop ([acc '()])
            (define d (read in))
            (if (eof-object? d)
                (reverse acc)
                (loop (cons d acc))))))
      (cons first-line forms))))

;; Name defined by a top-level form, or #f if the form is not a definition.
(define (define-name f)
  (match f
    [(list* 'define (cons name _) _) name]
    [(list* 'define (? symbol? name) _) name]
    [_ #f]))

;; Sorted list of symbols used in forms that are neither permitted built-ins
;; nor names the solution binds itself (define, lambda, let/let*/letrec,
;; named let). Quoted data is skipped because it is not code.
(define (forbidden-names forms)
  (define bound (mutable-seteq))
  (define used (mutable-seteq))
  (define (bind! x)
    (cond [(symbol? x) (set-add! bound x)]
          [(pair? x) (bind! (car x)) (bind! (cdr x))]
          [else (void)]))
  (define (walk-all xs)
    (cond [(pair? xs) (walk (car xs)) (walk-all (cdr xs))]
          [(null? xs) (void)]
          [else (walk xs)]))
  (define (walk f)
    (match f
      [(list 'quote _) (void)]
      [(list* 'define (cons name params) body)
       (set-add! used 'define) (bind! name) (bind! params) (walk-all body)]
      [(list* 'define (? symbol? name) rhs)
       (set-add! used 'define) (bind! name) (walk-all rhs)]
      [(list* 'lambda params body)
       (set-add! used 'lambda) (bind! params) (walk-all body)]
      [(list* 'let (? symbol? name) (list (list vars inits) ...) body)
       (set-add! used 'let) (bind! name) (bind! vars)
       (walk-all inits) (walk-all body)]
      [(list* (and kw (or 'let 'let* 'letrec)) (list (list vars inits) ...) body)
       (set-add! used kw) (bind! vars) (walk-all inits) (walk-all body)]
      [(? pair?) (walk-all f)]
      [(? symbol?) (set-add! used f)]
      [_ (void)]))
  (walk-all forms)
  (sort (for/list ([s (in-set used)]
                   #:unless (or (permitted? s) (set-member? bound s)))
          s)
        symbol<?))

(printf "S2 test suite for ~a\n" (path->string src))

(section "A. Static checks")

(check "A1 file begins with #lang racket/base"
       (lambda () (string-trim (car (read-source src))))
       "#lang racket/base")

(check "A2 top level contains only definitions (no calls, no output)"
       (lambda () (filter (lambda (f) (not (define-name f)))
                          (cdr (read-source src))))
       '())

(check "A3 defines the five S2 functions, each exactly once"
       (lambda () (sort (filter-map define-name (cdr (read-source src)))
                        symbol<?))
       '(insert-if-short make-inserter my-length my-map print-insert-result))

(check "A4 uses only built-ins permitted by the PDF"
       (lambda () (forbidden-names (cdr (read-source src))))
       '())

;; ---------------------------------------------------------------------------
;; B. Subprocess checks (exactly how the grader runs the file)
;; ---------------------------------------------------------------------------

(define racket-exe
  (let ([self (find-system-path 'exec-file)])
    (or (and (absolute-path? self) (file-exists? self) self)
        (find-executable-path self)
        (find-executable-path "racket")
        (find-executable-path "racket.exe"))))

;; Runs `racket file` with input on stdin. Returns
;; (list exit-code stdout stderr) with \r\n normalised to \n, or 'timeout.
(define (run-racket file input)
  (unless racket-exe
    (error 'run-racket "cannot locate the racket executable"))
  (define-values (sp from-out to-in from-err)
    (subprocess #f #f #f racket-exe (path->string file)))
  (define out-text "")
  (define err-text "")
  (define t-out
    (thread (lambda ()
              (with-handlers ([exn:fail? void])
                (set! out-text (port->string from-out))))))
  (define t-err
    (thread (lambda ()
              (with-handlers ([exn:fail? void])
                (set! err-text (port->string from-err))))))
  (with-handlers ([exn:fail? void])
    (write-string input to-in))
  (with-handlers ([exn:fail? void])
    (close-output-port to-in))
  (define finished (sync/timeout (- TIMEOUT-SECONDS 5) sp))
  (unless finished (subprocess-kill sp #t))
  (thread-wait t-out)
  (thread-wait t-err)
  (close-input-port from-out)
  (close-input-port from-err)
  (if finished
      (list (subprocess-status sp) (crlf->lf out-text) (crlf->lf err-text))
      'timeout))

;; Temporary copy of the solution with `appended` added at the end.
(define (make-temp-copy appended)
  (define tmp (make-temporary-file "s2test~a.rkt"))
  (with-output-to-file tmp #:exists 'truncate
    (lambda ()
      (write-string (file->string src))
      (newline)
      (write-string appended)
      (newline)))
  tmp)

(section "B. Running the file as the grader does")

(check "B1 `racket code/61_q4.rkt` exits 0 and prints nothing (stdout and stderr)"
       (lambda () (run-racket src ""))
       (list 0 "" ""))

;; Each entry: (name stdin expected-stdout)
(define grader-cases
  '(("B2 stdin: 42 ((1 2) (3 4 5) (6) ()) 3"
     "42 ((1 2) (3 4 5) (6) ()) 3\n"
     "((42 1 2) (3 4 5) (42 6) (42))\n")
    ("B3 stdin: 0 (((1) 2) (3) ((4 5 6) ())) 3"
     "0 (((1) 2) (3) ((4 5 6) ())) 3\n"
     "((0 (0 1) 2) (0 3) (0 (4 5 6) (0)))\n")
    ("B4 stdin: 7 () 3"
     "7 () 3\n"
     "(7)\n")
    ("B5 stdin: 7 () 0"
     "7 () 0\n"
     "()\n")
    ("B6 stdin split over three lines"
     "x\n(a (b) ())\n2\n"
     "(a (x b) (x))\n")))

(match (run-guarded (lambda () (make-temp-copy "(print-insert-result)")))
  [(list 'ok tmp)
   (dynamic-wind
    void
    (lambda ()
      (for ([c grader-cases])
        (match-define (list name input expected) c)
        (check (string-append name " (exit 0, exact stdout, empty stderr)")
               (lambda () (run-racket tmp input))
               (list 0 expected ""))))
    (lambda ()
      (when (file-exists? tmp) (delete-file tmp))))]
  [(list 'exn e)
   (fail! "B2-B6 create temporary copy" (string-append "exception: " (exn->text e)))]
  [(list 'timeout)
   (fail! "B2-B6 create temporary copy" "timed out")])

;; ---------------------------------------------------------------------------
;; C. In-process checks on the unexported definitions
;; ---------------------------------------------------------------------------

(section "C0. Loading the module")

(define load-output (open-output-string))

(define sol-ns
  (match (run-guarded
          (lambda ()
            (parameterize ([current-namespace (make-base-namespace)]
                           [current-output-port load-output]
                           [current-input-port (open-input-string "")])
              (dynamic-require src #f)
              (module->namespace src))))
    [(list 'ok ns) (pass! "C0.1 module loads without error") ns]
    [(list 'exn e)
     (fail! "C0.1 module loads without error" (string-append "exception: " (exn->text e)))
     #f]
    [(list 'timeout)
     (fail! "C0.1 module loads without error" "timed out")
     #f]))

(check "C0.2 loading the module prints nothing"
       (lambda () (get-output-string load-output))
       "")

;; Fetches an unexported definition. If it is missing, returns a procedure
;; that raises, so every test using it is reported as FAIL.
(define (sol name)
  (with-handlers ([(lambda (_) #t)
                   (lambda (e)
                     (lambda args (error name "not available from code/61_q4.rkt")))])
    (eval name sol-ns)))

(define my-length (sol 'my-length))
(define my-map (sol 'my-map))
(define make-inserter (sol 'make-inserter))
(define insert-if-short (sol 'insert-if-short))
(define print-insert-result (sol 'print-insert-result))

;; Runs print-insert-result with the given stdin and returns everything it printed.
(define (print-with input)
  (define out (open-output-string))
  (parameterize ([current-input-port (open-input-string input)]
                 [current-output-port out])
    (print-insert-result))
  (get-output-string out))

;; Test data, built by the test file itself.
(define big (build-list 10000 add1))                       ; (1 2 ... 10000)
(define (deep k leaf)                                      ; k wrappers around leaf
  (if (= k 0) leaf (list (deep (- k 1) leaf))))
(define (deep-x k)                                         ; deep with x at every level
  (if (= k 0) '(x) (list 'x (deep-x (- k 1)))))
(define (wide-deep k)                                      ; (1 2 (1 2 (... ())))
  (if (= k 0) '() (list 1 2 (wide-deep (- k 1)))))
(define (wide-deep-all k)                                  ; x inserted at every level
  (if (= k 0) '(x) (list 'x 1 2 (wide-deep-all (- k 1)))))
(define (wide-deep-leaf k)                                 ; x inserted only innermost
  (if (= k 0) '(x) (list 1 2 (wide-deep-leaf (- k 1)))))
(define big-text (string-join (map number->string big) " "))

(section "C1. my-length")

(check "C1.1 empty list" (lambda () (my-length '())) 0)
(check "C1.2 one atom" (lambda () (my-length '(a))) 1)
(check "C1.3 flat list" (lambda () (my-length '(1 2 3 4 5))) 5)
(check "C1.4 nested lists count as one element each"
       (lambda () (my-length '((1 2) (3 4 5) (6) ()))) 4)
(check "C1.5 list of empty lists" (lambda () (my-length '(() () ()))) 3)
(check "C1.6 single deeply nested element" (lambda () (my-length '((((a)))))) 1)
(check "C1.7 10,000 atoms" (lambda () (my-length big)) 10000)
(check "C1.8 10,000 sublists" (lambda () (my-length (build-list 10000 (lambda (i) (list i i))))) 10000)
(check "C1.9 depth-100 nesting has top-level length 1" (lambda () (my-length (deep 100 '()))) 1)

(section "C2. my-map")

(check "C2.1 empty list" (lambda () (my-map add1 '())) '())
(check "C2.2 add1" (lambda () (my-map add1 '(1 2 3))) '(2 3 4))
(check "C2.3 squaring" (lambda () (my-map (lambda (v) (* v v)) '(1 2 3 4))) '(1 4 9 16))
(check "C2.4 identity keeps nested elements unchanged"
       (lambda () (my-map (lambda (v) v) '(a (b c) () ((d))))) '(a (b c) () ((d))))
(check "C2.5 f applied to nested elements as whole values"
       (lambda () (my-map my-length '((1 2) () (3 4 5) ((6 7))))) '(2 0 3 1))
(check "C2.6 order preserved"
       (lambda () (my-map list '(3 1 2))) '((3) (1) (2)))
(check "C2.7 f applied left to right, once per element"
       (lambda ()
         (define seen '())
         (my-map (lambda (v) (set! seen (cons v seen)) v) '(1 2 3))
         (reverse seen))
       '(1 2 3))
(check "C2.8 10,000 atoms (compared with built-in map as oracle)"
       (lambda () (my-map add1 big)) (map add1 big))
(check "C2.9 10,000 sublists"
       (lambda () (my-map my-length (build-list 10000 (lambda (i) (list i i)))))
       (make-list 10000 2))

(section "C3. insert-if-short: PDF examples")

(check "C3.1 42 ((1 2) (3 4 5) (6) ()) 3"
       (lambda () (insert-if-short 42 '((1 2) (3 4 5) (6) ()) 3))
       '((42 1 2) (3 4 5) (42 6) (42)))
(check "C3.2 0 (((1) 2) (3) ((4 5 6) ())) 3"
       (lambda () (insert-if-short 0 '(((1) 2) (3) ((4 5 6) ())) 3))
       '((0 (0 1) 2) (0 3) (0 (4 5 6) (0))))
(check "C3.3 7 () 3" (lambda () (insert-if-short 7 '() 3)) '(7))
(check "C3.4 7 () 0" (lambda () (insert-if-short 7 '() 0)) '())

(section "C4. insert-if-short: strict inequality")

(check "C4.1 length 3, n = 3: no insertion" (lambda () (insert-if-short 'x '(a b c) 3)) '(a b c))
(check "C4.2 length 3, n = 4: insertion" (lambda () (insert-if-short 'x '(a b c) 4)) '(x a b c))
(check "C4.3 nested: length 2 = n skipped, length 1 < n inserted"
       (lambda () (insert-if-short 'x '((a b) (c)) 2)) '((a b) (x c)))
(check "C4.4 10,000 elements, n = 10000: no insertion" (lambda () (insert-if-short 'x big 10000)) big)
(check "C4.5 10,000 elements, n = 10001: insertion" (lambda () (insert-if-short 'x big 10001)) (cons 'x big))

(section "C5. Lengths measured on the original list, x inserted once")

(check "C5.1 () with n = 1 becomes (x) (length after insertion would be 1)"
       (lambda () (insert-if-short 'x '() 1)) '(x))
(check "C5.2 (a) with n = 2 becomes (x a)" (lambda () (insert-if-short 'x '(a) 2)) '(x a))
(check "C5.3 large n inserts x only once" (lambda () (insert-if-short 'x '(a b) 10)) '(x a b))
(check "C5.4 children changing does not change the parent's length"
       (lambda () (insert-if-short 'x '((a) (b) (c)) 3)) '((x a) (x b) (x c)))
(check "C5.5 parent and children all qualify"
       (lambda () (insert-if-short 'x '(() (a)) 3)) '(x (x) (x a)))
(check "C5.6 len-ok? receives each list's original length, once per list"
       (lambda ()
         (define seen '())
         ((make-inserter 'x (lambda (l) (set! seen (cons l seen)) #f))
          '((1 2) (3 4 5) (6) ()))
         (sort seen <))
       '(0 1 2 3 4))

(section "C6. Outermost list")

(check "C6.1 outermost list qualifies" (lambda () (insert-if-short 'x '(a b) 3)) '(x a b))
(check "C6.2 outermost and inner lists qualify"
       (lambda () (insert-if-short 'x '((1) 2) 3)) '(x (x 1) 2))
(check "C6.3 outermost list of length 4, n = 5" (lambda () (insert-if-short 'x '(a b c d) 5)) '(x a b c d))
(check "C6.4 nested chain: every level qualifies"
       (lambda () (insert-if-short 'x (deep 4 '()) 10)) (deep-x 4))

(section "C7. Empty lists, mixed elements, repeated values, symbols")

(check "C7.1 nested empty lists, n = 1"
       (lambda () (insert-if-short 'x '(() (()) ((()))) 1)) '((x) ((x)) (((x)))))
(check "C7.2 nested empty lists, n = 2"
       (lambda () (insert-if-short 'x '(() (()) ((()))) 2)) '((x) (x (x)) (x (x (x)))))
(check "C7.3 x equal to atoms already in the list"
       (lambda () (insert-if-short 1 '(1 (1 1) 1 (1)) 2)) '(1 (1 1) 1 (1 1)))
(check "C7.4 symbolic atoms"
       (lambda () (insert-if-short 'z '(a (b c d) (e) ()) 2)) '(a (b c d) (z e) (z)))
(check "C7.5 n = 0 leaves a nested structure unchanged"
       (lambda () (insert-if-short 'x '(1 () (2 ())) 0)) '(1 () (2 ())))
(check "C7.6 large n inserts into every list"
       (lambda () (insert-if-short 'x '(a (b) ()) 100)) '(x a (x b) (x)))

(section "C8. make-inserter with other predicates")

(check "C8.1 exact length 1"
       (lambda () ((make-inserter 'q (lambda (l) (= l 1))) '(a (b) (c d) ((e)))))
       '(a (q b) (c d) (q (q e))))
(check "C8.2 exact length 0"
       (lambda () ((make-inserter 'z (lambda (l) (= l 0))) '(a () (b ()))))
       '(a (z) (b (z))))
(check "C8.3 always true"
       (lambda () ((make-inserter 'x (lambda (l) #t)) '(1 (2 (3)))))
       '(x 1 (x 2 (x 3))))
(check "C8.4 always false leaves the list unchanged"
       (lambda () ((make-inserter 'x (lambda (l) #f)) '(1 (2 (3)) ())))
       '(1 (2 (3)) ()))
(check "C8.5 even lengths (including 0)"
       (lambda () ((make-inserter 'e even?) '((1 2) (3) () (4 5 6 7))))
       '(e (e 1 2) (3) (e) (e 4 5 6 7)))
(check "C8.6 length >= 2"
       (lambda () ((make-inserter 'x (lambda (l) (>= l 2))) '(a (b) (c d))))
       '(x a (b) (x c d)))
(check "C8.7 returns a one-argument function"
       (lambda () (procedure-arity (make-inserter 'x (lambda (l) #t))))
       1)
(check "C8.8 one inserter reused on several lists"
       (lambda ()
         (define ins (make-inserter 'x (lambda (l) (< l 2))))
         (list (ins '(a)) (ins '(a b)) (ins '())))
       '((x a) (a b) (x)))

(section "C9. print-insert-result")

(check "C9.1 takes no arguments" (lambda () (procedure-arity print-insert-result)) 0)
(check "C9.2 PDF example 1"
       (lambda () (print-with "42 ((1 2) (3 4 5) (6) ()) 3"))
       "((42 1 2) (3 4 5) (42 6) (42))\n")
(check "C9.3 PDF example 2"
       (lambda () (print-with "0 (((1) 2) (3) ((4 5 6) ())) 3"))
       "((0 (0 1) 2) (0 3) (0 (4 5 6) (0)))\n")
(check "C9.4 PDF example 3" (lambda () (print-with "7 () 3")) "(7)\n")
(check "C9.5 PDF example 4" (lambda () (print-with "7 () 0")) "()\n")
(check "C9.6 reads in the order x, lst, n (swapping x and n would give (4 1 2 3))"
       (lambda () (print-with "5 (1 2 3) 4")) "(5 1 2 3)\n")
(check "C9.7 input spread over several lines"
       (lambda () (print-with "x\n(a (b) ())\n2\n")) "(a (x b) (x))\n")
(check "C9.8 reads exactly three values (the fourth is left unread)"
       (lambda ()
         (define in (open-input-string "7 () 3 99"))
         (define out (open-output-string))
         (parameterize ([current-input-port in] [current-output-port out])
           (print-insert-result))
         (list (get-output-string out) (read in)))
       (list "(7)\n" 99))
(check "C9.9 10,000-element input"
       (lambda () (print-with (string-append "x (" big-text ") 10001")))
       (string-append "(x " big-text ")\n"))
(check "C9.10 depth-100 input"
       (lambda () (print-with (string-append "x " (make-string 100 #\() (make-string 100 #\)) " 2")))
       (format "~a\n" (deep-x 99)))

(section "C10. Large inputs and deep nesting")

(check "C10.1 depth 100, n = 2: x at every level"
       (lambda () (insert-if-short 'x (deep 100 '()) 2)) (deep-x 100))
(check "C10.2 depth 100, n = 1: x only in the innermost ()"
       (lambda () (insert-if-short 'x (deep 100 '()) 1)) (deep 100 '(x)))
(check "C10.3 depth 100, n = 0: unchanged"
       (lambda () (insert-if-short 'x (deep 100 '()) 0)) (deep 100 '()))
(check "C10.4 depth 100 with three elements per level, n = 4"
       (lambda () (insert-if-short 'x (wide-deep 100) 4)) (wide-deep-all 100))
(check "C10.5 depth 100 with three elements per level, n = 3"
       (lambda () (insert-if-short 'x (wide-deep 100) 3)) (wide-deep-leaf 100))
(check "C10.6 10,000 empty sublists, n = 1"
       (lambda () (insert-if-short 'x (make-list 10000 '()) 1)) (make-list 10000 '(x)))
(check "C10.7 10,000 mixed atoms and sublists, n = 2"
       (lambda ()
         (insert-if-short 'x (build-list 10000 (lambda (i) (if (even? i) i (list i)))) 2))
       (build-list 10000 (lambda (i) (if (even? i) i (list 'x i)))))
(check "C10.8 100 sublists, each nested 100 deep, n = 2"
       (lambda () (insert-if-short 'x (make-list 100 (deep 100 '())) 2))
       (make-list 100 (deep-x 100)))
(check "C10.9 my-length of a 10,001-element result"
       (lambda () (my-length (insert-if-short 'x big 10001))) 10001)

;; ---------------------------------------------------------------------------
;; Summary
;; ---------------------------------------------------------------------------

(printf "\n== Summary ==\n~a passed, ~a failed, ~a total\n" passed failed (+ passed failed))
(exit (if (zero? failed) 0 1))