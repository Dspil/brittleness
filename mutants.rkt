#lang racket

(require racket/list)

;; ===============
;; Input arguments
;; ===============

(define buffer-threshold (make-parameter 100000000))
(define output-dir (make-parameter #f))
(define mutant-num (make-parameter 1))
(define starting-num (make-parameter 0))
(define renaming (make-parameter #t))
(define shuffling (make-parameter #t))
(define display-progress (make-parameter #t))

;; ===================
;; Random string state
;; ===================

(define allowed-start-symbols (list->vector
                               (append (map (lambda (a)
                                              (integer->char (+ a (char->integer #\a)))) (range 0 26))
                                       (map (lambda (a)
                                              (integer->char (+ a (char->integer #\A)))) (range 0 26)))))
(define allowed-symbols (list->vector
                         (append (map (lambda (a)
                                        (integer->char (+ a (char->integer #\a)))) (range 0 26))
                                 (map (lambda (a)
                                        (integer->char (+ a (char->integer #\A)))) (range 0 26))
                                 (map (lambda (a)
                                        (integer->char (+ a (char->integer #\0)))) (range 0 10))
                                 '(#\- #\: #\@ #\_))))

;; =======
;; Writing
;; =======

(define (needs-bars? s)
  (let ([str (format "~s" s)])
    (and
     (not (string-prefix? str "|"))
     (not (string-prefix? str ":")))))

(define (custom-write obj port)
  (match obj
    [(? symbol? obj) (if (needs-bars? obj)
                         (display (format "|~s| " obj) port)
                         (display (format "~s " obj) port))]
    [(? list?) (write-string "(" port)
               (map (lambda (o)
                      (custom-write o port))
                    obj)
               (write-string ") " port)]
    [_ (write obj port)
       (display " " port)]))

(define (program->string prog)
  (let ([virtual-output (open-output-string)])
    (for-each (lambda (sexp)
                (custom-write sexp virtual-output)
                (display #\newline virtual-output))
              prog)
    (get-output-string virtual-output)))

;; ============
;; Symbol table
;; ============

(struct symbol-table (scopes) #:mutable)

(define (new-symbol-table)
  (let ([symb-table (symbol-table (list (make-hash)))])
    (put-symbol symb-table '|=| '(((#f #f) Bool)))
    (put-symbol symb-table '|and| '(((Bool Bool) Bool)))
    (put-symbol symb-table '|or| '(((Bool Bool) Bool)))
    (put-symbol symb-table '|+| '(((Int Int) Int)))
    (put-symbol symb-table '|-| '(((Int Int) Int)))
    (put-symbol symb-table '|/| '(((Int Int) Int)))
    (put-symbol symb-table '|*| '(((Int Int) Int)))
    symb-table))

(define (push-scope symb-table)
  (set-symbol-table-scopes! symb-table (cons (make-hash) (symbol-table-scopes symb-table))))

(define (pop-scope symb-table)
  (set-symbol-table-scopes! symb-table (cdr (symbol-table-scopes symb-table))))

(define (put-symbol symb-table symb symb-type)
  (display "Putting symbol ")
  (display symb)
  (display ": ")
  (displayln symb-type)
  (hash-set! (car (symbol-table-scopes symb-table)) symb symb-type))

(define (get-symbol symb-table symb fallback)
  (letrec ([g (lambda (scopes)
                (if (empty? scopes)
                    fallback
                    (let ([existing (hash-ref (car scopes) symb #f)])
                      (if existing
                          existing
                          (g (cdr scopes))))))])
    (g (symbol-table-scopes symb-table))))

;; ===============
;; Sexp alteration
;; ===============

(define (should-keep program)
  (not
   (and (equal? (car program) 'set-option)
        (member (second program)
                '(:sat.random_seed
                  :nlsat.seed
                  :fp.spacer.random_seed
                  :smt.random_seed
                  :sls.random_seed)))))

(define (random-char v)
  (vector-ref v (random (vector-length v))))

(define (random-string)
  (let* ([start (random-char allowed-start-symbols)]
         [len (random 4 13)]
         [body (map (lambda (a) (random-char allowed-symbols)) (range (- len 1)))])
    (list->string (cons start body))))

(define (unique-random-string memory)
  (let ([s (random-string)])
    (if (set-member? memory s)
        (unique-random-string memory)
        s)))

(define (symbol-generator)
  (let* ([string-memory (mutable-set)])
    (lambda ()
      (let ([s (unique-random-string string-memory)])
        (set-add! string-memory s)
        (string->symbol s)))))

(define (is-assert? sexp)
  (and (not (empty? sexp)) ; could be removed potentially
       (equal? (car sexp) 'assert)))

(define (is-def? sexp)
  (and (not (empty? sexp))
       (member (car sexp) '(declare-sort declare-fun declare-const))))

(define (add-forall-symbols symb-table sexp)
  (map (lambda (s)
         (put-symbol symb-table (car s) (cadr s)))
       (cadr sexp)))

(define (get-function-rename rename-table symb-table old-name arg-types)
  (let ([pos (hash-ref rename-table old-name #f)])
    (if (equal? (length pos) 1)
        (cdar pos)
        (letrec ([m (lambda (p)
                      (display "HERERE: ")
                      (displayln p)
                      (if (foldl (lambda (a b) (and a b))
                                 #t
                                 (map (lambda (a b) (equal? a b))
                                      (caar p)
                                      arg-types))
                          (cdar p)
                          (m (cdr p))))])
          (displayln pos)
          (displayln arg-types)
          (m pos)))))

(define (get-function-ret func-name arg-types symb-table)
  (let ([pos (get-symbol func-name symb-table #f)])
    (if (equal? (length pos) 1)
        (cdar pos)
        (letrec ([f (lambda (p)
                      (if (foldl (lambda (a b) (and a b))
                                 #t
                                 (map (lambda (a b) (equal? a b))
                                      (caar p)
                                      arg-types))
                          (cdar p)
                          (f (cdr p))))])
          (f pos)))))

(define (type-check sexp symb-table)
  (cond
    [(symbol? sexp)
     (get-symbol symb-table sexp #f)]
    [(list? sexp)
     (let* ([func-name (car sexp)]
            [arg-types (map (lambda (arg) (type-check arg symb-table)) (cdr sexp))])
       (get-function-ret func-name arg-types symb-table))]
    [(number? sexp)
     'Int]
    [(or (equal? sexp 'true)
         (equal? sexp 'false))
     'Bool]))

(define (handle-function-application sexp rename-table symb-table)
  (let* ([name (car sexp)]
         [arg-types (map (lambda (a) (type-check a symb-table))
                          (cdr sexp))]
         [new-name (get-function-rename rename-table symb-table name arg-types)])
    (display "Found new name: ")
    (displayln new-name)
    (cons new-name
          (map (lambda (s)
                 (rename-symbs s rename-table symb-table))
               (cdr sexp)))))

(define (rename-symbs sexp rename-table symb-table)
  (display "Renaming ")
  (displayln sexp)
  (if (renaming) ; renaming happens only when it is activated
      (cond
        [(list? sexp)
         (cond
           [(and (not (empty? sexp)) (or (equal? (car sexp) 'forall)
                                         (equal? (car sexp) 'exists))) ; forall and exists
            (let ([start-symb (car sexp)])
              (push-scope symb-table)
              (add-forall-symbols symb-table sexp)
              (begin0
                (cons start-symb
                      (cons (map (lambda (arg)
                                   (list (rename-symbs (car arg) rename-table symb-table)
                                         (rename-symbs (cadr arg) rename-table symb-table)))
                                 (cadr sexp))
                            (map (lambda (s)
                                   (rename-symbs s rename-table symb-table))
                                 (cddr sexp))))
                (pop-scope symb-table)))]
           [(and (not (empty? sexp)) (equal? (car sexp) 'declare-fun)) ; function declaration
            (let* ([args (caddr sexp)]
                   [new-name (get-function-rename rename-table symb-table (cadr sexp) args)])
              (list 'declare-fun new-name
                    (map (lambda (s)
                           (rename-symbs s rename-table symb-table))
                         (caddr sexp))
                    (rename-symbs (cadddr sexp) rename-table symb-table)))]
           [(and (> (length sexp) 1)
                 (hash-ref rename-table (car sexp) #f)
                 (foldl (lambda (a b) (and b (symbol? a))) #t (cdr sexp))) ; function application
            (displayln "inside")
            (handle-function-application sexp rename-table symb-table)]
           [(and (> (length sexp) 1)
                 (hash-ref rename-table (car sexp) #f))
            (displayln "inside2")
            (let ([new-name (cdar (hash-ref rename-table (car sexp) #f))])
              (display "Found new name: ")
              (displayln new-name)
              (cons new-name
                    (map (lambda (s)
                           (rename-symbs s rename-table symb-table))
                         (cdr sexp))))]
           [else
            (map (lambda (s)
                   (rename-symbs s rename-table symb-table))
                 sexp)])]
        [(symbol? sexp)
         (hash-ref rename-table sexp sexp)]
        [else sexp])
      sexp))

(define (update-tables sexp rename-table symb-table symb-gen)
  (let ([kind (car sexp)])
    (cond
      [(equal? kind 'declare-sort)
       (hash-set! rename-table (cadr sexp) (symb-gen))]
      [(equal? kind 'declare-const)
       (let* ([new-symb (symb-gen)]
              [old-symb (cadr sexp)]
              [symb-type (caddr sexp)])
         (hash-set! rename-table old-symb new-symb)
         (put-symbol symb-table old-symb symb-type))]
      [(equal? kind 'declare-fun)
       (let* ([new-symb (symb-gen)]
              [old-symb (cadr sexp)]
              [arg-type (caddr sexp)]
              [ret-type (cadddr sexp)]
              [existing (hash-ref rename-table old-symb '())]
              [existing-type (get-symbol symb-table old-symb '())])
         (hash-set! rename-table old-symb (cons (cons arg-type new-symb) existing))
         (put-symbol symb-table old-symb (cons (cons arg-type ret-type) existing-type)))])))

;; ======
;; Writer
;; ======

(define (writer out)
  (let ([symb-gen (symbol-generator)]
        [accumulator '()]
        [writer-buffer (open-output-string)]
        [writer-buffer-size 0]
        [accumulating #f]
        [rename-table (make-hash)]
        [symb-table (new-symbol-table)])
    (lambda (sexp)
      (if (equal? sexp 'flush)
          (display (get-output-string writer-buffer) out)
          (when (should-keep sexp)
            (if (is-assert? sexp)
                (begin (when (not accumulating)
                         (set! accumulating 'assert))
                       (set! accumulator (cons (rename-symbs sexp rename-table symb-table) accumulator)))
                (begin (unless (empty? accumulator)
                         (let ([program-string (program->string
                                                (if (shuffling) ; shuffle only when shuffling is activated
                                                    (shuffle accumulator)
                                                    accumulator))])
                           (display program-string writer-buffer)
                           (set! writer-buffer-size (+ writer-buffer-size
                                                       (string-length program-string))))
                         (set! accumulator '()))
                       (set! accumulating #f)
                       (when (is-def? sexp)
                         (display "FOund def: ")
                         (displayln sexp)
                         (update-tables sexp rename-table symb-table symb-gen))
                       (let ([program-string (program->string (list (rename-symbs sexp rename-table symb-table)))])
                         (display program-string writer-buffer)
                         (set! writer-buffer-size (+ writer-buffer-size
                                                     (string-length program-string))))
                       (when (> writer-buffer-size (buffer-threshold))
                         (display (get-output-string writer-buffer) out)
                         (set! writer-buffer (open-output-string))
                         (set! writer-buffer-size 0)))))))))

;; ======================
;; Main method definition
;; ======================

(define (make-progress-bar sofar total)
  (let ([chars (quotient (* 20 sofar) total)])
    (display #\return)
    (display (format "Progress: [~a~a] ~a%"
                     (make-string chars #\=)
                     (make-string (- 20 chars) #\space)
                     (quotient (* 100 sofar) total)))))

(define (create-mutants file-path out-dir num)
  (let*-values ([(seeds) (range (starting-num) (+ (starting-num) num))]
                [(fname-base fname _) (split-path file-path)]
                [(output-directory) (begin
                                      (when (and out-dir (not (directory-exists? out-dir)))
                                        (make-directory out-dir))
                                      (or out-dir (if (equal? fname-base 'relative) "." fname-base)))]
                [(outs) (map (lambda (n)
                               (open-output-file
                                (build-path output-directory (format "mutant_~a_of_~a" n fname))
                                #:exists 'replace))
                             seeds)]
                [(writers) (map writer outs)]
                [(total-size) (file-size file-path)])
    (letrec ([write-all
              (lambda (infile)
                (let [(sexp (read infile))]
                  (when (not (eof-object? sexp))
                    (when (display-progress)
                      (make-progress-bar (file-position infile) total-size))
                    (map (lambda (w) (w sexp)) writers)
                    (write-all infile))))])
      (let ([input-file (open-input-file file-path)])
        (write-all input-file)
        (map (lambda (w) (w 'flush)) writers) ; flush all the writer buffers
        (when (display-progress)
          (display #\return) ; set the progress to 100 :)
          (display (format "Progress: [~a] 100%\n" (make-string 20 #\=))))
        (close-input-port input-file)
        (map close-output-port outs)
        (void)))))

;; =============================
;; Define command line arguments
;; =============================


(define file-to-mutate
  (command-line
   #:program "mutants"
   #:once-each
   [("-n" "--num") num
                   "Set the number of mutants. Default: 1."
                   (mutant-num (string->number num))]
   [("-d" "--directory") dir
                         "Where to put the mutants. Default is the directory of the input file."
                         (output-dir dir)]
   [("-t" "--threshold") t
                         ("Buffer threshold for writing to the disk in bytes."
                          "Default: 100Mb")
                         (buffer-threshold (string->number t))]
   [("-s" "--start") start
                     "Starting number of the mutants"
                     (starting-num (string->number start))]
   [("-r" "--norename")
    "Disable renaming."
    (renaming #f)]
   [("-o" "--noshuffle")
    "Disable shuffling."
    (shuffling #f)]
   [("-p" "--noprogress")
    "Disable showing the progress bar."
    (display-progress #f)]
   #:args (filename)
   filename))


(begin (create-mutants file-to-mutate (output-dir) (mutant-num))
       (void))

