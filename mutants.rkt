#lang racket

(require racket/list)

;; ===============
;; Input arguments
;; ===============

(define buffer-threshold (make-parameter 100000000))
(define output-dir (make-parameter #f))
(define mutant-num (make-parameter 10))
(define starting-num (make-parameter 0))
(define renaming (make-parameter #t))
(define shuffling (make-parameter #t))

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

(define (rename-symbs sexp symb-table)
  (if (renaming) ; renaming happens only when it is activated
      (cond [(list? sexp)
             (map (lambda (s)
                    (rename-symbs s symb-table))
                  sexp)]
            [(symbol? sexp)
             (hash-ref symb-table sexp sexp)]
            [else sexp])
      sexp))

;; ======
;; Writer
;; ======

(define (writer out)
  (let ([symb-gen (symbol-generator)]
        [accumulator '()]
        [writer-buffer (open-output-string)]
        [writer-buffer-size 0]
        [accumulating #f]
        [symb-table (make-hash)])
    (lambda (sexp)
      (if (equal? sexp 'flush)
          (display (get-output-string writer-buffer) out)
          (when (should-keep sexp)
            (if (is-assert? sexp)
                (begin (when (not accumulating)
                         (set! accumulating 'assert))
                       (set! accumulator (cons (rename-symbs sexp symb-table) accumulator)))
                (begin (let ([program-string (program->string
                                              (if (shuffling) ; shuffle only when shuffling is activated
                                                  (shuffle accumulator)
                                                  accumulator))])
                         (display program-string writer-buffer)
                         (set! writer-buffer-size (+ writer-buffer-size
                                                     (string-length program-string))))
                       (set! accumulator '())
                       (set! accumulating #f)
                       (when (is-def? sexp)
                         (hash-set! symb-table (cadr sexp) (symb-gen)))
                       (let ([program-string (program->string (list (rename-symbs sexp symb-table)))])
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
                    (make-progress-bar (file-position infile) total-size)
                    (map (lambda (w) (w sexp)) writers)
                    (write-all infile))))])
      (let ([input-file (open-input-file file-path)])
        (write-all input-file)
        (map (lambda (w) (w 'flush)) writers) ; flush all the writer buffers
        (display #\return) ; set the progress to 100 :)
        (display (format "Progress: [~a] 100%\n" (make-string 20 #\=)))
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
                   "Set the number of mutants. Default: 10."
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
   #:args (filename)
   filename))


(begin (create-mutants file-to-mutate (output-dir) (mutant-num))
       (void))

