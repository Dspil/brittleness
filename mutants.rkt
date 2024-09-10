#lang racket

(require racket/list)

(define BUFFER-THRESHOLD 100000000)

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

(define (should-keep program)
  (not
   (and (equal? (car program) 'set-option)
        (member (second program)
                '(:sat.random_seed
                  :nlsat.seed
                  :fp.spacer.random_seed
                  :smt.random_seed
                  :sls.random_seed)))))

(define (decode-symb stable item)
  (letrec ([base-n
            (lambda (stable item acc)
              (if (zero? item)
                  acc
                  (let ([vlen (vector-length stable)])
                    (base-n stable (quotient item vlen)
                            (cons (remainder item vlen) acc)
                            ))))])
    (list->string (map (lambda (i) (vector-ref stable i))
                       (base-n stable item '())))))

(define (symbol-generator seed)
  (let* ([stable (list->vector
                  (shuffle
                   (append (map (lambda (a)
                                  (integer->char (+ a (char->integer #\a)))) (range 0 26))
                           (map (lambda (a)
                                  (integer->char (+ a (char->integer #\A)))) (range 0 26)))))]
         [current-item 0])
    (lambda ()
      (begin0
        (string->symbol (format "GS-~a-~a"
                                seed
                                (decode-symb stable current-item)))
        (set! current-item (+ current-item 1))))))

(define (is-assert? sexp)
  (and (not (empty? sexp)) ; could be removed potentially
       (equal? (car sexp) 'assert)))

(define (is-def? sexp)
  (and (not (empty? sexp))
       (member (car sexp) '(declare-sort declare-fun declare-const))))

(define (rename-symbs sexp symb-table)
  (cond [(list? sexp)
         (map (lambda (s)
                (rename-symbs s symb-table))
              sexp)]
        [(symbol? sexp)
         (hash-ref symb-table sexp sexp)]
        [else sexp]))

(define (writer out seed)
  (let ([symb-gen (symbol-generator seed)]
        [accumulator '()]
        [writer-buffer (open-output-string)]
        [writer-buffer-size 0]
        [accumulating #f]
        [symb-table (make-hash)])
    (lambda (sexp)
      (if (equal? sexp 'flush)
          (print (get-output-string writer-buffer) out)
          (when (should-keep sexp)
            (if (is-assert? sexp)
                (begin (when (not accumulating)
                         (set! accumulating 'assert))
                       (set! accumulator (cons (rename-symbs sexp symb-table) accumulator)))
                (begin (let ([program-string (program->string (shuffle accumulator))])
                         (print program-string writer-buffer)
                         (set! writer-buffer-size (+ writer-buffer-size
                                                     (string-length program-string))))
                       (set! accumulator '())
                       (set! accumulating #f)
                       (when (is-def? sexp)
                         (hash-set! symb-table (cadr sexp) (symb-gen)))
                       (let ([program-string (program->string (list (rename-symbs sexp symb-table)))])
                         (print program-string writer-buffer)
                         (set! writer-buffer-size (+ writer-buffer-size
                                                     (string-length program-string))))
                       (when (> writer-buffer-size BUFFER-THRESHOLD)
                         (print (get-output-string writer-buffer) out)
                         (set! writer-buffer (open-output-string))
                         (set! writer-buffer-size 0)))))))))

(define (make-progress-bar sofar total)
  (let ([chars (quotient (* 20 sofar) total)])
    (display #\return)
    (display (format "Progress: [~a~a] ~a%"
                     (make-string chars #\=)
                     (make-string (- 20 chars) #\space)
                     (quotient (* 100 sofar) total)))))

(define (create-mutants fname num)
  (let* ([seeds (range 0 num)]
         [outs (map (lambda (n)
                      (open-output-file
                       (format "mutant_~a_of_~a" n fname)
                       #:exists 'replace))
                    seeds)]
         [writers (map writer outs seeds)]
         [total-size (file-size fname)])
    (letrec ([write-all
              (lambda (infile)
                (let [(sexp (read infile))]
                  (when (not (eof-object? sexp))
                    (make-progress-bar (file-position infile) total-size)
                    (map (lambda (w) (w sexp)) writers)
                    (write-all infile))))])
      (let ([input-file (open-input-file fname)])
        (write-all input-file)
        (map (lambda (w) (w 'flush)) writers) ; flush all the writer buffers
        (display #\return) ; set the progress to 100 :)
        (display (format "Progress: [~a] 100%\n" (make-string 20 #\=)))
        (close-input-port input-file)
        (map close-output-port outs)))))

(let* ([args (current-command-line-arguments)]
       [fname (vector-ref args 0)]
       [num (string->number (vector-ref args 1))])
  (create-mutants fname num)
  (void))

