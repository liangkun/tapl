#lang racket
(require parser-tools/lex)
(require parser-tools/yacc)

;; Chapter 4
;; Implementation of untyped arithmetic expressions.


;; term definitions
(struct Term (info))
(struct TmTrue Term ())
(struct TmFalse Term ())
(struct TmIf Term (tmcond tmthen tmelse))
(struct TmZero Term ())
(struct TmSucc Term (term))
(struct TmPred Term (term))
(struct TmIsZero Term (term))

;; check if a term is a numeric value
(define (isnumericval term)
  (match term
    [(TmZero _) #t]
    [(TmSucc _ term) (isnumericval term)]
    [_ #f]))

;; check if a term is a value
(define (isval term)
  (match term
    [(TmTrue _) #t]
    [(TmFalse _) #t]
    [t (isnumericval t)]))

;; pretty print values
(define (val-to-string val)
  (match val
    [(TmTrue _) "true"]
    [(TmFalse _) "false"]
    [(TmZero _) "0"]
    [(TmSucc _ t1) #:when (isnumericval t1) (format "(succ ~a)" (val-to-string t1))]
    [_ (error 'NotValue)]))


;; eval functions definitions

(define dummyinfo 'dummyinfo)

;; eval a single step
(define (eval1 term)
  (match term
    [(TmIf _ (TmTrue _) t1 t2) t1]
    [(TmIf _ (TmFalse _) t1 t2) t2]
    [(TmIf fi t1 t2 t3) (let [(t1_1 (eval1 t1))]
                          (TmIf fi t1_1 t2 t3))]
    [(TmSucc fi t1) (let [(t1_1 (eval1 t1))]
                      (TmSucc fi t1_1))]
    [(TmPred _ (TmZero _)) (TmZero dummyinfo)]
    [(TmPred _ (TmSucc _ nv)) #:when (isnumericval nv) nv]
    [(TmPred fi t1) (let [(t1_1 (eval1 t1))]
                      (TmPred fi t1_1))]
    [(TmIsZero _ (TmZero _)) (TmTrue dummyinfo)]
    [(TmIsZero _ (TmSucc _ nv)) #:when (isnumericval nv) (TmFalse dummyinfo)]
    [(TmIsZero fi t1) (let [(t1_1 (eval1 t1))]
                        (TmIsZero fi t1_1))]
    [_ (raise 'NoRuleApplies)]))

(define (eval term)
  (with-handlers [((lambda (e) (eq? e 'NoRuleApplies)) (lambda (e) term))]
    (let ((term (eval1 term)))
      (eval term))))


;; simple parser implementation

(define-empty-tokens arith-token
  (TRUE FALSE IF THEN ELSE ZERO SUCC PRED ISZERO OPEN CLOSE EOF))

(define arith-lex
  (lexer-src-pos
   ["true" (token-TRUE)]
   ["false" (token-FALSE)]
   ["if" (token-IF)]
   ["then" (token-THEN)]
   ["else" (token-ELSE)]
   ["0" (token-ZERO)]
   ["succ" (token-SUCC)]
   ["pred" (token-PRED)]
   ["iszero" (token-ISZERO)]
   ["(" (token-OPEN)]
   [")" (token-CLOSE)]
   [(eof) (token-EOF)]
   [whitespace (return-without-pos (arith-lex input-port))]
   [any-char (let [(pos start-pos)]
               (printf "WARNING: unkonw char '~a' at line ~a colum ~a\n"
                       lexeme (position-line pos) (+ 1 (position-col pos)))
               (return-without-pos (arith-lex input-port)))]))

(define (arith-parse in)
  (port-count-lines! in)
  (define (gen) (arith-lex in))
  ((parser
    (src-pos)
    (tokens arith-token)
    (start term)
    (end EOF)
    (error (lambda (ok name value start-pos end-pos)
             (printf "ERROR: invalid token '~a' at line ~a column ~a\n"
                     name (position-line start-pos) (position-col start-pos))))
    (grammar
     [term
      ((TRUE) (TmTrue $1-start-pos))
      ((FALSE) (TmFalse $1-start-pos))
      ((ZERO) (TmZero $1-start-pos))
      ((OPEN term CLOSE) $2)
      ((IF term THEN term ELSE term) (TmIf $1-start-pos $2 $4 $6))
      ((SUCC term) (TmSucc $1-start-pos $2))
      ((PRED term) (TmPred $1-start-pos $2))
      ((ISZERO term) (TmIsZero $1-start-pos $2))]))
   gen))


;; main starting point
(printf "~a\n"
        (val-to-string (eval (arith-parse (current-input-port)))))

