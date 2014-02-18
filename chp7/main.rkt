#lang racket
(require parser-tools/lex)
(require parser-tools/yacc)

;; Chapter 7
;; Implementation of untyped lambda calculas.

;; Assertion
(define (assert condition message)
  (if (not condition)
      (error message)
      (void)))

;; Term definitions.
(struct Term (info))
(struct TmVar Term (index ctxlength))
(struct TmAbs Term (term name))
(struct TmApp Term (tmabs tmarg))

;; Variable name context implementation.
;; We use a list of strings to store variable names currently.
;; Note: variable indexes are used as the static distances in chapter 6.

;; this is the internal structure.
(struct CtxImpl (length names))

;; Ctx from a list of names.
(define (make-ctx . names)
  (CtxImpl (length names) names))

;; Get length of the context.
(define (ctxlength ctx)
  (CtxImpl-length ctx))

;; Get all the names in the context.
(define (ctxnames ctx)
  (CtxImpl-names ctx))

;; Get the name on the index.
(define (index->name ctx index)
  (assert (and (>= index 0) (< index (ctxlength ctx)))
          (format "ctxlength: ~a, index: ~a." (ctxlength ctx) index))
  
  (list-ref (CtxImpl-names ctx) index))

;; Get the index of the name, returns false if no such name in the ctx.
(define (name->index ctx name)
  (let loop ([index 0] [names (CtxImpl-names ctx)])
    (cond
      [(null? names) #f]
      [(string=? name (car names)) index]
      [else (loop (+ index 1) (cdr names))])))

;; Shifts the context by inserting a new name at index 0.
(define (ctxshiftin ctx name)
  (CtxImpl (+ (ctxlength ctx) 1) (cons name (CtxImpl-names ctx))))

;; Append the new name after the context.
(define (ctxappend ctx name)
  (CtxImpl (+ (ctxlength ctx) 1) (append (ctxnames ctx) name)))

;; Merge two ctx into one
(define (ctxmerge master slave)
  (let loop ([ctx master] [names (ctxnames slave)])
    (if (null? names)
        ctx
        (let ([name (car names)] [names (cdr names)])
          (if (name->index ctx name)
              (loop ctx names)
              (loop (ctxshiftin ctx name) names))))))

;; Pick a distinct name in ctx.
;; Returns a new context with the distinct name added and the name.
(define (pickfreshname ctx name)
  (if (name->index ctx name)
      (pickfreshname ctx (string-append name "'"))
      (values (ctxshiftin ctx name) name)))

;; Term to a readable string.
(define (term->string ctx term)
  (match term
    [(TmVar fi index length)
     (assert (= length (ctxlength ctx))
             (format "variable at ~a has a wrong ctx expect: ~a, got: ~a"
                     fi length (ctxlength ctx)))
     (index->name ctx index)]
    
    [(TmAbs _ t1 name)
     (let-values ([(ctx_1 name_1) (pickfreshname ctx name)])
       (format "(lambda (~a) ~a)" name_1 (term->string ctx_1 t1)))]
    
    [(TmApp _ t1 t2)
     (format "(~a ~a)" (term->string ctx t1) (term->string ctx t2))]))


;; Term shift & substitution.

(define (term-shift term d (c 0))
  (define (shift/cut idx)
    (if (>= idx c) (+ idx d) idx))
  
  (match term
    [(TmVar fi index length) (TmVar fi (shift/cut index) (+ length d))]
    [(TmAbs fi t1 name) (TmAbs fi (term-shift t1 d (+ c 1)) name)]
    [(TmApp fi t1 t2) (TmApp fi (term-shift t1 d c) (term-shift t2 d c))]))

(define (term-substitute term j s (c 0))
  (match term
    [(TmVar fi index length) (if (= index (+ c j)) (term-shift s c) term)]
    [(TmAbs fi t1 name) (TmAbs fi (term-substitute t1 j s (+ c 1)) name)]
    [(TmApp fi t1 t2) (TmApp fi (term-substitute t1 j s c) (term-substitute t2 j s c))]))

(define (beta-reduce term s)
  (term-shift (term-substitute term 0 (term-shift s 1)) -1))


;; Eval
(define (isval term)
  (match term
    [(TmAbs _ _ _) #t]
    [_ #f]))

(define (eval1 term)
  (match term
    [(TmApp fi (TmAbs _ t1 name) v2) #:when (isval v2) (beta-reduce t1 v2)]
    [(TmApp fi v1 t2) #:when (isval v1) (TmApp fi v1 (eval1 t2))]
    [(TmApp fi t1 t2) (TmApp fi (eval1 t1) t2)]
    [_ (raise 'NoRuleApplies)]))

(define (eval term)
  (with-handlers ([(lambda (e) (eq? e 'NoRuleApplies)) (lambda (e) term)])
    (eval (eval1 term))))


;; Simple parser implementation

(define-tokens lambda-tokens
  (LAMBDA ID OPEN CLOSE SEMICOLON EOF))

(define lambda-lex
  (lexer-src-pos
   ["lambda" (token-LAMBDA 'lambda)]
   ["(" (token-OPEN 'open)]
   [")" (token-CLOSE 'close)]
   [";" (token-SEMICOLON 'semicolon)]
   [(eof) (token-EOF 'eof)]
   [(repetition 1 +inf.0 alphabetic) (token-ID lexeme)]
   [whitespace (return-without-pos (lambda-lex input-port))]
   [any-char (let [(pos start-pos)]
               (eprintf "WARNING: unkonw char '~a' at line ~a colum ~a\n"
                        lexeme (position-line pos) (+ 1 (position-col pos)))
               (return-without-pos (lambda-lex input-port)))]))

;; Terms used in parsing
(struct AstNode (info))
(struct AstVar AstNode (name))
(struct AstAbs AstNode (name body))
(struct AstApp AstNode (abs arg))

;; Parse terms.
(define (lambda-parse in)
  (port-count-lines! in)
  (define (gen) (lambda-lex in))
  (define lalr-parser
    (parser
     (src-pos)
     (tokens lambda-tokens)
     (start term-list)
     (end EOF)
     (error (lambda (ok name value start-pos end-pos)
              (eprintf "ERROR: invalid token '~a' at line ~a column ~a\n"
                      name (position-line start-pos) (position-col start-pos))))
     (grammar
      [term
       ((ID) (AstVar $1-start-pos $1))
       ((LAMBDA ID term) (AstAbs $1-start-pos $2 $3))
       ((term term) (AstApp 'dymmy-location $1 $2))
       ((OPEN term CLOSE) $2)]
      [term-list
       (() '())
       ((term-list term SEMICOLON) (cons $2 $1))])))
  (reverse (lalr-parser gen)))

;; Normalize term, returns a ctx and the normalized term.
;; Note: term is AstNode.
(define (normalize term)
  ;; Get free varable context from the term.
  (define (get-frees-ctx frees binds term)
      (match term
        [(AstVar _ name)
         (if (name->index binds name)
             frees
             (if (name->index frees name)
                 frees
                 (ctxshiftin frees name)))]
        
        [(AstAbs _ name body)
         (get-frees-ctx frees (ctxshiftin binds name) body)]
        
        [(AstApp _ abs arg)
         (let ([absfrees (get-frees-ctx frees binds abs)]
               [argfrees (get-frees-ctx frees binds arg)])
           (ctxmerge absfrees argfrees))]))
  
  (define frees (get-frees-ctx (make-ctx) (make-ctx) term))
  
  (define (normalize-rec term binds)
    (match term
      [(AstVar fi name)
       (cond
         [(name->index binds name) => (lambda (idx)
                                        (TmVar fi
                                               idx
                                               (+ (ctxlength binds) (ctxlength frees))))]
         [(name->index frees name) => (lambda (idx)
                                        (TmVar fi
                                               (+ idx (ctxlength binds))
                                               (+ (ctxlength binds) (ctxlength frees))))]

         [else (assert #f (format "Should not reach here: ~a\n" term))])]
      
      [(AstAbs fi name body)
       (TmAbs fi (normalize-rec body (ctxshiftin binds name)) name)]
      
      [(AstApp fi abs arg)
       (TmApp fi (normalize-rec abs binds) (normalize-rec arg binds))]))
  
  ;; let's get the result
  (values frees (normalize-rec term (make-ctx))))

;; main starting point
(for-each (lambda (term)
            (let-values ([(ctx term) (normalize term)])
              (printf "~a\n" (term->string ctx (eval term)))))
          (lambda-parse (current-input-port)))
