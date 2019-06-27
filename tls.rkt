#lang rackjure
(require sugar)
(require point-free)

; atom? :: x -> Bool
(define atom?
  (lambda (x)
    (and (not (pair? x))
         (not (null? x)))))

; lat? :: [a] -> Bool
(define lat?
  (lambda (ls)
    (cond
      [(null? ls) #f]
      [(null? (cdr ls)) #t]
      [(atom? (car ls)) (lat? (cdr ls))]
      [else #f])))

; member? :: a -> [Atom] -> Bool
(define member?
  (lambda (a lat)
    (cond
      [(null? lat) #f]
      [else (or (eq? (car lat) a)
                (member? a (cdr lat)))])))

; rember :: a -> [Atom] -> [Atom] | '()
(define rember
  (lambda (a lat)
    (cond
      [(null? lat) empty]
      [(eq? (car lat) a) (cdr lat)]
      [else (cons (car lat)
                  (rember a (cdr lat)))])))

; multirember :: a -> [Atom] -> [Atom] | '()
(define multirember
  (lambda (a lat)
    (cond
      [(null? lat) '()]
      [(eq? (car lat) a) 
       (multirember a (cdr lat))]
      [else (cons (car lat) 
                  (multirember a (cdr lat)))])))

; firsts :: [a] -> [a] | '()
(define firsts
  (lambda (l)
    (cond
      [(null? l) empty]
      [else (cons (car (car l))
                  (firsts (cdr l)))])))

(define insertR
  (lambda (new old lat)
    (cond
      [(null? lat) empty]
      [else (cond
              [(eq? (car lat) old)
                    (cons old
                          (cons new (cdr lat)))]
              [else
                (cons (car lat)
                      (insertR new old (cdr lat)))])])))

(define multiinsertR
  (lambda (new old ls)
    (letrec ((I (lambda (lat)
    (cond
      [(null? lat) empty]
      [else (cond
              [(equal? (car lat) old)
               (cons old 
                     (cons new 
                           (I (cdr lat))))]
              [else 
                (cons (car lat)
                      (I (cdr lat)))])]))))
      (I ls))))

(define multiinsertL
  (lambda (new old lat)
    (cond
      ((null? lat) empty)
      [else (cond
              [(equal? (car lat) old)
               (cons new 
                     (cons old (multiinsertL new old (cdr lat))))]
              [else
                (cons (car lat)
                      (multiinsertL new old (cdr lat)))])])))


(define (m-multiinsertL old new ls)
  (let loop ([ls ls])
    (match ls
      ['() '()]
      [(list x xs ...) (cons (if (equal? old x)
                               new
                               x)
                             (loop xs))])))

(define insertL
  (lambda (new old lat)
    (cond
      ((null? lat) empty)
      [else (cond
              [(equal? (car lat) old)
               (cons new lat)]
              [else 
                (cons (car lat)
                      (insertL new old (cdr lat)))])])))

(define multisubst
  (lambda (new old lat)
    (cond
      [(null? lat) empty]
      [else (cond
              [(equal? (car lat) old)
               (cons new (multisubst new old (cdr lat)))]
              [else
                (cons (car lat)
                      (multisubst new old (cdr lat)))])])))

(define tup+
  (lambda (tup1 tup2)
    (cond
      [(and (null? tup1) (null? tup2))
       empty]
      [else
        (cons (+ (car tup1) (car tup2))
              (tup+ (cdr tup1) (cdr tup2)))])))

(define length*
  (lambda (lat)
    (cond
      [(null? lat) 0]
      [else (add1 (length (cdr lat)))])))

(define rempick
  (lambda (n lat)
    (cond
      [(zero? (sub1 n)) (cdr lat)]
      [else (cons (car lat)
                  (rempick (sub1 n)
                           (cdr lat)))])))

(define no-nums
  (lambda (lat)
    (cond
      [(null? lat) empty]
      [else (cond
              [(number? (car lat)) (no-nums (cdr lat))]
              [else
                (cons (car lat) (no-nums (cdr lat)))])])))

(define all-nums
  (lambda (lat)
    (cond
      [(null? lat) empty] 
      [else (cond
              [(number? (car lat)) (cons (car lat) (all-nums (cdr lat)))]
              [else
                (all-nums (cdr lat))])])))

(define eqan?
  (lambda (a1 a2)
    (cond
      [(and (number? a1) (number? a2)) (= a1 a2)]
      [(or (number? a1) (number? a2)) #f]
      [else (eq? a1 a2)])))

(define split
  (lambda (str)
    (let [(lat (string->list str))]
      (let loop [(lat lat)]
        (cond
          [(null? lat) empty]
          [(equal? (car lat) '#\space) (list(loop (cdr lat)))]
          [else
            (cons (car lat) (loop (cdr lat)))])))))

(define convert
  (lambda (lat)
    (let loop ([i 0] [lat lat])
      (cond
        [(empty? lat) 0]
        [else
          (+ (* (expt 10 i) (car lat))
             (loop (+ i 1) (cdr lat)))]))))

(define flatten
  (lambda (ls)
    (cond
      [(null? ls) '()]
      [else
        (cond
          [(atom? (car ls))
           (cons (car ls) (flatten (cdr ls)))]
          [else
            (append (flatten (car ls))
                    (flatten (cdr ls)))])])))

(define (occur* a l)
  (cond
    [(null? l) 0]
    [(atom? (car l))
     (cond
       [(eq? (car l) a)
        (+ 1 (occur* a (cdr l)))]
       [else (occur* a (cdr l))])]
    [else
      (+ (occur* a (car l))
         (occur* a (cdr l)))]))

(define (subst* new_ old l)
  (cond
    [(null? l) '()]
    [(atom? (car l))
     (cond
       [(eq? (car l) old)
        (cons new_
              (subst*  new_ old (cdr l)))]
       [else (cons (car l) (subst* new_ old (cdr l)))])]
    [else
      (cons (subst* new_ old (car l))
            (subst* new_ old (cdr l)))]))

(define (insertL* new_ old l)
  (cond
    [(null? l) '()]
    [(atom? (car l))
     (cond
       [(eq? (car l) old)
        (cons new_
              (cons (car l)
                    (insertL* new_ old (cdr l))))]
       [else
         (cons (car l)
               (insertL* new_ old (cdr l)))])]
    [else
      (cons (insertL* new_ old (car l))
            (insertL* new_ old (cdr l)))]))

(define (member* a l)
  (cond
    [(null? l) #f]
    [(atom? (car l))
     (cond
       [(eq? (car l) a) #t]
       [else (member* a (cdr l))])]
    [else
      (or (member* a (car l))
          (member* a (cdr l)))]))

(define (leftmost l)
  (cond
    [(null? l) '()]
    [(atom? (car l)) (car l)]
    [else
      (leftmost (car l))]))

(define (rightmost ls)
  (cond
    [(null? ls) '()]
    [(null? (cdr ls))
     (if (atom? (car ls))
       (car ls)
       (rightmost (car ls)))]
    [else
      (rightmost (cdr ls))]))


(define (eqlist? l1 l2)
  (cond
    [(and (null? l1) (null? l2)) #t]
    [(and (atom? (car l1)) (atom? (car l2)))
     (if (equal? (car l1) (car l2))
       (eqlist? (cdr l1) (cdr l2))
       #f)]
    [(and (list? (car l1)) (list? (car l2)))
     (and (eqlist? (car l1) (car l2))
          (eqlist? (cdr l1) (cdr l2)))]
    [else #f]))

(define (between sep ls)
  (cond
    [(null? (cdr ls)) ls]
    [else
      (cons (car ls)
            (cons sep (between sep (cdr ls))))]))

(define (count-parens-all ls)
  (cond
    [(null? ls) 2]
    [(atom? (car ls)) (count-parens-all (cdr ls))]
    [else (+ (count-parens-all (car ls))
             (count-parens-all (cdr ls)))]))

(define (string-reverse str)
  (let loop ([str str])
    (cond
      [(equal? str "") ""]
      [else
        (string-append (string-reverse (substring str 1))
                       (substring str 0 1))])))

(define (palindrome? str)
  (if (equal? (string-reverse str) str)
    #t
    #f))


(define (substring? sub str)
  (cond
    [(> (string-length sub)
        (string-length str))
     #f]
    [(string=? sub (substring str 0 (string-length sub)))]
    [else (substring? sub (substring str 1 (string-length str)))]))

;(define (or-version-substring? sub str)
;    (cond
;      [(> (string-length sub)
;          (string-length str))
;       #f]
;      [else
;        (or (string=? sub (substring str 0 (string-length sub)))
;            (substring? sub (substring str 1 (string-length str))))]))
;
;(define (substring? sub str)
;  (let loop ([sub sub]
;             [str str])
;    (cond
;      [(> (string-length sub)
;          (string-length str))
;       #f]
;      [(string=? sub
;                 (substring str 0 (string-length sub)))]
;      [else
;        (loop sub (substring str 1 (string-length str)))])))
;
;(define (substring? sub str)
;  (let iter ([sub sub]
;             [i 0])
;    (cond
;      [(> (+ i (string-length sub))
;          (string-length str))
;       #f]
;      [(string=? sub
;                 (substring str i (+ i (string-length sub))))]
;      [else
;        (iter sub (+ i 1))])))

(define memoize
  (lambda (f)
    (define cache (make-hash))
    (lambda (x)
      (display cache)
      (hash-ref! cache
                 x
                 (lambda ()
                   (f x))))))

(define compose*
  (lambda fns
    (lambda (x)
      (foldr (lambda (f x) (f x))
             x
             fns))))

;(define multimap
;  (lambda args
;    (define ls (last args))
;    (define fns (drop-right args 1))
;    (foldl (lambda (f l) (map f l)) ls fns)))
;
(define map-c
  (lambda (f)
    (lambda (ls)
      (map f ls))))

(define (bubble-sort ls)
  (define (bubble ls)
    (cond
      [(null? (cdr ls)) ls]
      [(< (car ls) (cadr ls))
       (cons (car ls)
             (bubble (cdr ls)))]
      [else (cons (cadr ls)
                  (bubble (cons (car ls)
                                (cddr ls))))]))
  (define (bubble-iter i ls)
    (cond
      [(= i 0) ls]
      [else (bubble-iter (- i 1) (bubble ls))]))
  (bubble-iter (length ls) ls)) 

(define (ref i ls)
  (cond
    [(null? ls) '()]
    [(= i 0) (car ls)]
    [else (ref (sub1 i)
               (cdr ls))]))

(define (quicksort xs)
  (if (null? xs)
    '()
    (let ([x (car xs)]
          [xs (cdr xs)])
      (append (quicksort
                (filter (lambda (a)
                          (< a x))
                        xs))
              (list x)
              (quicksort
                (filter (lambda (a)
                          (>= a x))
                        xs))))))

(define (randlist n m size)
  (for/list ([i size])
    (random n m)))

(define filter-preds
  (lambda preds
    (lambda (ls)
      (filter (apply conjoin preds) ls))))

(define my-conjoin
  (lambda preds
    (lambda (x)
      (if (null? preds)
        #t
        (and ((car preds) x)
             ((apply my-conjoin (cdr preds)) x))))))

(define (foldl1 f ls)
  (if (null? ls)
    (error "empty list")
    (foldl f (car ls) (cdr ls))))

(define filtermap-wind
  (curryr (wind-pre compose
                    (curry filter)
                    (curry map))))

(define filtermap-nowind
  (curryr (compose compose
                   (join (curry filter)
                         (curry map)))))

(define lambda-literal-length
  (curry foldl #λ(add1 %2) 0))

(define (filtermap* f p)
  (compose #λ(filter p %)
           #λ(map f %)))

(define filtermap-literal
  (curry #λ(filter %2 (map %1 %3))))

(define compose-all
  (lambda fs
    (foldl compose identity fs)))

(define (f-string los)
  (foldr string-append "" (map ->string los)))

(define (flip f)
  (lambda (a b . cs)
    (apply f b a cs)))

(define/match (group n ls)
  [(_ '()) '()]
  [(n (list xs ...))
   (if (> n 0)
     (if (< n (length ls))
       (cons (take xs n)
             (group n (drop xs n)))
       ls)
     (error "negative or zero n"))])
     

(define rand-fun
  (λ (seed) (modulo (* seed 16807) 2147483647)))

(define (iterate f x)
  (stream-cons x (iterate f (f x))))

(define (make-rng seed)
  (stream-map #λ(modulo % 100) (stream-iterate rand-fun seed)))
    
;hash_hash = defaultdict(dict)
;hash_hash["first"]["second"] = value
;That avoids having the check
;if "first" not in hash_hash:
;   hash_hash["first"] = {}
(define (dict-set-with-default! hh fst snd value)
 (hash-set! (hash-ref! hh fst make-hash) snd value))
;Functionally:
;(hash-update h 'first  (lambda (h-first) (hash-set h-first 'second value) hash)
;Or currying the update function?
