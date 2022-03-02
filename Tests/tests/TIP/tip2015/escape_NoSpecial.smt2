(declare-datatype Token ((A) (B) (C) (D) (ESC) (P) (Q) (R)))
(declare-datatype list ((nil) (cons (head Token) (tail list))))
(define-fun
  isSpecial
  ((x Token)) Bool
  (match x
    ((__ false)
     (ESC true)
     (P true)
     (Q true)
     (R true))))
(define-fun
  ok
  ((x Token)) Bool
  (or (not (isSpecial x))
    (match x
      ((__ false)
       (ESC true)))))
(define-fun-rec
  formula
  ((x list)) Bool
  (match x
    ((nil true)
     ((cons y xs) (and (ok y) (formula xs))))))
(define-fun
  code
  ((x Token)) Token
  (match x
    ((__ x)
     (ESC ESC)
     (P A)
     (Q B)
     (R C))))
(define-fun-rec
  escape
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (ite
        (isSpecial y) (cons ESC (cons (code y) (escape xs)))
        (cons y (escape xs)))))))
(assert (not (forall ((xs list)) (formula (escape xs)))))
(check-sat)
