(declare-datatype Token ((A) (B) (C) (D) (ESC) (P) (Q) (R)))
(declare-datatype list ((nil) (cons (head Token) (tail list))))
(define-fun
  isSpecial
  ((x Token)) Bool
  (match x
    ((_ false)
     (ESC true)
     (P true)
     (Q true)
     (R true))))
(define-fun
  code
  ((x Token)) Token
  (match x
    ((_ x)
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
(assert
  (not
    (forall ((xs list) (ys list))
      (=> (= (escape xs) (escape ys)) (= xs ys)))))
(check-sat)
