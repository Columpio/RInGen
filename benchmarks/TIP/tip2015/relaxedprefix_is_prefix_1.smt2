(declare-datatype It ((A) (B) (C)))
(declare-datatype list ((nil) (cons (head It) (tail list))))
(define-fun-rec
  isPrefix
  ((x list) (y list)) Bool
  (match x
    ((nil true)
     ((cons z x2)
      (match y
        ((nil false)
         ((cons x3 x4) (and (= z x3) (isPrefix x2 x4)))))))))
(define-fun-rec
  isRelaxedPrefix
  ((x list) (y list)) Bool
  (match x
    ((nil true)
     ((cons z x2)
      (match x2
        ((nil true)
         ((cons x3 x4)
          (match y
            ((nil false)
             ((cons x5 x6)
              (ite
                (= z x5) (isRelaxedPrefix (cons x3 x4) x6)
                (isPrefix (cons x3 x4) (cons x5 x6)))))))))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(assert
  (not
    (forall ((xs list) (ys list)) (isRelaxedPrefix xs (++ xs ys)))))
(check-sat)
