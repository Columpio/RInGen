(declare-datatype
  list3 ((nil3) (cons3 (head3 Bool) (tail3 list3))))
(declare-datatype It ((A) (B) (C)))
(declare-datatype list2 ((nil2) (cons2 (head2 It) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(define-fun-rec
  removeOne
  ((x It) (y list)) list
  (match y
    ((nil nil)
     ((cons z x2) (cons (cons2 x z) (removeOne x x2))))))
(define-fun-rec
  removeOne2
  ((x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y xs) (cons xs (removeOne y (removeOne2 xs)))))))
(define-fun-rec
  or2
  ((x list3)) Bool
  (match x
    ((nil3 false)
     ((cons3 y xs) (or y (or2 xs))))))
(define-fun-rec
  isPrefix
  ((x list2) (y list2)) Bool
  (match x
    ((nil2 true)
     ((cons2 z x2)
      (match y
        ((nil2 false)
         ((cons2 x3 x4) (and (= z x3) (isPrefix x2 x4)))))))))
(define-fun-rec
  isRelaxedPrefix
  ((x list2) (y list2)) Bool
  (match x
    ((nil2 true)
     ((cons2 z x2)
      (match x2
        ((nil2 true)
         ((cons2 x3 x4)
          (match y
            ((nil2 false)
             ((cons2 x5 x6)
              (ite
                (= z x5) (isRelaxedPrefix (cons2 x3 x4) x6)
                (isPrefix (cons2 x3 x4) (cons2 x5 x6)))))))))))))
(define-fun-rec
  spec
  ((ys list2) (x list)) list3
  (match x
    ((nil nil3)
     ((cons y z) (cons3 (isPrefix y ys) (spec ys z))))))
(define-fun
  spec2
  ((x list2) (y list2)) Bool (or2 (spec y (cons x (removeOne2 x)))))
(assert
  (not
    (forall ((xs list2) (ys list2))
      (= (isRelaxedPrefix xs ys) (spec2 xs ys)))))
(check-sat)
