(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  leq
  ((x Nat) (y Nat)) Bool
  (match x
    ((zero true)
     ((succ z)
      (match y
        ((zero false)
         ((succ x2) (leq z x2))))))))
(define-fun-rec
  ordered
  ((x list)) Bool
  (match x
    ((nil true)
     ((cons y z)
      (match z
        ((nil true)
         ((cons y2 xs) (and (leq y y2) (ordered (cons y2 xs))))))))))
(define-fun
  sort2
  ((x Nat) (y Nat)) list
  (ite (leq x y) (cons x (cons y nil)) (cons y (cons x nil))))
(define-funs-rec
  ((evens
    ((x list)) list)
   (odds
    ((x list)) list))
  ((match x
     ((nil nil)
      ((cons y xs) (cons y (odds xs)))))
   (match x
     ((nil nil)
      ((cons y xs) (evens xs))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  pairs
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z x2)
      (match y
        ((nil (cons z x2))
         ((cons x3 x4) (++ (sort2 z x3) (pairs x2 x4)))))))))
(define-fun
  stitch
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (pairs xs y))))))
(define-fun-rec
  bmerge
  ((x list) (y list)) list
  (match x
    ((nil nil)
     ((cons z x2)
      (match y
        ((nil (cons z x2))
         ((cons x3 x4)
          (let
            ((fail
                (stitch (bmerge (evens (cons z x2)) (evens (cons x3 x4)))
                  (bmerge (odds (cons z x2)) (odds (cons x3 x4))))))
            (match x2
              ((nil
                (match x4
                  ((nil (sort2 z x3))
                   ((cons x5 x6) fail))))
               ((cons x7 x8) fail)))))))))))
(define-fun-rec
  bsort
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y z)
      (match z
        ((nil (cons y nil))
         ((cons x2 x3)
          (bmerge (bsort (evens (cons y (cons x2 x3))))
            (bsort (odds (cons y (cons x2 x3))))))))))))
(assert (not (forall ((xs list)) (ordered (bsort xs)))))
(check-sat)
