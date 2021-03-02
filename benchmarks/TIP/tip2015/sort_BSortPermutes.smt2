(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun lam (Int) fun12)
(declare-const lam2 fun1)
(declare-fun apply1 (fun1 Int) fun12)
(declare-fun apply12 (fun12 Int) Bool)
(define-fun
  sort2
  ((x Int) (y Int)) list
  (ite (<= x y) (cons x (cons y nil)) (cons y (cons x nil))))
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
  elem
  ((x Int) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  deleteBy
  ((x fun1) (y Int) (z list)) list
  (match z
    ((nil nil)
     ((cons y2 ys)
      (ite (apply12 (apply1 x y) y2) ys (cons y2 (deleteBy x y ys)))))))
(define-fun-rec
  isPermutation
  ((x list) (y list)) Bool
  (match x
    ((nil
      (match y
        ((nil true)
         ((cons z x2) false))))
     ((cons x3 xs)
      (and (elem x3 y) (isPermutation xs (deleteBy lam2 x3 y)))))))
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
(assert (forall ((x4 Int)) (= (apply1 lam2 x4) (lam x4))))
(assert
  (forall ((x4 Int) (x5 Int)) (= (apply12 (lam x4) x5) (= x4 x5))))
(assert (not (forall ((xs list)) (isPermutation (bsort xs) xs))))
(check-sat)
