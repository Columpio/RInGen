(declare-sort sk 0)
(declare-datatype
  pair3 ((pair22 (proj1-pair2 sk) (proj2-pair2 sk))))
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-datatype Q ((Q2 (proj1-Q list) (proj2-Q list))))
(declare-datatype Maybe2 ((Nothing2) (Just2 (proj1-Just2 sk))))
(declare-datatype Maybe ((Nothing) (Just (proj1-Just Q))))
(declare-datatype
  E
  ((Empty) (EnqL (proj1-EnqL sk) (proj2-EnqL E))
   (EnqR (proj1-EnqR E) (proj2-EnqR sk)) (DeqL (proj1-DeqL E))
   (DeqR (proj1-DeqR E)) (App (proj1-App E) (proj2-App E))))
(define-fun-rec
  take
  ((x Int) (y list)) list
  (ite
    (<= x 0) nil
    (match y
      ((nil nil)
       ((cons z xs) (cons z (take (- x 1) xs)))))))
(define-fun
  tail2
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs) xs))))
(define-fun-rec
  length
  ((x list)) Int
  (match x
    ((nil 0)
     ((cons y l) (+ 1 (length l))))))
(define-fun-rec
  last
  ((x list)) Maybe2
  (match x
    ((nil Nothing2)
     ((cons y z)
      (match z
        ((nil (Just2 y))
         ((cons x2 x3) (last (cons x2 x3)))))))))
(define-fun-rec
  init
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y z)
      (match z
        ((nil nil)
         ((cons x2 x3) (cons y (init (cons x2 x3))))))))))
(define-fun
  fstR
  ((x Q)) Maybe2
  (match x
    (((Q2 y z)
      (let
        ((fail
            (match z
              ((nil Nothing2)
               ((cons y2 x2) (Just2 y2))))))
        (match y
          ((nil fail)
           ((cons x3 x4)
            (match x4
              ((nil
                (match z
                  ((nil (Just2 x3))
                   ((cons x5 x6) fail))))
               ((cons x7 x8) fail)))))))))))
(define-fun
  fromMaybe2
  ((x sk) (y Maybe2)) sk
  (match y
    ((Nothing2 x)
     ((Just2 z) z))))
(define-fun
  fromMaybe
  ((x Q) (y Maybe)) Q
  (match y
    ((Nothing x)
     ((Just z) z))))
(define-fun
  empty
  () Q (Q2 nil nil))
(define-fun-rec
  drop
  ((x Int) (y list)) list
  (ite
    (<= x 0) y
    (match y
      ((nil nil)
       ((cons z xs1) (drop (- x 1) xs1))))))
(define-fun
  halve
  ((x list)) pair
  (let ((k (div (length x) 2))) (pair2 (take k x) (drop k x))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  list2
  ((x E)) list
  (match x
    ((Empty nil)
     ((EnqL y e) (cons y (list2 e)))
     ((EnqR e2 z) (++ (list2 e2) (cons z nil)))
     ((DeqL e3) (tail2 (list2 e3)))
     ((DeqR e4) (init (list2 e4)))
     ((App a1 b2) (++ (list2 a1) (list2 b2))))))
(define-fun-rec
  reverse
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs) (++ (reverse xs) (cons y nil))))))
(define-fun
  enqL
  ((x sk) (y Q)) Q
  (match y
    (((Q2 xs ys)
      (match ys
        ((nil
          (match (halve (cons x xs))
            (((pair2 as1 bs) (Q2 as1 (reverse bs))))))
         ((cons z x2) (Q2 (cons x xs) (cons z x2)))))))))
(define-fun
  mkQ
  ((x list) (y list)) Q
  (match x
    ((nil (match (halve y) (((pair2 as1 bs1) (Q2 (reverse bs1) as1)))))
     ((cons z x2)
      (match y
        ((nil
          (match (halve (cons z x2))
            (((pair2 as12 bs) (Q2 as12 (reverse bs))))))
         ((cons x3 x4) (Q2 (cons z x2) (cons x3 x4)))))))))
(define-fun
  +++
  ((x Q) (y Q)) Q
  (match x
    (((Q2 xs ys)
      (match y
        (((Q2 vs ws) (mkQ (++ xs (reverse ys)) (++ (reverse vs) ws)))))))))
(define-fun
  deqL
  ((x Q)) Maybe
  (match x
    (((Q2 y z)
      (match y
        ((nil
          (match z
            ((nil Nothing)
             ((cons x2 x3)
              (match x3
                ((nil (Just empty))
                 ((cons x4 x5) Nothing)))))))
         ((cons x6 xs) (Just (mkQ xs z)))))))))
(define-fun
  deqR
  ((x Q)) Maybe
  (match x
    (((Q2 y z)
      (let
        ((fail
            (match z
              ((nil Nothing)
               ((cons y2 ys) (Just (mkQ y ys)))))))
        (match y
          ((nil fail)
           ((cons x2 x3)
            (match x3
              ((nil
                (match z
                  ((nil (Just empty))
                   ((cons x4 x5) fail))))
               ((cons x6 x7) fail)))))))))))
(define-fun
  enqR
  ((x Q) (y sk)) Q (match x (((Q2 xs ys) (mkQ xs (cons y ys))))))
(define-fun-rec
  queue
  ((x E)) Q
  (match x
    ((Empty empty)
     ((EnqL y e) (enqL y (queue e)))
     ((EnqR e2 z) (enqR (queue e2) z))
     ((DeqL e3) (let ((q (queue e3))) (fromMaybe q (deqL q))))
     ((DeqR e4) (let ((r (queue e4))) (fromMaybe r (deqR r))))
     ((App a1 b2) (+++ (queue a1) (queue b2))))))
(assert
  (not (forall ((e E)) (= (fstR (queue e)) (last (list2 e))))))
(check-sat)
