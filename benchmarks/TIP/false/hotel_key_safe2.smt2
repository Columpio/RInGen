(declare-datatype
  pair6 ((pair25 (proj1-pair5 Int) (proj2-pair5 Bool))))
(declare-datatype
  pair5 ((pair24 (proj1-pair4 Int) (proj2-pair4 Int))))
(declare-datatype Maybe ((Nothing2) (Just2 (proj1-Just2 Int))))
(declare-datatype
  pair ((pair2 (proj1-pair Int) (proj2-pair Maybe))))
(declare-datatype
  Map5
  ((Rest4 (proj1-Rest4 Int))
   (Slot4 (proj1-Slot4 Int) (proj2-Slot4 Map5))))
(declare-datatype
  Reach
  ((Init (proj1-Init Map5))
   (CheckIn (proj1-CheckIn Int)
     (proj2-CheckIn Int) (proj3-CheckIn Int) (proj4-CheckIn Reach))
   (EnterRoom (proj1-EnterRoom Int)
     (proj2-EnterRoom Int) (proj3-EnterRoom pair5)
     (proj4-EnterRoom Reach))
   (ExitRoom (proj1-ExitRoom Int)
     (proj2-ExitRoom Int) (proj3-ExitRoom Reach))))
(declare-datatype
  Map3
  ((Rest (proj1-Rest Maybe))
   (Slot (proj1-Slot Maybe) (proj2-Slot Map3))))
(declare-datatype
  Map2
  ((Rest5 (proj1-Rest5 Bool))
   (Slot5 (proj1-Slot5 Bool) (proj2-Slot5 Map2))))
(declare-datatype
  pair4 ((pair23 (proj1-pair3 Int) (proj2-pair3 Map2))))
(declare-datatype
  Map
  ((Rest3 (proj1-Rest3 Map2))
   (Slot3 (proj1-Slot3 Map2) (proj2-Slot3 Map))))
(declare-datatype
  Map4
  ((Rest2 (proj1-Rest2 Map))
   (Slot2 (proj1-Slot2 Map) (proj2-Slot2 Map4))))
(declare-datatype
  State
  ((State2 (proj1-State Map3)
     (proj2-State Map5) (proj3-State Map2) (proj4-State Map4)
     (proj5-State Map5) (proj6-State Map) (proj7-State Map2))))
(declare-datatype Maybe2 ((Nothing) (Just (proj1-Just State))))
(declare-datatype
  pair3 ((pair22 (proj1-pair2 Int) (proj2-pair2 Map))))
(define-fun
  safe
  ((x State)) Map2 (match x (((State2 y z x2 x3 x4 x5 x6) x6))))
(define-fun
  roomk
  ((x State)) Map5 (match x (((State2 y z x2 x3 x4 x5 x6) x4))))
(define-fun
  owns
  ((x State)) Map3 (match x (((State2 y z x2 x3 x4 x5 x6) y))))
(define-fun
  issued
  ((x State)) Map2 (match x (((State2 y z x2 x3 x4 x5 x6) x2))))
(define-fun
  isin
  ((x State)) Map (match x (((State2 y z x2 x3 x4 x5 x6) x5))))
(define-fun-rec
  inj-upto1
  ((x Int) (y Int) (z Map5)) Bool
  (ite
    (= x 0) true
    (match z
      (((Rest4 y2) (distinct y y2))
       ((Slot4 y3 m1) (and (distinct y y3) (inj-upto1 (- x 1) y m1)))))))
(define-fun-rec
  inj
  ((x Int) (y Map5)) Bool
  (ite
    (= x 0) true
    (match y
      (((Rest4 z) false)
       ((Slot4 x2 m) (and (inj (- x 1) m) (inj-upto1 x x2 m)))))))
(define-fun
  empty2
  () Map (Rest3 (Rest5 false)))
(define-fun
  empty
  () Map2 (Rest5 false))
(define-fun
  currk
  ((x State)) Map5 (match x (((State2 y z x2 x3 x4 x5 x6) z))))
(define-fun
  cards
  ((x State)) Map4 (match x (((State2 y z x2 x3 x4 x5 x6) x3))))
(define-fun-rec
  <=>
  ((x Map2) (y Map2)) Bool
  (match x
    (((Rest5 z)
      (match y
        (((Rest5 y2) (= z y2))
         ((Slot5 y3 q) (and (= z y3) (<=> (Rest5 z) q))))))
     ((Slot5 x2 p)
      (match y
        (((Rest5 y4) (and (= x2 y4) (<=> p (Rest5 y4))))
         ((Slot5 y5 r) (and (= x2 y5) (<=> p r)))))))))
(define-fun-rec
  !=5
  ((x Map2) (y pair6)) Map2
  (match x
    (((Rest5 z)
      (match y
        (((pair25 x2 y2)
          (ite
            (= x2 0) (Slot5 y2 (Rest5 z))
            (Slot5 z (!=5 (Rest5 z) (pair25 (- x2 1) y2))))))))
     ((Slot5 x3 m1)
      (match y
        (((pair25 x4 y3)
          (ite
            (= x4 0) (Slot5 y3 m1)
            (Slot5 x3 (!=5 m1 (pair25 (- x4 1) y3)))))))))))
(define-fun
  add
  ((x Int) (y Map2)) Map2 (!=5 y (pair25 x true)))
(define-fun-rec
  range
  ((x Map5)) Map2
  (match x
    (((Rest4 y) (add y empty))
     ((Slot4 z m) (add z (range m))))))
(define-fun
  rem
  ((x Int) (y Map2)) Map2 (!=5 y (pair25 x false)))
(define-fun-rec
  !=4
  ((x Map5) (y pair5)) Map5
  (match x
    (((Rest4 z)
      (match y
        (((pair24 x2 y2)
          (ite
            (= x2 0) (Slot4 y2 (Rest4 z))
            (Slot4 z (!=4 (Rest4 z) (pair24 (- x2 1) y2))))))))
     ((Slot4 x3 m1)
      (match y
        (((pair24 x4 y3)
          (ite
            (= x4 0) (Slot4 y3 m1)
            (Slot4 x3 (!=4 m1 (pair24 (- x4 1) y3)))))))))))
(define-fun-rec
  !=3
  ((x Map) (y pair4)) Map
  (match x
    (((Rest3 z)
      (match y
        (((pair23 x2 y2)
          (ite
            (= x2 0) (Slot3 y2 (Rest3 z))
            (Slot3 z (!=3 (Rest3 z) (pair23 (- x2 1) y2))))))))
     ((Slot3 x3 m1)
      (match y
        (((pair23 x4 y3)
          (ite
            (= x4 0) (Slot3 y3 m1)
            (Slot3 x3 (!=3 m1 (pair23 (- x4 1) y3)))))))))))
(define-fun-rec
  !=2
  ((x Map4) (y pair3)) Map4
  (match x
    (((Rest2 z)
      (match y
        (((pair22 x2 y2)
          (ite
            (= x2 0) (Slot2 y2 (Rest2 z))
            (Slot2 z (!=2 (Rest2 z) (pair22 (- x2 1) y2))))))))
     ((Slot2 x3 m1)
      (match y
        (((pair22 x4 y3)
          (ite
            (= x4 0) (Slot2 y3 m1)
            (Slot2 x3 (!=2 m1 (pair22 (- x4 1) y3)))))))))))
(define-fun-rec
  !=
  ((x Map3) (y pair)) Map3
  (match x
    (((Rest z)
      (match y
        (((pair2 x2 y2)
          (ite
            (= x2 0) (Slot y2 (Rest z))
            (Slot z (!= (Rest z) (pair2 (- x2 1) y2))))))))
     ((Slot x3 m1)
      (match y
        (((pair2 x4 y3)
          (ite
            (= x4 0) (Slot y3 m1) (Slot x3 (!= m1 (pair2 (- x4 1) y3)))))))))))
(define-fun-rec
  !25
  ((x Map2) (y Int)) Bool
  (match x
    (((Rest5 z) z)
     ((Slot5 x2 m) (ite (= y 0) x2 (!25 m (- y 1)))))))
(define-fun-rec
  !24
  ((x Map5) (y Int)) Int
  (match x
    (((Rest4 z) z)
     ((Slot4 x2 m) (ite (= y 0) x2 (!24 m (- y 1)))))))
(define-fun-rec
  !23
  ((x Map) (y Int)) Map2
  (match x
    (((Rest3 z) z)
     ((Slot3 x2 m) (ite (= y 0) x2 (!23 m (- y 1)))))))
(define-fun
  add2
  ((x pair5) (y Map)) Map
  (match x (((pair24 z y2) (!=3 y (pair23 z (add y2 (!23 y z))))))))
(define-fun-rec
  !22
  ((x Map4) (y Int)) Map
  (match x
    (((Rest2 z) z)
     ((Slot2 x2 m) (ite (= y 0) x2 (!22 m (- y 1)))))))
(define-fun-rec
  !2
  ((x Map3) (y Int)) Maybe
  (match x
    (((Rest z) z)
     ((Slot x2 m) (ite (= y 0) x2 (!2 m (- y 1)))))))
(define-fun-rec
  reach
  ((x Int) (y Reach)) Maybe2
  (match y
    (((Init initk)
      (ite
        (inj x initk)
        (Just
          (State2 (Rest Nothing2)
            initk (range initk) (Rest2 empty2) initk (Rest3 empty)
            (Rest5 true)))
        Nothing))
     ((CheckIn g r k q)
      (match (reach x q)
        ((Nothing Nothing)
         ((Just s)
          (ite
            (and (<= r x) (not (!25 (issued s) k)))
            (match s
              (((State2 z x2 x3 x4 x5 x6 x7)
                (Just
                  (State2 (!= z (pair2 r (Just2 g)))
                    (!=4 x2 (pair24 r k)) (add k x3)
                    (!=2 x4 (pair22 g (add2 (pair24 (!24 x2 r) k) (!22 x4 g)))) x5 x6
                    (!=5 x7 (pair25 r false)))))))
            Nothing)))))
     ((EnterRoom f p x8 q2)
      (match x8
        (((pair24 i |k'|)
          (match (reach x q2)
            ((Nothing Nothing)
             ((Just t)
              (let ((rk (!24 (roomk t) p)))
                (ite
                  (and (<= p x)
                    (and (!25 (!23 (!22 (cards t) f) i) |k'|)
                      (or (= rk i) (= rk |k'|))))
                  (match t
                    (((State2 x9 x10 x11 x12 x13 x14 x15)
                      (Just
                        (State2 x9
                          x10 x11 x12 (!=4 x13 (pair24 p |k'|))
                          (!=3 x14 (pair23 p (add f (!23 x14 p))))
                          (!=5 x15
                            (pair25 p
                              (or (and (= (!2 x9 p) (Just2 f)) (<=> (!23 x14 p) empty))
                                (!25 x15 p)))))))))
                  Nothing)))))))))
     ((ExitRoom h r2 q3)
      (match (reach x q3)
        ((Nothing Nothing)
         ((Just s2)
          (ite
            (and (<= r2 x) (!25 (!23 (isin s2) r2) h))
            (match s2
              (((State2 x16 x17 x18 x19 x20 x21 x22)
                (Just
                  (State2 x16
                    x17 x18 x19 x20 (!=3 x21 (pair23 r2 (rem h (!23 x21 r2)))) x22)))))
            Nothing))))))))
(define-fun
  psafe
  ((x Int) (y Int) (z Int) (x2 Reach)) Bool
  (match (reach x x2)
    ((Nothing true)
     ((Just s)
      (ite
        (and (<= y x) (and (!25 (safe s) y) (!25 (!23 (isin s) y) z)))
        (= (!2 (owns s) y) (Just2 z)) true)))))
(define-fun
  !!
  ((x Map) (y pair5)) Bool
  (match y (((pair24 z y2) (!25 (!23 x z) y2)))))
(assert
  (not
    (forall ((dom Int) (r Int) (g Int) (q Reach)) (psafe dom r g q))))
(check-sat)
