open import Agda.Primitive

data eq (?0v : Level)  (A_v : Set ?0v) (X-x_v : A_v) : (X--v : A_v) -> Set ?0v where
  refl' : eq ?0v A_v X-x_v X-x_v

refl : (?1v : Level) -> (Av : Set ?1v) -> (xv : Av) -> eq ?1v Av xv xv
refl _ _ x = refl'

match-eq : (?5v : Level) -> (Av : Set ?5v) -> (X-xv : Av) -> (return-sortv : Level) -> (return-typev : (X--v : Av) -> (zv : eq ?5v Av X-xv X--v) -> Set return-sortv) -> (case-reflv : return-typev X-xv (refl ?5v Av X-xv)) -> (X--v : Av) -> (zv : eq ?5v Av X-xv X--v) -> return-typev X--v zv
match-eq _ _ _ _ _ caserefl _ refl' = caserefl



eq-ind : (?8v ?5v : Level) -> (Av : Set ?8v) -> (X-xv : Av) -> (Q-v : (x-1v : Av) -> (X-x-2v : eq ?8v Av X-xv x-1v) -> Set ?5v) -> (X-H-reflv : Q-v X-xv (refl ?8v Av X-xv)) -> (x-1v : Av) -> (x-2v : eq ?8v Av X-xv x-1v) -> Q-v x-1v x-2v
eq-ind _ _ _ _ _ caserefl _ refl' = caserefl

eq-rect-Type4 : (?8v ?5v : Level) -> (Av : Set ?8v) -> (X-xv : Av) -> (Q-v : (x-4v : Av) -> (X-x-5v : eq ?8v Av X-xv x-4v) -> Set ?5v) -> (X-H-reflv : Q-v X-xv (refl ?8v Av X-xv)) -> (x-4v : Av) -> (x-5v : eq ?8v Av X-xv x-4v) -> Q-v x-4v x-5v
eq-rect-Type4 _ _ _ _ _ caserefl _ refl' = caserefl

eq-rect-Type5 : (?8v ?5v : Level) -> (Av : Set ?8v) -> (X-xv : Av) -> (Q-v : (x-7v : Av) -> (X-x-8v : eq ?8v Av X-xv x-7v) -> Set ?5v) -> (X-H-reflv : Q-v X-xv (refl ?8v Av X-xv)) -> (x-7v : Av) -> (x-8v : eq ?8v Av X-xv x-7v) -> Q-v x-7v x-8v
eq-rect-Type5 _ _ _ _ _ caserefl _ refl' = caserefl

eq-rect-Type3 : (?8v ?5v : Level) -> (Av : Set ?8v) -> (X-xv : Av) -> (Q-v : (x-10v : Av) -> (X-x-11v : eq ?8v Av X-xv x-10v) -> Set ?5v) -> (X-H-reflv : Q-v X-xv (refl ?8v Av X-xv)) -> (x-10v : Av) -> (x-11v : eq ?8v Av X-xv x-10v) -> Q-v x-10v x-11v
eq-rect-Type3 _ _ _ _ _ caserefl _ refl' = caserefl

eq-rect-Type2 : (?8v ?5v : Level) -> (Av : Set ?8v) -> (X-xv : Av) -> (Q-v : (x-13v : Av) -> (X-x-14v : eq ?8v Av X-xv x-13v) -> Set ?5v) -> (X-H-reflv : Q-v X-xv (refl ?8v Av X-xv)) -> (x-13v : Av) -> (x-14v : eq ?8v Av X-xv x-13v) -> Q-v x-13v x-14v
eq-rect-Type2 _ _ _ _ _ caserefl _ refl' = caserefl

eq-rect-Type1 : (?8v ?5v : Level) -> (Av : Set ?8v) -> (X-xv : Av) -> (Q-v : (x-16v : Av) -> (X-x-17v : eq ?8v Av X-xv x-16v) -> Set ?5v) -> (X-H-reflv : Q-v X-xv (refl ?8v Av X-xv)) -> (x-16v : Av) -> (x-17v : eq ?8v Av X-xv x-16v) -> Q-v x-16v x-17v
eq-rect-Type1 _ _ _ _ _ caserefl _ refl' = caserefl

eq-rect-Type0 : (?8v ?5v : Level) -> (Av : Set ?8v) -> (X-xv : Av) -> (Q-v : (x-19v : Av) -> (X-x-20v : eq ?8v Av X-xv x-19v) -> Set ?5v) -> (X-H-reflv : Q-v X-xv (refl ?8v Av X-xv)) -> (x-19v : Av) -> (x-20v : eq ?8v Av X-xv x-19v) -> Q-v x-19v x-20v
eq-rect-Type0 _ _ _ _ _ caserefl _ refl' = caserefl




eq-rect-r : (l35 l16 : Level) -> (A : Set l35) -> (a : A) -> (x : A) -> (p : eq l35 A x a) -> (P : (x0 : A) -> (X-- : eq l35 A x0 a) -> Set l16) -> (X-- : P a (refl l35 A a)) -> P x p
eq-rect-r = λ (l35 l16 : Level) -> λ (A : Set l35) -> λ (a : A) -> λ (x : A) -> λ (p : eq l35 A x a) -> match-eq l35 A x ((lsuc lzero) ⊔ (l35 ⊔ (lsuc l16))) (λ (X-- : A) -> λ (X-0 : eq l35 A x X--) -> (P : (x0 : A) -> (X--1 : eq l35 A x0 X--) -> Set l16) -> (X--1 : P X-- (refl l35 A X--)) -> P x X-0) (λ (P : (x0 : A) -> (X-- : eq l35 A x0 x) -> Set l16) -> λ (auto : P x (refl l35 A x)) -> auto) a p

eq-ind-r : (l15 l10 : Level) -> (A : Set l15) -> (a : A) -> (P : (x : A) -> (X-- : eq l15 A x a) -> Set l10) -> (X-- : P a (refl l15 A a)) -> (x : A) -> (p : eq l15 A x a) -> P x p
eq-ind-r = λ (l15 l10 : Level) -> λ (A : Set l15) -> λ (a : A) -> λ (P : (x : A) -> (X-- : eq l15 A x a) -> Set l10) -> λ (p : P a (refl l15 A a)) -> λ (x0 : A) -> λ (p0 : eq l15 A x0 a) -> eq-rect-r l15 l10 A a x0 p0 (λ (x01 : A) -> λ (X-- : eq l15 A x01 a) -> P x01 X--) p

eq-rect-Type0-r : (l41 l36 : Level) -> (A : Set l41) -> (a : A) -> (P : (x : A) -> (X-- : eq l41 A x a) -> Set l36) -> (X-- : P a (refl l41 A a)) -> (x : A) -> (p : eq l41 A x a) -> P x p
eq-rect-Type0-r = λ (l41 l36 : Level) -> λ (A : Set l41) -> λ (a : A) -> λ (P : (x : A) -> (X-- : eq l41 A x a) -> Set l36) -> λ (H : P a (refl l41 A a)) -> λ (x : A) -> λ (p : eq l41 A x a) -> match-eq l41 A x ((lsuc lzero) ⊔ (l41 ⊔ (lsuc l36))) (λ (X-- : A) -> λ (X-0 : eq l41 A x X--) -> (f : (x0 : A) -> (X--1 : eq l41 A x0 X--) -> Set l36) -> (X--1 : f X-- (refl l41 A X--)) -> f x X-0) (λ (f : (x0 : A) -> (X-- : eq l41 A x0 x) -> Set l36) -> λ (auto : f x (refl l41 A x)) -> auto) a p P H

eq-rect-Type1-r : (l41 l36 : Level) -> (A : Set l41) -> (a : A) -> (P : (x : A) -> (X-- : eq l41 A x a) -> Set l36) -> (X-- : P a (refl l41 A a)) -> (x : A) -> (p : eq l41 A x a) -> P x p
eq-rect-Type1-r = λ (l41 l36 : Level) -> λ (A : Set l41) -> λ (a : A) -> λ (P : (x : A) -> (X-- : eq l41 A x a) -> Set l36) -> λ (H : P a (refl l41 A a)) -> λ (x : A) -> λ (p : eq l41 A x a) -> match-eq l41 A x ((lsuc lzero) ⊔ (l41 ⊔ (lsuc l36))) (λ (X-- : A) -> λ (X-0 : eq l41 A x X--) -> (f : (x0 : A) -> (X--1 : eq l41 A x0 X--) -> Set l36) -> (X--1 : f X-- (refl l41 A X--)) -> f x X-0) (λ (f : (x0 : A) -> (X-- : eq l41 A x0 x) -> Set l36) -> λ (auto : f x (refl l41 A x)) -> auto) a p P H

eq-rect-Type2-r : (l41 l36 : Level) -> (A : Set l41) -> (a : A) -> (P : (x : A) -> (X-- : eq l41 A x a) -> Set l36) -> (X-- : P a (refl l41 A a)) -> (x : A) -> (p : eq l41 A x a) -> P x p
eq-rect-Type2-r = λ (l41 l36 : Level) -> λ (A : Set l41) -> λ (a : A) -> λ (P : (x : A) -> (X-- : eq l41 A x a) -> Set l36) -> λ (H : P a (refl l41 A a)) -> λ (x : A) -> λ (p : eq l41 A x a) -> match-eq l41 A x ((lsuc lzero) ⊔ (l41 ⊔ (lsuc l36))) (λ (X-- : A) -> λ (X-0 : eq l41 A x X--) -> (f : (x0 : A) -> (X--1 : eq l41 A x0 X--) -> Set l36) -> (X--1 : f X-- (refl l41 A X--)) -> f x X-0) (λ (f : (x0 : A) -> (X-- : eq l41 A x0 x) -> Set l36) -> λ (auto : f x (refl l41 A x)) -> auto) a p P H

eq-rect-Type3-r : (l41 l36 : Level) -> (A : Set l41) -> (a : A) -> (P : (x : A) -> (X-- : eq l41 A x a) -> Set l36) -> (X-- : P a (refl l41 A a)) -> (x : A) -> (p : eq l41 A x a) -> P x p
eq-rect-Type3-r = λ (l41 l36 : Level) -> λ (A : Set l41) -> λ (a : A) -> λ (P : (x : A) -> (X-- : eq l41 A x a) -> Set l36) -> λ (H : P a (refl l41 A a)) -> λ (x : A) -> λ (p : eq l41 A x a) -> match-eq l41 A x ((lsuc lzero) ⊔ (l41 ⊔ (lsuc l36))) (λ (X-- : A) -> λ (X-0 : eq l41 A x X--) -> (f : (x0 : A) -> (X--1 : eq l41 A x0 X--) -> Set l36) -> (X--1 : f X-- (refl l41 A X--)) -> f x X-0) (λ (f : (x0 : A) -> (X-- : eq l41 A x0 x) -> Set l36) -> λ (auto : f x (refl l41 A x)) -> auto) a p P H

rewrite-l : (l12 l9 : Level) -> (A : Set l12) -> (x : A) -> (P : (X-- : A) -> Set l9) -> (X-- : P x) -> (y : A) -> (X--1 : eq l12 A x y) -> P y
rewrite-l = λ (l12 l9 : Level) -> λ (A : Set l12) -> λ (x : A) -> λ (P : (X-- : A) -> Set l9) -> λ (Hx : P x) -> λ (y : A) -> λ (Heq : eq l12 A x y) -> match-eq l12 A x l9 (λ (X-- : A) -> λ (X-0 : eq l12 A x X--) -> P X--) Hx y Heq

sym-eq : (l14 : Level) -> (A : Set l14) -> (x : A) -> (y : A) -> (X-- : eq l14 A x y) -> eq l14 A y x
sym-eq = λ (l14 : Level) -> λ (A : Set l14) -> λ (x : A) -> λ (y : A) -> λ (Heq : eq l14 A x y) -> rewrite-l l14 l14 A x (λ (X-- : A) -> eq l14 A X-- x) (refl l14 A x) y (rewrite-l l14 l14 A x (λ (X-- : A) -> eq l14 A x X--) (refl l14 A x) y Heq)

rewrite-r : (l13 l10 : Level) -> (A : Set l13) -> (x : A) -> (P : (X-- : A) -> Set l10) -> (X-- : P x) -> (y : A) -> (X--1 : eq l13 A y x) -> P y
rewrite-r = λ (l13 l10 : Level) -> λ (A : Set l13) -> λ (x : A) -> λ (P : (X-- : A) -> Set l10) -> λ (Hx : P x) -> λ (y : A) -> λ (Heq : eq l13 A y x) -> match-eq l13 A x l10 (λ (X-- : A) -> λ (X-0 : eq l13 A x X--) -> P X--) Hx y (sym-eq l13 A y x Heq)

eq-coerc : (l12 : Level) -> (A : Set l12) -> (B : Set l12) -> (X-- : A) -> (X--1 : eq ((lsuc lzero) ⊔ (lsuc l12)) (Set l12) A B) -> B
eq-coerc = λ (l12 : Level) -> λ (A : Set l12) -> λ (B : Set l12) -> λ (Ha : A) -> λ (Heq : eq ((lsuc lzero) ⊔ (lsuc l12)) (Set l12) A B) -> eq-rect-Type0 ((lsuc lzero) ⊔ (lsuc l12)) l12 (Set l12) A (λ (x-19 : Set l12) -> λ (X-x-20 : eq ((lsuc lzero) ⊔ (lsuc l12)) (Set l12) A x-19) -> x-19) Ha B Heq

trans-eq : (l26 : Level) -> (A : Set l26) -> (x : A) -> (y : A) -> (z : A) -> (X-- : eq l26 A x y) -> (X--1 : eq l26 A y z) -> eq l26 A x z
trans-eq = λ (l26 : Level) -> λ (A : Set l26) -> λ (x : A) -> λ (y : A) -> λ (z : A) -> λ (H1 : eq l26 A x y) -> λ (H2 : eq l26 A y z) -> eq-ind-r l26 l26 A y (λ (x0 : A) -> λ (X-- : eq l26 A x0 y) -> eq l26 A x0 z) (rewrite-l l26 l26 A x (λ (X-- : A) -> eq l26 A X-- z) (rewrite-l l26 l26 A x (λ (X-- : A) -> eq l26 A x X--) (refl l26 A x) z (rewrite-r l26 l26 A y (λ (X-- : A) -> eq l26 A X-- z) H2 x H1)) y H1) x H1

eq-f : (l22 l21 : Level) -> (A : Set l22) -> (B : Set l21) -> (f : (X-- : A) -> B) -> (x : A) -> (y : A) -> (X-- : eq l22 A x y) -> eq l21 B (f x) (f y)
eq-f = λ (l22 l21 : Level) -> λ (A : Set l22) -> λ (B : Set l21) -> λ (f : (X-- : A) -> B) -> λ (x : A) -> λ (y : A) -> λ (H : eq l22 A x y) -> eq-ind-r l22 l21 A y (λ (x0 : A) -> λ (X-- : eq l22 A x0 y) -> eq l21 B (f x0) (f y)) (rewrite-l l22 l21 A x (λ (X-- : A) -> eq l21 B (f X--) (f y)) (rewrite-l l22 l21 A x (λ (X-- : A) -> eq l21 B (f x) (f X--)) (refl l21 B (f x)) y H) y H) x H

eq-f2 : (l42 l41 l40 : Level) -> (A : Set l42) -> (B : Set l41) -> (C : Set l40) -> (f : (X-- : A) -> (X--1 : B) -> C) -> (x1 : A) -> (x2 : A) -> (y1 : B) -> (y2 : B) -> (X-- : eq l42 A x1 x2) -> (X--1 : eq l41 B y1 y2) -> eq l40 C (f x1 y1) (f x2 y2)
eq-f2 = λ (l42 l41 l40 : Level) -> λ (A : Set l42) -> λ (B : Set l41) -> λ (C : Set l40) -> λ (f : (X-- : A) -> (X--1 : B) -> C) -> λ (x1 : A) -> λ (x2 : A) -> λ (y1 : B) -> λ (y2 : B) -> λ (E1 : eq l42 A x1 x2) -> λ (E2 : eq l41 B y1 y2) -> eq-ind-r l42 l40 A x2 (λ (x : A) -> λ (X-- : eq l42 A x x2) -> eq l40 C (f x y1) (f x2 y2)) (eq-ind-r l41 l40 B y2 (λ (x : B) -> λ (X-- : eq l41 B x y2) -> eq l40 C (f x2 x) (f x2 y2)) (rewrite-l l42 l40 A x1 (λ (X-- : A) -> eq l40 C (f X-- y2) (f x2 y2)) (rewrite-l l41 l40 B y1 (λ (X-- : B) -> eq l40 C (f x1 X--) (f x2 y2)) (rewrite-l l42 l40 A x1 (λ (X-- : A) -> eq l40 C (f x1 y1) (f X-- y2)) (rewrite-l l41 l40 B y1 (λ (X-- : B) -> eq l40 C (f x1 y1) (f x1 X--)) (refl l40 C (f x1 y1)) y2 E2) x2 E1) y2 E2) x2 E1) y1 E2) x1 E1

eq-f3 : (l62 l61 l60 l59 : Level) -> (A : Set l62) -> (B : Set l61) -> (C : Set l60) -> (D : Set l59) -> (f : (X-- : A) -> (X--1 : B) -> (X--2 : C) -> D) -> (x1 : A) -> (x2 : A) -> (y1 : B) -> (y2 : B) -> (z1 : C) -> (z2 : C) -> (X-- : eq l62 A x1 x2) -> (X--1 : eq l61 B y1 y2) -> (X--2 : eq l60 C z1 z2) -> eq l59 D (f x1 y1 z1) (f x2 y2 z2)
eq-f3 = λ (l62 l61 l60 l59 : Level) -> λ (A : Set l62) -> λ (B : Set l61) -> λ (C : Set l60) -> λ (D : Set l59) -> λ (f : (X-- : A) -> (X--1 : B) -> (X--2 : C) -> D) -> λ (x1 : A) -> λ (x2 : A) -> λ (y1 : B) -> λ (y2 : B) -> λ (z1 : C) -> λ (z2 : C) -> λ (E1 : eq l62 A x1 x2) -> λ (E2 : eq l61 B y1 y2) -> λ (E3 : eq l60 C z1 z2) -> eq-ind-r l62 l59 A x2 (λ (x : A) -> λ (X-- : eq l62 A x x2) -> eq l59 D (f x y1 z1) (f x2 y2 z2)) (eq-ind-r l61 l59 B y2 (λ (x : B) -> λ (X-- : eq l61 B x y2) -> eq l59 D (f x2 x z1) (f x2 y2 z2)) (eq-ind-r l60 l59 C z2 (λ (x : C) -> λ (X-- : eq l60 C x z2) -> eq l59 D (f x2 y2 x) (f x2 y2 z2)) (rewrite-l l62 l59 A x1 (λ (X-- : A) -> eq l59 D (f X-- y2 z2) (f x2 y2 z2)) (rewrite-l l61 l59 B y1 (λ (X-- : B) -> eq l59 D (f x1 X-- z2) (f x2 y2 z2)) (rewrite-l l60 l59 C z1 (λ (X-- : C) -> eq l59 D (f x1 y1 X--) (f x2 y2 z2)) (rewrite-l l62 l59 A x1 (λ (X-- : A) -> eq l59 D (f x1 y1 z1) (f X-- y2 z2)) (rewrite-l l61 l59 B y1 (λ (X-- : B) -> eq l59 D (f x1 y1 z1) (f x1 X-- z2)) (rewrite-l l60 l59 C z1 (λ (X-- : C) -> eq l59 D (f x1 y1 z1) (f x1 y1 X--)) (refl l59 D (f x1 y1 z1)) z2 E3) y2 E2) x2 E1) z2 E3) y2 E2) x2 E1) z1 E3) y1 E2) x1 E1


data True (?0v : Level) : Set ?0v where
  I' : True ?0v

I : (?1v : Level) -> True ?1v
I _ = I'

match-True : (?4v return-sortv : Level) -> (return-typev : (zv : True ?4v) -> Set return-sortv) -> (case-Iv : return-typev (I ?4v)) -> (zv : True ?4v) -> return-typev zv
match-True _ _ _ caseI I' = caseI


True-ind : (?7v ?4v : Level) -> (Q-v : (X-x-40v : True ?7v) -> Set ?4v) -> (X-H-Iv : Q-v (I ?7v)) -> (x-40v : True ?7v) -> Q-v x-40v
True-ind _ _ _ caseI I' = caseI

True-rect-Type4 : (?7v ?4v : Level) -> (Q-v : (X-x-42v : True ?7v) -> Set ?4v) -> (X-H-Iv : Q-v (I ?7v)) -> (x-42v : True ?7v) -> Q-v x-42v
True-rect-Type4 _ _ _ caseI I' = caseI

True-rect-Type5 : (?7v ?4v : Level) -> (Q-v : (X-x-42v : True ?7v) -> Set ?4v) -> (X-H-Iv : Q-v (I ?7v)) -> (x-42v : True ?7v) -> Q-v x-42v
True-rect-Type5 _ _ _ caseI I' = caseI

True-rect-Type3 : (?7v ?4v : Level) -> (Q-v : (X-x-42v : True ?7v) -> Set ?4v) -> (X-H-Iv : Q-v (I ?7v)) -> (x-42v : True ?7v) -> Q-v x-42v
True-rect-Type3 _ _ _ caseI I' = caseI

True-rect-Type2 : (?7v ?4v : Level) -> (Q-v : (X-x-42v : True ?7v) -> Set ?4v) -> (X-H-Iv : Q-v (I ?7v)) -> (x-42v : True ?7v) -> Q-v x-42v
True-rect-Type2 _ _ _ caseI I' = caseI

True-rect-Type1 : (?7v ?4v : Level) -> (Q-v : (X-x-42v : True ?7v) -> Set ?4v) -> (X-H-Iv : Q-v (I ?7v)) -> (x-42v : True ?7v) -> Q-v x-42v
True-rect-Type1 _ _ _ caseI I' = caseI

True-rect-Type0 : (?7v ?4v : Level) -> (Q-v : (X-x-42v : True ?7v) -> Set ?4v) -> (X-H-Iv : Q-v (I ?7v)) -> (x-42v : True ?7v) -> Q-v x-42v
True-rect-Type0 _ _ _ caseI I' = caseI


True-inv-ind : (l23 l19 : Level) -> (Hterm : True l23) -> (P : (X-z125 : True l23) -> Set l19) -> (X-H1 : (X-z126 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> P Hterm
True-inv-ind = λ (l23 l19 : Level) -> λ (Hterm : True l23) -> λ (P : (X-z125 : True l23) -> Set l19) -> λ (H1 : (X-z126 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> True-ind l23 (l23 ⊔ l19) (λ (X-x-40 : True l23) -> (X-z126 : eq l23 (True l23) Hterm X-x-40) -> P X-x-40) H1 Hterm (refl l23 (True l23) Hterm)

True-inv-rect-Type4 : (l23 l19 : Level) -> (Hterm : True l23) -> (P : (X-z131 : True l23) -> Set l19) -> (X-H1 : (X-z132 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> P Hterm
True-inv-rect-Type4 = λ (l23 l19 : Level) -> λ (Hterm : True l23) -> λ (P : (X-z131 : True l23) -> Set l19) -> λ (H1 : (X-z132 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> True-rect-Type4 l23 (l23 ⊔ l19) (λ (X-x-42 : True l23) -> (X-z132 : eq l23 (True l23) Hterm X-x-42) -> P X-x-42) H1 Hterm (refl l23 (True l23) Hterm)

True-inv-rect-Type3 : (l23 l19 : Level) -> (Hterm : True l23) -> (P : (X-z137 : True l23) -> Set l19) -> (X-H1 : (X-z138 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> P Hterm
True-inv-rect-Type3 = λ (l23 l19 : Level) -> λ (Hterm : True l23) -> λ (P : (X-z137 : True l23) -> Set l19) -> λ (H1 : (X-z138 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> True-rect-Type3 l23 (l23 ⊔ l19) (λ (X-x-46 : True l23) -> (X-z138 : eq l23 (True l23) Hterm X-x-46) -> P X-x-46) H1 Hterm (refl l23 (True l23) Hterm)

True-inv-rect-Type2 : (l23 l19 : Level) -> (Hterm : True l23) -> (P : (X-z143 : True l23) -> Set l19) -> (X-H1 : (X-z144 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> P Hterm
True-inv-rect-Type2 = λ (l23 l19 : Level) -> λ (Hterm : True l23) -> λ (P : (X-z143 : True l23) -> Set l19) -> λ (H1 : (X-z144 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> True-rect-Type2 l23 (l23 ⊔ l19) (λ (X-x-48 : True l23) -> (X-z144 : eq l23 (True l23) Hterm X-x-48) -> P X-x-48) H1 Hterm (refl l23 (True l23) Hterm)

True-inv-rect-Type1 : (l23 l19 : Level) -> (Hterm : True l23) -> (P : (X-z149 : True l23) -> Set l19) -> (X-H1 : (X-z150 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> P Hterm
True-inv-rect-Type1 = λ (l23 l19 : Level) -> λ (Hterm : True l23) -> λ (P : (X-z149 : True l23) -> Set l19) -> λ (H1 : (X-z150 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> True-rect-Type1 l23 (l23 ⊔ l19) (λ (X-x-50 : True l23) -> (X-z150 : eq l23 (True l23) Hterm X-x-50) -> P X-x-50) H1 Hterm (refl l23 (True l23) Hterm)

True-inv-rect-Type0 : (l23 l19 : Level) -> (Hterm : True l23) -> (P : (X-z155 : True l23) -> Set l19) -> (X-H1 : (X-z156 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> P Hterm
True-inv-rect-Type0 = λ (l23 l19 : Level) -> λ (Hterm : True l23) -> λ (P : (X-z155 : True l23) -> Set l19) -> λ (H1 : (X-z156 : eq l23 (True l23) Hterm (I l23)) -> P (I l23)) -> True-rect-Type0 l23 (l23 ⊔ l19) (λ (X-x-52 : True l23) -> (X-z156 : eq l23 (True l23) Hterm X-x-52) -> P X-x-52) H1 Hterm (refl l23 (True l23) Hterm)

True-discr : (l58 l68 : Level) -> (x : True l58) -> (y : True l58) -> (X-e : eq l58 (True l58) x y) -> match-True l58 ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l68))) (λ (X-- : True l58) -> Set ((lsuc lzero) ⊔ (lsuc l68))) (match-True l58 ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l68))) (λ (X-- : True l58) -> Set ((lsuc lzero) ⊔ (lsuc l68))) ((P : Set l68) -> (X-z5 : P) -> P) y) x
True-discr = λ (l58 l68 : Level) -> λ (x : True l58) -> λ (y : True l58) -> λ (Deq : eq l58 (True l58) x y) -> eq-rect-Type2 l58 ((lsuc lzero) ⊔ (lsuc l68)) (True l58) x (λ (x-13 : True l58) -> λ (X-x-14 : eq l58 (True l58) x x-13) -> match-True l58 ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l68))) (λ (X-- : True l58) -> Set ((lsuc lzero) ⊔ (lsuc l68))) (match-True l58 ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l68))) (λ (X-- : True l58) -> Set ((lsuc lzero) ⊔ (lsuc l68))) ((P : Set l68) -> (X-z5 : P) -> P) x-13) x) (match-True l58 ((lsuc lzero) ⊔ (lsuc l68)) (λ (X-- : True l58) -> match-True l58 ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l68))) (λ (X-0 : True l58) -> Set ((lsuc lzero) ⊔ (lsuc l68))) (match-True l58 ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l68))) (λ (X-0 : True l58) -> Set ((lsuc lzero) ⊔ (lsuc l68))) ((P : Set l68) -> (X-z5 : P) -> P) X--) X--) (λ (P : Set l68) -> λ (DH : P) -> DH) x) y Deq


data False (?0v : Level) : Set ?0v where

match-False : (?3v return-sortv : Level) -> (return-typev : (zv : False ?3v) -> Set return-sortv) -> (zv : False ?3v) -> return-typev zv
match-False _ _ _ ()

False-ind : (?5v ?0v : Level) -> (Q-v : (X-x-66v : False ?5v) -> Set ?0v) -> (x-66v : False ?5v) -> Q-v x-66v
False-ind _ _ _ ()

False-rect-Type4 : (?5v ?0v : Level) -> (Q-v : (X-x-66v : False ?5v) -> Set ?0v) -> (x-66v : False ?5v) -> Q-v x-66v
False-rect-Type4 _ _ _ ()

False-rect-Type5 : (?5v ?0v : Level) -> (Q-v : (X-x-66v : False ?5v) -> Set ?0v) -> (x-66v : False ?5v) -> Q-v x-66v
False-rect-Type5 _ _ _ ()

False-rect-Type3 : (?5v ?0v : Level) -> (Q-v : (X-x-66v : False ?5v) -> Set ?0v) -> (x-66v : False ?5v) -> Q-v x-66v
False-rect-Type3 _ _ _ ()

False-rect-Type2 : (?5v ?0v : Level) -> (Q-v : (X-x-66v : False ?5v) -> Set ?0v) -> (x-66v : False ?5v) -> Q-v x-66v
False-rect-Type2 _ _ _ ()

False-rect-Type1 : (?5v ?0v : Level) -> (Q-v : (X-x-66v : False ?5v) -> Set ?0v) -> (x-66v : False ?5v) -> Q-v x-66v
False-rect-Type1 _ _ _ ()

False-rect-Type0 : (?5v ?0v : Level) -> (Q-v : (X-x-66v : False ?5v) -> Set ?0v) -> (x-66v : False ?5v) -> Q-v x-66v
False-rect-Type0 _ _ _ ()




data Not (?0v : Level) (X-Av : Set ?0v) : Set ?0v where
  nmk' : (X-Av -> False ?0v) -> Not ?0v X-Av

nmk : (?3v : Level) -> (Av : Set ?3v) -> (X--v : (X--v : Av) -> False ?3v) -> Not ?3v Av
nmk _ _ x = nmk' x

match-Not : (?7v : Level) -> (X-Av : Set ?7v) -> (return-sortv : Level) -> (return-typev : (zv : Not ?7v X-Av) -> Set return-sortv) -> (case-nmkv : (X--v : (X--v : X-Av) -> False ?7v) -> return-typev (nmk ?7v X-Av X--v)) -> (zv : Not ?7v X-Av) -> return-typev zv
match-Not _ _ _ _ casenm (nmk' x) = casenm x

Not-ind : (?10v ?4v : Level) -> (X-Av : Set ?10v) -> (Q-v : (X-x-79v : Not ?10v X-Av) -> Set ?4v) -> (X-H-nmkv : (x-80v : (X--v : X-Av) -> False ?10v) -> Q-v (nmk ?10v X-Av x-80v)) -> (x-79v : Not ?10v X-Av) -> Q-v x-79v
Not-ind _ _ _ _ casenm (nmk' x) = casenm x


Not-rect-Type4 : (?10v ?4v : Level) -> (X-Av : Set ?10v) -> (Q-v : (X-x-82v : Not ?10v X-Av) -> Set ?4v) -> (X-H-nmkv : (x-83v : (X--v : X-Av) -> False ?10v) -> Q-v (nmk ?10v X-Av x-83v)) -> (x-82v : Not ?10v X-Av) -> Q-v x-82v
Not-rect-Type4 _ _ _ _ casenm (nmk' x) = casenm x

Not-rect-Type5 : (?10v ?4v : Level) -> (X-Av : Set ?10v) -> (Q-v : (X-x-82v : Not ?10v X-Av) -> Set ?4v) -> (X-H-nmkv : (x-83v : (X--v : X-Av) -> False ?10v) -> Q-v (nmk ?10v X-Av x-83v)) -> (x-82v : Not ?10v X-Av) -> Q-v x-82v
Not-rect-Type5 _ _ _ _ casenm (nmk' x) = casenm x

Not-rect-Type3 : (?10v ?4v : Level) -> (X-Av : Set ?10v) -> (Q-v : (X-x-82v : Not ?10v X-Av) -> Set ?4v) -> (X-H-nmkv : (x-83v : (X--v : X-Av) -> False ?10v) -> Q-v (nmk ?10v X-Av x-83v)) -> (x-82v : Not ?10v X-Av) -> Q-v x-82v
Not-rect-Type3 _ _ _ _ casenm (nmk' x) = casenm x

Not-rect-Type2 : (?10v ?4v : Level) -> (X-Av : Set ?10v) -> (Q-v : (X-x-82v : Not ?10v X-Av) -> Set ?4v) -> (X-H-nmkv : (x-83v : (X--v : X-Av) -> False ?10v) -> Q-v (nmk ?10v X-Av x-83v)) -> (x-82v : Not ?10v X-Av) -> Q-v x-82v
Not-rect-Type2 _ _ _ _ casenm (nmk' x) = casenm x

Not-rect-Type1 : (?10v ?4v : Level) -> (X-Av : Set ?10v) -> (Q-v : (X-x-82v : Not ?10v X-Av) -> Set ?4v) -> (X-H-nmkv : (x-83v : (X--v : X-Av) -> False ?10v) -> Q-v (nmk ?10v X-Av x-83v)) -> (x-82v : Not ?10v X-Av) -> Q-v x-82v
Not-rect-Type1 _ _ _ _ casenm (nmk' x) = casenm x

Not-rect-Type0 : (?10v ?4v : Level) -> (X-Av : Set ?10v) -> (Q-v : (X-x-82v : Not ?10v X-Av) -> Set ?4v) -> (X-H-nmkv : (x-83v : (X--v : X-Av) -> False ?10v) -> Q-v (nmk ?10v X-Av x-83v)) -> (x-82v : Not ?10v X-Av) -> Q-v x-82v
Not-rect-Type0 _ _ _ _ casenm (nmk' x) = casenm x




Not-inv-ind : (l27 l22 : Level) -> (x1 : Set l27) -> (Hterm : Not l27 x1) -> (P : (X-z257 : Not l27 x1) -> Set l22) -> (X-H1 : (x-80 : (X-- : x1) -> False l27) -> (X-z258 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-80)) -> P (nmk l27 x1 x-80)) -> P Hterm
Not-inv-ind = λ (l27 l22 : Level) -> λ (x1 : Set l27) -> λ (Hterm : Not l27 x1) -> λ (P : (X-z257 : Not l27 x1) -> Set l22) -> λ (H1 : (x-80 : (X-- : x1) -> False l27) -> (X-z258 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-80)) -> P (nmk l27 x1 x-80)) -> Not-ind l27 (l27 ⊔ l22) x1 (λ (X-x-79 : Not l27 x1) -> (X-z258 : eq l27 (Not l27 x1) Hterm X-x-79) -> P X-x-79) H1 Hterm (refl l27 (Not l27 x1) Hterm)

Not-inv-rect-Type4 : (l27 l22 : Level) -> (x1 : Set l27) -> (Hterm : Not l27 x1) -> (P : (X-z263 : Not l27 x1) -> Set l22) -> (X-H1 : (x-83 : (X-- : x1) -> False l27) -> (X-z264 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-83)) -> P (nmk l27 x1 x-83)) -> P Hterm
Not-inv-rect-Type4 = λ (l27 l22 : Level) -> λ (x1 : Set l27) -> λ (Hterm : Not l27 x1) -> λ (P : (X-z263 : Not l27 x1) -> Set l22) -> λ (H1 : (x-83 : (X-- : x1) -> False l27) -> (X-z264 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-83)) -> P (nmk l27 x1 x-83)) -> Not-rect-Type4 l27 (l27 ⊔ l22) x1 (λ (X-x-82 : Not l27 x1) -> (X-z264 : eq l27 (Not l27 x1) Hterm X-x-82) -> P X-x-82) H1 Hterm (refl l27 (Not l27 x1) Hterm)

Not-inv-rect-Type3 : (l27 l22 : Level) -> (x1 : Set l27) -> (Hterm : Not l27 x1) -> (P : (X-z269 : Not l27 x1) -> Set l22) -> (X-H1 : (x-89 : (X-- : x1) -> False l27) -> (X-z270 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-89)) -> P (nmk l27 x1 x-89)) -> P Hterm
Not-inv-rect-Type3 = λ (l27 l22 : Level) -> λ (x1 : Set l27) -> λ (Hterm : Not l27 x1) -> λ (P : (X-z269 : Not l27 x1) -> Set l22) -> λ (H1 : (x-89 : (X-- : x1) -> False l27) -> (X-z270 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-89)) -> P (nmk l27 x1 x-89)) -> Not-rect-Type3 l27 (l27 ⊔ l22) x1 (λ (X-x-88 : Not l27 x1) -> (X-z270 : eq l27 (Not l27 x1) Hterm X-x-88) -> P X-x-88) H1 Hterm (refl l27 (Not l27 x1) Hterm)

Not-inv-rect-Type2 : (l27 l22 : Level) -> (x1 : Set l27) -> (Hterm : Not l27 x1) -> (P : (X-z275 : Not l27 x1) -> Set l22) -> (X-H1 : (x-92 : (X-- : x1) -> False l27) -> (X-z276 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-92)) -> P (nmk l27 x1 x-92)) -> P Hterm
Not-inv-rect-Type2 = λ (l27 l22 : Level) -> λ (x1 : Set l27) -> λ (Hterm : Not l27 x1) -> λ (P : (X-z275 : Not l27 x1) -> Set l22) -> λ (H1 : (x-92 : (X-- : x1) -> False l27) -> (X-z276 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-92)) -> P (nmk l27 x1 x-92)) -> Not-rect-Type2 l27 (l27 ⊔ l22) x1 (λ (X-x-91 : Not l27 x1) -> (X-z276 : eq l27 (Not l27 x1) Hterm X-x-91) -> P X-x-91) H1 Hterm (refl l27 (Not l27 x1) Hterm)

Not-inv-rect-Type1 : (l27 l22 : Level) -> (x1 : Set l27) -> (Hterm : Not l27 x1) -> (P : (X-z281 : Not l27 x1) -> Set l22) -> (X-H1 : (x-95 : (X-- : x1) -> False l27) -> (X-z282 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-95)) -> P (nmk l27 x1 x-95)) -> P Hterm
Not-inv-rect-Type1 = λ (l27 l22 : Level) -> λ (x1 : Set l27) -> λ (Hterm : Not l27 x1) -> λ (P : (X-z281 : Not l27 x1) -> Set l22) -> λ (H1 : (x-95 : (X-- : x1) -> False l27) -> (X-z282 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-95)) -> P (nmk l27 x1 x-95)) -> Not-rect-Type1 l27 (l27 ⊔ l22) x1 (λ (X-x-94 : Not l27 x1) -> (X-z282 : eq l27 (Not l27 x1) Hterm X-x-94) -> P X-x-94) H1 Hterm (refl l27 (Not l27 x1) Hterm)

Not-inv-rect-Type0 : (l27 l22 : Level) -> (x1 : Set l27) -> (Hterm : Not l27 x1) -> (P : (X-z287 : Not l27 x1) -> Set l22) -> (X-H1 : (x-98 : (X-- : x1) -> False l27) -> (X-z288 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-98)) -> P (nmk l27 x1 x-98)) -> P Hterm
Not-inv-rect-Type0 = λ (l27 l22 : Level) -> λ (x1 : Set l27) -> λ (Hterm : Not l27 x1) -> λ (P : (X-z287 : Not l27 x1) -> Set l22) -> λ (H1 : (x-98 : (X-- : x1) -> False l27) -> (X-z288 : eq l27 (Not l27 x1) Hterm (nmk l27 x1 x-98)) -> P (nmk l27 x1 x-98)) -> Not-rect-Type0 l27 (l27 ⊔ l22) x1 (λ (X-x-97 : Not l27 x1) -> (X-z288 : eq l27 (Not l27 x1) Hterm X-x-97) -> P X-x-97) H1 Hterm (refl l27 (Not l27 x1) Hterm)

absurd : (l11 : Level) -> (A : Set l11) -> (X-- : A) -> (X--1 : Not l11 A) -> False l11
absurd = λ (l11 : Level) -> λ (A : Set l11) -> λ (H : A) -> λ (Hn : Not l11 A) -> Not-ind l11 l11 A (λ (X-x-79 : Not l11 A) -> False l11) (λ (X-x-80 : (X-- : A) -> False l11) -> X-x-80 H) Hn

not-to-not : (l8 : Level) -> (A : Set l8) -> (B : Set l8) -> (X-- : (X-- : A) -> B) -> (X--1 : Not l8 B) -> Not l8 A
not-to-not = λ (l8 : Level) -> λ (A : Set l8) -> λ (B : Set l8) -> λ (auto : (X-- : A) -> B) -> λ (auto' : Not l8 B) -> nmk l8 A (λ (auto'' : A) -> absurd l8 B (auto auto'') auto')

sym-not-eq : (l16 : Level) -> (A : Set l16) -> (x : A) -> (y : A) -> (X-- : Not l16 (eq l16 A x y)) -> Not l16 (eq l16 A y x)
sym-not-eq = λ (l16 : Level) -> λ (A : Set l16) -> λ (x : A) -> λ (y : A) -> λ (auto : Not l16 (eq l16 A x y)) -> nmk l16 (eq l16 A y x) (λ (auto' : eq l16 A y x) -> absurd l16 (eq l16 A x y) (rewrite-r l16 l16 A x (λ (X-- : A) -> eq l16 A x X--) (refl l16 A x) y auto') auto)



data And (?2v ?1v : Level) (X-Av : Set ?2v) (X-Bv : Set ?1v) : Set (lzero ⊔ (?2v ⊔ ?1v)) where
  conj' : X-Av -> X-Bv -> And ?2v ?1v X-Av X-Bv

conj : (?4v ?3v : Level) -> (Av : Set ?4v) -> (Bv : Set ?3v) -> (X--v : Av) -> (X--1v : Bv) -> And ?4v ?3v Av Bv
conj _ _ _ _ = conj'

match-And : (?8v ?7v : Level) -> (X-Av : Set ?8v) -> (X-Bv : Set ?7v) -> (return-sortv : Level) -> (return-typev : (zv : And ?8v ?7v X-Av X-Bv) -> Set return-sortv) -> (case-conjv : (X--v : X-Av) -> (X--1v : X-Bv) -> return-typev (conj ?8v ?7v X-Av X-Bv X--v X--1v)) -> (zv : And ?8v ?7v X-Av X-Bv) -> return-typev zv
match-And _ _ _ _ _ _ caseconj (conj' a b) = caseconj a b

And-ind : (?11v ?10v ?6v : Level) -> (X-Av : Set ?11v) -> (X-Bv : Set ?10v) -> (Q-v : (X-x-118v : And ?11v ?10v X-Av X-Bv) -> Set ?6v) -> (X-H-conjv : (x-120v : X-Av) -> (x-119v : X-Bv) -> Q-v (conj ?11v ?10v X-Av X-Bv x-120v x-119v)) -> (x-118v : And ?11v ?10v X-Av X-Bv) -> Q-v x-118v
And-ind _ _ _ _ _ _ caseconj (conj' a b) = caseconj a b

And-rect-Type4 : (?11v ?10v ?6v : Level) -> (X-Av : Set ?11v) -> (X-Bv : Set ?10v) -> (Q-v : (X-x-122v : And ?11v ?10v X-Av X-Bv) -> Set ?6v) -> (X-H-conjv : (x-124v : X-Av) -> (x-123v : X-Bv) -> Q-v (conj ?11v ?10v X-Av X-Bv x-124v x-123v)) -> (x-122v : And ?11v ?10v X-Av X-Bv) -> Q-v x-122v
And-rect-Type4 _ _ _ _ _ _ caseconj (conj' a b) = caseconj a b

And-rect-Type5 : (?11v ?10v ?6v : Level) -> (X-Av : Set ?11v) -> (X-Bv : Set ?10v) -> (Q-v : (X-x-122v : And ?11v ?10v X-Av X-Bv) -> Set ?6v) -> (X-H-conjv : (x-124v : X-Av) -> (x-123v : X-Bv) -> Q-v (conj ?11v ?10v X-Av X-Bv x-124v x-123v)) -> (x-122v : And ?11v ?10v X-Av X-Bv) -> Q-v x-122v
And-rect-Type5 _ _ _ _ _ _ caseconj (conj' a b) = caseconj a b

And-rect-Type3 : (?11v ?10v ?6v : Level) -> (X-Av : Set ?11v) -> (X-Bv : Set ?10v) -> (Q-v : (X-x-122v : And ?11v ?10v X-Av X-Bv) -> Set ?6v) -> (X-H-conjv : (x-124v : X-Av) -> (x-123v : X-Bv) -> Q-v (conj ?11v ?10v X-Av X-Bv x-124v x-123v)) -> (x-122v : And ?11v ?10v X-Av X-Bv) -> Q-v x-122v
And-rect-Type3 _ _ _ _ _ _ caseconj (conj' a b) = caseconj a b

And-rect-Type2 : (?11v ?10v ?6v : Level) -> (X-Av : Set ?11v) -> (X-Bv : Set ?10v) -> (Q-v : (X-x-122v : And ?11v ?10v X-Av X-Bv) -> Set ?6v) -> (X-H-conjv : (x-124v : X-Av) -> (x-123v : X-Bv) -> Q-v (conj ?11v ?10v X-Av X-Bv x-124v x-123v)) -> (x-122v : And ?11v ?10v X-Av X-Bv) -> Q-v x-122v
And-rect-Type2 _ _ _ _ _ _ caseconj (conj' a b) = caseconj a b

And-rect-Type1 : (?11v ?10v ?6v : Level) -> (X-Av : Set ?11v) -> (X-Bv : Set ?10v) -> (Q-v : (X-x-122v : And ?11v ?10v X-Av X-Bv) -> Set ?6v) -> (X-H-conjv : (x-124v : X-Av) -> (x-123v : X-Bv) -> Q-v (conj ?11v ?10v X-Av X-Bv x-124v x-123v)) -> (x-122v : And ?11v ?10v X-Av X-Bv) -> Q-v x-122v
And-rect-Type1 _ _ _ _ _ _ caseconj (conj' a b) = caseconj a b

And-rect-Type0 : (?11v ?10v ?6v : Level) -> (X-Av : Set ?11v) -> (X-Bv : Set ?10v) -> (Q-v : (X-x-122v : And ?11v ?10v X-Av X-Bv) -> Set ?6v) -> (X-H-conjv : (x-124v : X-Av) -> (x-123v : X-Bv) -> Q-v (conj ?11v ?10v X-Av X-Bv x-124v x-123v)) -> (x-122v : And ?11v ?10v X-Av X-Bv) -> Q-v x-122v
And-rect-Type0 _ _ _ _ _ _ caseconj (conj' a b) = caseconj a b


And-inv-ind : (l37 l36 l29 : Level) -> (x1 : Set l37) -> (x2 : Set l36) -> (Hterm : And l37 l36 x1 x2) -> (P : (X-z323 : And l37 l36 x1 x2) -> Set l29) -> (X-H1 : (x-120 : x1) -> (x-119 : x2) -> (X-z324 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-120 x-119)) -> P (conj l37 l36 x1 x2 x-120 x-119)) -> P Hterm
And-inv-ind = λ (l37 l36 l29 : Level) -> λ (x1 : Set l37) -> λ (x2 : Set l36) -> λ (Hterm : And l37 l36 x1 x2) -> λ (P : (X-z323 : And l37 l36 x1 x2) -> Set l29) -> λ (H1 : (x-120 : x1) -> (x-119 : x2) -> (X-z324 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-120 x-119)) -> P (conj l37 l36 x1 x2 x-120 x-119)) -> And-ind l37 l36 ((l37 ⊔ l36) ⊔ l29) x1 x2 (λ (X-x-118 : And l37 l36 x1 x2) -> (X-z324 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm X-x-118) -> P X-x-118) H1 Hterm (refl (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm)

And-inv-rect-Type4 : (l37 l36 l29 : Level) -> (x1 : Set l37) -> (x2 : Set l36) -> (Hterm : And l37 l36 x1 x2) -> (P : (X-z329 : And l37 l36 x1 x2) -> Set l29) -> (X-H1 : (x-124 : x1) -> (x-123 : x2) -> (X-z330 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-124 x-123)) -> P (conj l37 l36 x1 x2 x-124 x-123)) -> P Hterm
And-inv-rect-Type4 = λ (l37 l36 l29 : Level) -> λ (x1 : Set l37) -> λ (x2 : Set l36) -> λ (Hterm : And l37 l36 x1 x2) -> λ (P : (X-z329 : And l37 l36 x1 x2) -> Set l29) -> λ (H1 : (x-124 : x1) -> (x-123 : x2) -> (X-z330 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-124 x-123)) -> P (conj l37 l36 x1 x2 x-124 x-123)) -> And-rect-Type4 l37 l36 ((l37 ⊔ l36) ⊔ l29) x1 x2 (λ (X-x-122 : And l37 l36 x1 x2) -> (X-z330 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm X-x-122) -> P X-x-122) H1 Hterm (refl (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm)

And-inv-rect-Type3 : (l37 l36 l29 : Level) -> (x1 : Set l37) -> (x2 : Set l36) -> (Hterm : And l37 l36 x1 x2) -> (P : (X-z335 : And l37 l36 x1 x2) -> Set l29) -> (X-H1 : (x-132 : x1) -> (x-131 : x2) -> (X-z336 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-132 x-131)) -> P (conj l37 l36 x1 x2 x-132 x-131)) -> P Hterm
And-inv-rect-Type3 = λ (l37 l36 l29 : Level) -> λ (x1 : Set l37) -> λ (x2 : Set l36) -> λ (Hterm : And l37 l36 x1 x2) -> λ (P : (X-z335 : And l37 l36 x1 x2) -> Set l29) -> λ (H1 : (x-132 : x1) -> (x-131 : x2) -> (X-z336 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-132 x-131)) -> P (conj l37 l36 x1 x2 x-132 x-131)) -> And-rect-Type3 l37 l36 ((l37 ⊔ l36) ⊔ l29) x1 x2 (λ (X-x-130 : And l37 l36 x1 x2) -> (X-z336 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm X-x-130) -> P X-x-130) H1 Hterm (refl (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm)

And-inv-rect-Type2 : (l37 l36 l29 : Level) -> (x1 : Set l37) -> (x2 : Set l36) -> (Hterm : And l37 l36 x1 x2) -> (P : (X-z341 : And l37 l36 x1 x2) -> Set l29) -> (X-H1 : (x-136 : x1) -> (x-135 : x2) -> (X-z342 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-136 x-135)) -> P (conj l37 l36 x1 x2 x-136 x-135)) -> P Hterm
And-inv-rect-Type2 = λ (l37 l36 l29 : Level) -> λ (x1 : Set l37) -> λ (x2 : Set l36) -> λ (Hterm : And l37 l36 x1 x2) -> λ (P : (X-z341 : And l37 l36 x1 x2) -> Set l29) -> λ (H1 : (x-136 : x1) -> (x-135 : x2) -> (X-z342 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-136 x-135)) -> P (conj l37 l36 x1 x2 x-136 x-135)) -> And-rect-Type2 l37 l36 ((l37 ⊔ l36) ⊔ l29) x1 x2 (λ (X-x-134 : And l37 l36 x1 x2) -> (X-z342 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm X-x-134) -> P X-x-134) H1 Hterm (refl (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm)

And-inv-rect-Type1 : (l37 l36 l29 : Level) -> (x1 : Set l37) -> (x2 : Set l36) -> (Hterm : And l37 l36 x1 x2) -> (P : (X-z347 : And l37 l36 x1 x2) -> Set l29) -> (X-H1 : (x-140 : x1) -> (x-139 : x2) -> (X-z348 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-140 x-139)) -> P (conj l37 l36 x1 x2 x-140 x-139)) -> P Hterm
And-inv-rect-Type1 = λ (l37 l36 l29 : Level) -> λ (x1 : Set l37) -> λ (x2 : Set l36) -> λ (Hterm : And l37 l36 x1 x2) -> λ (P : (X-z347 : And l37 l36 x1 x2) -> Set l29) -> λ (H1 : (x-140 : x1) -> (x-139 : x2) -> (X-z348 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-140 x-139)) -> P (conj l37 l36 x1 x2 x-140 x-139)) -> And-rect-Type1 l37 l36 ((l37 ⊔ l36) ⊔ l29) x1 x2 (λ (X-x-138 : And l37 l36 x1 x2) -> (X-z348 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm X-x-138) -> P X-x-138) H1 Hterm (refl (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm)

And-inv-rect-Type0 : (l37 l36 l29 : Level) -> (x1 : Set l37) -> (x2 : Set l36) -> (Hterm : And l37 l36 x1 x2) -> (P : (X-z353 : And l37 l36 x1 x2) -> Set l29) -> (X-H1 : (x-144 : x1) -> (x-143 : x2) -> (X-z354 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-144 x-143)) -> P (conj l37 l36 x1 x2 x-144 x-143)) -> P Hterm
And-inv-rect-Type0 = λ (l37 l36 l29 : Level) -> λ (x1 : Set l37) -> λ (x2 : Set l36) -> λ (Hterm : And l37 l36 x1 x2) -> λ (P : (X-z353 : And l37 l36 x1 x2) -> Set l29) -> λ (H1 : (x-144 : x1) -> (x-143 : x2) -> (X-z354 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm (conj l37 l36 x1 x2 x-144 x-143)) -> P (conj l37 l36 x1 x2 x-144 x-143)) -> And-rect-Type0 l37 l36 ((l37 ⊔ l36) ⊔ l29) x1 x2 (λ (X-x-142 : And l37 l36 x1 x2) -> (X-z354 : eq (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm X-x-142) -> P X-x-142) H1 Hterm (refl (l37 ⊔ l36) (And l37 l36 x1 x2) Hterm)

proj1 : (l12 l11 : Level) -> (A : Set l12) -> (B : Set l11) -> (X-- : And l12 l11 A B) -> A
proj1 = λ (l12 l11 : Level) -> λ (A : Set l12) -> λ (B : Set l11) -> λ (AB : And l12 l11 A B) -> And-ind l12 l11 l12 A B (λ (X-x-118 : And l12 l11 A B) -> A) (λ (X-x-120 : A) -> λ (X-x-119 : B) -> X-x-120) AB

proj2 : (l12 l11 : Level) -> (A : Set l12) -> (B : Set l11) -> (X-- : And l12 l11 A B) -> B
proj2 = λ (l12 l11 : Level) -> λ (A : Set l12) -> λ (B : Set l11) -> λ (AB : And l12 l11 A B) -> And-ind l12 l11 l11 A B (λ (X-x-118 : And l12 l11 A B) -> B) (λ (X-x-120 : A) -> λ (X-x-119 : B) -> X-x-119) AB


data Or (?2v ?1v : Level) (X-Av : Set ?2v) (X-Bv : Set ?1v) : Set (lzero ⊔ (?2v ⊔ ?1v)) where
  or-introl' : X-Av -> Or ?2v ?1v X-Av X-Bv
  or-intror' : X-Bv -> Or ?2v ?1v X-Av X-Bv

or-introl : (?3v ?0v : Level) -> (Av : Set ?3v) -> (Bv : Set ?0v) -> (X--v : Av) -> Or ?3v ?0v Av Bv
or-introl _ _ _ _ = or-introl'


or-intror : (?1v ?3v : Level) -> (Av : Set ?1v) -> (Bv : Set ?3v) -> (X--v : Bv) -> Or ?1v ?3v Av Bv
or-intror _ _ _ _ = or-intror'

match-Or : (?10v ?9v : Level) -> (X-Av : Set ?10v) -> (X-Bv : Set ?9v) -> (return-sortv : Level) -> (return-typev : (zv : Or ?10v ?9v X-Av X-Bv) -> Set return-sortv) -> (case-or-introlv : (X--v : X-Av) -> return-typev (or-introl ?10v ?9v X-Av X-Bv X--v)) -> (case-or-introrv : (X--v : X-Bv) -> return-typev (or-intror ?10v ?9v X-Av X-Bv X--v)) -> (zv : Or ?10v ?9v X-Av X-Bv) -> return-typev zv
match-Or _ _ _ _ _ _ casel caser (or-introl' a) = casel a
match-Or _ _ _ _ _ _ casel caser (or-intror' b) = caser b

Or-ind : (?14v ?13v ?10v : Level) -> (X-Av : Set ?14v) -> (X-Bv : Set ?13v) -> (Q-v : (X-x-170v : Or ?14v ?13v X-Av X-Bv) -> Set ?10v) -> (X-H-or-introlv : (x-171v : X-Av) -> Q-v (or-introl ?14v ?13v X-Av X-Bv x-171v)) -> (X-H-or-introrv : (x-172v : X-Bv) -> Q-v (or-intror ?14v ?13v X-Av X-Bv x-172v)) -> (x-170v : Or ?14v ?13v X-Av X-Bv) -> Q-v x-170v
Or-ind _ _ _ _ _ _ casel caser (or-introl' a) = casel a
Or-ind _ _ _ _ _ _ casel caser (or-intror' b) = caser b


Or-inv-ind : (l46 l45 l38 : Level) -> (x1 : Set l46) -> (x2 : Set l45) -> (Hterm : Or l46 l45 x1 x2) -> (P : (X-z389 : Or l46 l45 x1 x2) -> Set l38) -> (X-H1 : (x-171 : x1) -> (X-z390 : eq (l46 ⊔ l45) (Or l46 l45 x1 x2) Hterm (or-introl l46 l45 x1 x2 x-171)) -> P (or-introl l46 l45 x1 x2 x-171)) -> (X-H2 : (x-172 : x2) -> (X-z390 : eq (l46 ⊔ l45) (Or l46 l45 x1 x2) Hterm (or-intror l46 l45 x1 x2 x-172)) -> P (or-intror l46 l45 x1 x2 x-172)) -> P Hterm
Or-inv-ind = λ (l46 l45 l38 : Level) -> λ (x1 : Set l46) -> λ (x2 : Set l45) -> λ (Hterm : Or l46 l45 x1 x2) -> λ (P : (X-z389 : Or l46 l45 x1 x2) -> Set l38) -> λ (H1 : (x-171 : x1) -> (X-z390 : eq (l46 ⊔ l45) (Or l46 l45 x1 x2) Hterm (or-introl l46 l45 x1 x2 x-171)) -> P (or-introl l46 l45 x1 x2 x-171)) -> λ (H2 : (x-172 : x2) -> (X-z390 : eq (l46 ⊔ l45) (Or l46 l45 x1 x2) Hterm (or-intror l46 l45 x1 x2 x-172)) -> P (or-intror l46 l45 x1 x2 x-172)) -> Or-ind l46 l45 ((l46 ⊔ l45) ⊔ l38) x1 x2 (λ (X-x-170 : Or l46 l45 x1 x2) -> (X-z390 : eq (l46 ⊔ l45) (Or l46 l45 x1 x2) Hterm X-x-170) -> P X-x-170) H1 H2 Hterm (refl (l46 ⊔ l45) (Or l46 l45 x1 x2) Hterm)

decidable : (l3 : Level) -> (X-- : Set l3) -> Set l3
decidable = λ (l3 : Level) -> λ (A : Set l3) -> Or l3 l3 A (Not l3 A)


data ex (?2v ?1v : Level)  (Av : Set ?2v)  (X-Pv : (X--v : Av) -> Set ?1v) : Set (lzero ⊔ (?2v ⊔ ?1v)) where
  ex-intro' : (x : Av) -> (px : X-Pv x) -> ex ?2v ?1v Av X-Pv

ex-intro : (?1v ?3v : Level) -> (Av : Set ?1v) -> (Pv : (X--v : Av) -> Set ?3v) -> (xv : Av) -> (X--v : Pv xv) -> ex ?1v ?3v Av Pv
ex-intro _ _ _ _ = ex-intro'

match-ex : (?8v ?7v : Level) -> (Av : Set ?8v) -> (X-Pv : (X--v : Av) -> Set ?7v) -> (return-sortv : Level) -> (return-typev : (zv : ex ?8v ?7v Av X-Pv) -> Set return-sortv) -> (case-ex-introv : (xv : Av) -> (X--v : X-Pv xv) -> return-typev (ex-intro ?8v ?7v Av X-Pv xv X--v)) -> (zv : ex ?8v ?7v Av X-Pv) -> return-typev zv
match-ex _ _ _ _ _ _ case-ex-intro (ex-intro' x px) = case-ex-intro x px

ex-ind : (?11v ?10v ?6v : Level) -> (Av : Set ?11v) -> (X-Pv : (X--v : Av) -> Set ?10v) -> (Q-v : (X-x-235v : ex ?11v ?10v Av X-Pv) -> Set ?6v) -> (X-H-ex-introv : (xv : Av) -> (x-236v : X-Pv xv) -> Q-v (ex-intro ?11v ?10v Av X-Pv xv x-236v)) -> (x-235v : ex ?11v ?10v Av X-Pv) -> Q-v x-235v
ex-ind _ _ _ _ _ _ case-ex-intro (ex-intro' x px) = case-ex-intro x px



ex-inv-ind : (l38 l36 l29 : Level) -> (x1 : Set l38) -> (x2 : (X-- : x1) -> Set l36) -> (Hterm : ex l38 l36 x1 x2) -> (P : (X-z455 : ex l38 l36 x1 x2) -> Set l29) -> (X-H1 : (x : x1) -> (x-236 : x2 x) -> (X-z456 : eq (l38 ⊔ l36) (ex l38 l36 x1 x2) Hterm (ex-intro l38 l36 x1 x2 x x-236)) -> P (ex-intro l38 l36 x1 x2 x x-236)) -> P Hterm
ex-inv-ind = λ (l38 l36 l29 : Level) -> λ (x1 : Set l38) -> λ (x2 : (X-- : x1) -> Set l36) -> λ (Hterm : ex l38 l36 x1 x2) -> λ (P : (X-z455 : ex l38 l36 x1 x2) -> Set l29) -> λ (H1 : (x : x1) -> (x-236 : x2 x) -> (X-z456 : eq (l38 ⊔ l36) (ex l38 l36 x1 x2) Hterm (ex-intro l38 l36 x1 x2 x x-236)) -> P (ex-intro l38 l36 x1 x2 x x-236)) -> ex-ind l38 l36 ((l38 ⊔ l36) ⊔ l29) x1 x2 (λ (X-x-235 : ex l38 l36 x1 x2) -> (X-z456 : eq (l38 ⊔ l36) (ex l38 l36 x1 x2) Hterm X-x-235) -> P X-x-235) H1 Hterm (refl (l38 ⊔ l36) (ex l38 l36 x1 x2) Hterm)


data ex2 (?4v ?3v ?1v : Level)  (Av : Set ?4v)  (X-Pv : (X--v : Av) -> Set ?3v)  (X-Qv : (X--v : Av) -> Set ?1v) : Set (lzero ⊔ ((?4v ⊔ ?3v) ⊔ ?1v)) where
  ex2-intro' : (x : Av) -> (xP : X-Pv x) -> (xQ : X-Qv x) -> ex2 ?4v ?3v ?1v Av X-Pv X-Qv

ex2-intro : (?2v ?5v ?4v : Level) -> (Av : Set ?2v) -> (Pv : (X--v : Av) -> Set ?5v) -> (Qv : (X--v : Av) -> Set ?4v) -> (xv : Av) -> (X--v : Pv xv) -> (X--1v : Qv xv) -> ex2 ?2v ?5v ?4v Av Pv Qv
ex2-intro _ _ _ _ _ _ = ex2-intro'

match-ex2 : (?12v ?10v ?11v : Level) -> (Av : Set ?12v) -> (X-Pv : (X--v : Av) -> Set ?10v) -> (X-Qv : (X--v : Av) -> Set ?11v) -> (return-sortv : Level) -> (return-typev : (zv : ex2 ?12v ?10v ?11v Av X-Pv X-Qv) -> Set return-sortv) -> (case-ex2-introv : (xv : Av) -> (X--v : X-Pv xv) -> (X--1v : X-Qv xv) -> return-typev (ex2-intro ?12v ?10v ?11v Av X-Pv X-Qv xv X--v X--1v)) -> (zv : ex2 ?12v ?10v ?11v Av X-Pv X-Qv) -> return-typev zv
match-ex2 _ _ _ _ _ _ _ _ case-ex2-intro (ex2-intro' x xp xq) = case-ex2-intro x xp xq

ex2-ind : (?15v ?13v ?14v ?8v : Level) -> (Av : Set ?15v) -> (X-Pv : (X--v : Av) -> Set ?13v) -> (X-Qv : (X--v : Av) -> Set ?14v) -> (Q-v : (X-x-274v : ex2 ?15v ?13v ?14v Av X-Pv X-Qv) -> Set ?8v) -> (X-H-ex2-introv : (xv : Av) -> (x-276v : X-Pv xv) -> (x-275v : X-Qv xv) -> Q-v (ex2-intro ?15v ?13v ?14v Av X-Pv X-Qv xv x-276v x-275v)) -> (x-274v : ex2 ?15v ?13v ?14v Av X-Pv X-Qv) -> Q-v x-274v
ex2-ind _ _ _ _ _ _ _ _ case-ex2-intro (ex2-intro' x xp xq) = case-ex2-intro x xp xq


ex2-inv-ind : (l51 l49 l47 l38 : Level) -> (x1 : Set l51) -> (x2 : (X-- : x1) -> Set l49) -> (x3 : (X-- : x1) -> Set l47) -> (Hterm : ex2 l51 l49 l47 x1 x2 x3) -> (P : (X-z521 : ex2 l51 l49 l47 x1 x2 x3) -> Set l38) -> (X-H1 : (x : x1) -> (x-276 : x2 x) -> (x-275 : x3 x) -> (X-z522 : eq ((l47 ⊔ l49) ⊔ l51) (ex2 l51 l49 l47 x1 x2 x3) Hterm (ex2-intro l51 l49 l47 x1 x2 x3 x x-276 x-275)) -> P (ex2-intro l51 l49 l47 x1 x2 x3 x x-276 x-275)) -> P Hterm
ex2-inv-ind = λ (l51 l49 l47 l38 : Level) -> λ (x1 : Set l51) -> λ (x2 : (X-- : x1) -> Set l49) -> λ (x3 : (X-- : x1) -> Set l47) -> λ (Hterm : ex2 l51 l49 l47 x1 x2 x3) -> λ (P : (X-z521 : ex2 l51 l49 l47 x1 x2 x3) -> Set l38) -> λ (H1 : (x : x1) -> (x-276 : x2 x) -> (x-275 : x3 x) -> (X-z522 : eq ((l47 ⊔ l49) ⊔ l51) (ex2 l51 l49 l47 x1 x2 x3) Hterm (ex2-intro l51 l49 l47 x1 x2 x3 x x-276 x-275)) -> P (ex2-intro l51 l49 l47 x1 x2 x3 x x-276 x-275)) -> ex2-ind l51 l49 l47 (((l47 ⊔ l51) ⊔ l38) ⊔ l49) x1 x2 x3 (λ (X-x-274 : ex2 l51 l49 l47 x1 x2 x3) -> (X-z522 : eq ((l47 ⊔ l49) ⊔ l51) (ex2 l51 l49 l47 x1 x2 x3) Hterm X-x-274) -> P X-x-274) H1 Hterm (refl ((l47 ⊔ l49) ⊔ l51) (ex2 l51 l49 l47 x1 x2 x3) Hterm)

ex2-commute : (l44 l33 l31 : Level) -> (A0 : Set l44) -> (P0 : (X-- : A0) -> Set l33) -> (P1 : (X-- : A0) -> Set l31) -> (X-- : ex2 l44 l33 l31 A0 (λ (x0 : A0) -> P0 x0) (λ (x0 : A0) -> P1 x0)) -> ex2 l44 l31 l33 A0 (λ (x0 : A0) -> P1 x0) (λ (x0 : A0) -> P0 x0)
ex2-commute = λ (l44 l33 l31 : Level) -> λ (A0 : Set l44) -> λ (P0 : (X-- : A0) -> Set l33) -> λ (P1 : (X-- : A0) -> Set l31) -> λ (X-clearme : ex2 l44 l33 l31 A0 (λ (x0 : A0) -> P0 x0) (λ (x0 : A0) -> P1 x0)) -> match-ex2 l44 l33 l31 A0 (λ (x0 : A0) -> P0 x0) (λ (x0 : A0) -> P1 x0) ((l44 ⊔ l33) ⊔ l31) (λ (X-- : ex2 l44 l33 l31 A0 (λ (x0 : A0) -> P0 x0) (λ (x0 : A0) -> P1 x0)) -> ex2 l44 l31 l33 A0 (λ (x0 : A0) -> P1 x0) (λ (x0 : A0) -> P0 x0)) (λ (x : A0) -> λ (auto : P0 x) -> λ (auto' : P1 x) -> ex2-intro l44 l31 l33 A0 (λ (x0 : A0) -> P1 x0) (λ (x0 : A0) -> P0 x0) x auto' auto) X-clearme

iff : (l9 l8 : Level) -> (X-A : Set l9) -> (X-B : Set l8) -> Set (lzero ⊔ (l9 ⊔ l8))
iff = λ (l9 l8 : Level) -> λ (A : Set l9) -> λ (B : Set l8) -> And (l9 ⊔ l8) (l9 ⊔ l8) ((X-- : A) -> B) ((X-- : B) -> A)

iff-sym : (l38 l37 : Level) -> (A : Set l38) -> (B : Set l37) -> (X-- : iff l38 l37 A B) -> iff l37 l38 B A
iff-sym = λ (l38 l37 : Level) -> λ (A : Set l38) -> λ (B : Set l37) -> λ (X-clearme : iff l38 l37 A B) -> match-And (l38 ⊔ l37) (l38 ⊔ l37) ((X-- : A) -> B) ((X-- : B) -> A) (l38 ⊔ l37) (λ (X-- : And (l38 ⊔ l37) (l38 ⊔ l37) ((X-- : A) -> B) ((X-- : B) -> A)) -> iff l37 l38 B A) (λ (auto : (X-- : A) -> B) -> λ (auto' : (X-- : B) -> A) -> conj (l38 ⊔ l37) (l38 ⊔ l37) ((X-- : B) -> A) ((X-- : A) -> B) (λ (auto'' : B) -> auto' auto'') (λ (auto'' : A) -> auto auto'')) X-clearme

iff-trans : (l73 l72 l71 : Level) -> (A : Set l73) -> (B : Set l72) -> (C : Set l71) -> (X-- : iff l73 l72 A B) -> (X--1 : iff l72 l71 B C) -> iff l73 l71 A C
iff-trans = λ (l73 l72 l71 : Level) -> λ (A : Set l73) -> λ (B : Set l72) -> λ (C : Set l71) -> λ (X-clearme : iff l73 l72 A B) -> match-And (l73 ⊔ l72) (l73 ⊔ l72) ((X-- : A) -> B) ((X-- : B) -> A) ((l73 ⊔ l72) ⊔ l71) (λ (X-- : And (l73 ⊔ l72) (l73 ⊔ l72) ((X-- : A) -> B) ((X-- : B) -> A)) -> (X--1 : iff l72 l71 B C) -> iff l73 l71 A C) (λ (H1 : (X-- : A) -> B) -> λ (H2 : (X-- : B) -> A) -> λ (X-clearme0 : iff l72 l71 B C) -> match-And (l72 ⊔ l71) (l72 ⊔ l71) ((X-- : B) -> C) ((X-- : C) -> B) (l73 ⊔ l71) (λ (X-- : And (l72 ⊔ l71) (l72 ⊔ l71) ((X-- : B) -> C) ((X-- : C) -> B)) -> iff l73 l71 A C) (λ (H3 : (X-- : B) -> C) -> λ (H4 : (X-- : C) -> B) -> conj (l73 ⊔ l71) (l73 ⊔ l71) ((X-- : A) -> C) ((X-- : C) -> A) (λ (auto : A) -> H3 (H1 auto)) (λ (auto : C) -> H2 (H4 auto))) X-clearme0) X-clearme

iff-not : (ll1 ll0 : Level) -> (A : Set (lzero ⊔ (ll1 ⊔ ll0))) -> (B : Set (lzero ⊔ (ll1 ⊔ ll0))) -> (X-- : iff (ll1 ⊔ ll0) (ll1 ⊔ ll0) A B) -> iff (ll1 ⊔ ll0) (ll1 ⊔ ll0) (Not (ll1 ⊔ ll0) A) (Not (ll1 ⊔ ll0) B)
iff-not = λ (ll1 ll0 : Level) -> λ (A : Set (lzero ⊔ (ll1 ⊔ ll0))) -> λ (B : Set (lzero ⊔ (ll1 ⊔ ll0))) -> λ (X-clearme : iff (ll1 ⊔ ll0) (ll1 ⊔ ll0) A B) -> match-And (ll1 ⊔ ll0) (ll1 ⊔ ll0) ((X-- : A) -> B) ((X-- : B) -> A) (ll1 ⊔ ll0) (λ (X-- : And (ll1 ⊔ ll0) (ll1 ⊔ ll0) ((X-- : A) -> B) ((X-- : B) -> A)) -> iff (ll1 ⊔ ll0) (ll1 ⊔ ll0) (Not (ll1 ⊔ ll0) A) (Not (ll1 ⊔ ll0) B)) (λ (H1 : (X-- : A) -> B) -> λ (H2 : (X-- : B) -> A) -> conj (ll1 ⊔ ll0) (ll1 ⊔ ll0) ((X-- : Not (ll1 ⊔ ll0) A) -> Not (ll1 ⊔ ll0) B) ((X-- : Not (ll1 ⊔ ll0) B) -> Not (ll1 ⊔ ll0) A) (λ (auto : Not (ll1 ⊔ ll0) A) -> not-to-not (ll1 ⊔ ll0) B A (λ (auto' : B) -> H2 auto') auto) (λ (auto : Not (ll1 ⊔ ll0) B) -> not-to-not (ll1 ⊔ ll0) A B (λ (auto' : A) -> H1 auto') auto)) X-clearme

iff-and-l : (l83 l82 l81 : Level) -> (A : Set l83) -> (B : Set l82) -> (C : Set l81) -> (X-- : iff l83 l82 A B) -> iff (l83 ⊔ l81) (l82 ⊔ l81) (And l81 l83 C A) (And l81 l82 C B)
iff-and-l = λ (l83 l82 l81 : Level) -> λ (A : Set l83) -> λ (B : Set l82) -> λ (C : Set l81) -> λ (X-clearme : iff l83 l82 A B) -> match-And (l83 ⊔ l82) (l83 ⊔ l82) ((X-- : A) -> B) ((X-- : B) -> A) ((l83 ⊔ l82) ⊔ l81) (λ (X-- : And (l83 ⊔ l82) (l83 ⊔ l82) ((X-- : A) -> B) ((X-- : B) -> A)) -> iff (l83 ⊔ l81) (l82 ⊔ l81) (And l81 l83 C A) (And l81 l82 C B)) (λ (H1 : (X-- : A) -> B) -> λ (H2 : (X-- : B) -> A) -> conj ((l83 ⊔ l82) ⊔ l81) ((l83 ⊔ l82) ⊔ l81) ((X-- : And l81 l83 C A) -> And l81 l82 C B) ((X-- : And l81 l82 C B) -> And l81 l83 C A) (λ (X-clearme0 : And l81 l83 C A) -> match-And l81 l83 C A (l82 ⊔ l81) (λ (X-- : And l81 l83 C A) -> And l81 l82 C B) (λ (auto : C) -> λ (auto' : A) -> conj l81 l82 C B auto (H1 auto')) X-clearme0) (λ (X-clearme0 : And l81 l82 C B) -> match-And l81 l82 C B (l83 ⊔ l81) (λ (X-- : And l81 l82 C B) -> And l81 l83 C A) (λ (auto : C) -> λ (auto' : B) -> conj l81 l83 C A auto (H2 auto')) X-clearme0)) X-clearme

iff-and-r : (l83 l82 l81 : Level) -> (A : Set l83) -> (B : Set l82) -> (C : Set l81) -> (X-- : iff l83 l82 A B) -> iff (l83 ⊔ l81) (l82 ⊔ l81) (And l83 l81 A C) (And l82 l81 B C)
iff-and-r = λ (l83 l82 l81 : Level) -> λ (A : Set l83) -> λ (B : Set l82) -> λ (C : Set l81) -> λ (X-clearme : iff l83 l82 A B) -> match-And (l83 ⊔ l82) (l83 ⊔ l82) ((X-- : A) -> B) ((X-- : B) -> A) ((l83 ⊔ l82) ⊔ l81) (λ (X-- : And (l83 ⊔ l82) (l83 ⊔ l82) ((X-- : A) -> B) ((X-- : B) -> A)) -> iff (l83 ⊔ l81) (l82 ⊔ l81) (And l83 l81 A C) (And l82 l81 B C)) (λ (H1 : (X-- : A) -> B) -> λ (H2 : (X-- : B) -> A) -> conj ((l83 ⊔ l82) ⊔ l81) ((l83 ⊔ l82) ⊔ l81) ((X-- : And l83 l81 A C) -> And l82 l81 B C) ((X-- : And l82 l81 B C) -> And l83 l81 A C) (λ (X-clearme0 : And l83 l81 A C) -> match-And l83 l81 A C (l82 ⊔ l81) (λ (X-- : And l83 l81 A C) -> And l82 l81 B C) (λ (auto : A) -> λ (auto' : C) -> conj l82 l81 B C (H1 auto) auto') X-clearme0) (λ (X-clearme0 : And l82 l81 B C) -> match-And l82 l81 B C (l83 ⊔ l81) (λ (X-- : And l82 l81 B C) -> And l83 l81 A C) (λ (auto : B) -> λ (auto' : C) -> conj l83 l81 A C (H2 auto) auto') X-clearme0)) X-clearme

iff-or-l : (l87 l86 l85 : Level) -> (A : Set l87) -> (B : Set l86) -> (C : Set l85) -> (X-- : iff l87 l86 A B) -> iff (l87 ⊔ l85) (l86 ⊔ l85) (Or l85 l87 C A) (Or l85 l86 C B)
iff-or-l = λ (l87 l86 l85 : Level) -> λ (A : Set l87) -> λ (B : Set l86) -> λ (C : Set l85) -> λ (X-clearme : iff l87 l86 A B) -> match-And (l87 ⊔ l86) (l87 ⊔ l86) ((X-- : A) -> B) ((X-- : B) -> A) ((l87 ⊔ l86) ⊔ l85) (λ (X-- : And (l87 ⊔ l86) (l87 ⊔ l86) ((X-- : A) -> B) ((X-- : B) -> A)) -> iff (l87 ⊔ l85) (l86 ⊔ l85) (Or l85 l87 C A) (Or l85 l86 C B)) (λ (H1 : (X-- : A) -> B) -> λ (H2 : (X-- : B) -> A) -> conj ((l87 ⊔ l86) ⊔ l85) ((l87 ⊔ l86) ⊔ l85) ((X-- : Or l85 l87 C A) -> Or l85 l86 C B) ((X-- : Or l85 l86 C B) -> Or l85 l87 C A) (λ (X-clearme0 : Or l85 l87 C A) -> match-Or l85 l87 C A (l86 ⊔ l85) (λ (X-- : Or l85 l87 C A) -> Or l85 l86 C B) (λ (auto : C) -> or-introl l85 l86 C B auto) (λ (auto : A) -> or-intror l85 l86 C B (H1 auto)) X-clearme0) (λ (X-clearme0 : Or l85 l86 C B) -> match-Or l85 l86 C B (l87 ⊔ l85) (λ (X-- : Or l85 l86 C B) -> Or l85 l87 C A) (λ (auto : C) -> or-introl l85 l87 C A auto) (λ (auto : B) -> or-intror l85 l87 C A (H2 auto)) X-clearme0)) X-clearme

iff-or-r : (l87 l86 l85 : Level) -> (A : Set l87) -> (B : Set l86) -> (C : Set l85) -> (X-- : iff l87 l86 A B) -> iff (l87 ⊔ l85) (l86 ⊔ l85) (Or l87 l85 A C) (Or l86 l85 B C)
iff-or-r = λ (l87 l86 l85 : Level) -> λ (A : Set l87) -> λ (B : Set l86) -> λ (C : Set l85) -> λ (X-clearme : iff l87 l86 A B) -> match-And (l87 ⊔ l86) (l87 ⊔ l86) ((X-- : A) -> B) ((X-- : B) -> A) ((l87 ⊔ l86) ⊔ l85) (λ (X-- : And (l87 ⊔ l86) (l87 ⊔ l86) ((X-- : A) -> B) ((X-- : B) -> A)) -> iff (l87 ⊔ l85) (l86 ⊔ l85) (Or l87 l85 A C) (Or l86 l85 B C)) (λ (H1 : (X-- : A) -> B) -> λ (H2 : (X-- : B) -> A) -> conj ((l87 ⊔ l86) ⊔ l85) ((l87 ⊔ l86) ⊔ l85) ((X-- : Or l87 l85 A C) -> Or l86 l85 B C) ((X-- : Or l86 l85 B C) -> Or l87 l85 A C) (λ (X-clearme0 : Or l87 l85 A C) -> match-Or l87 l85 A C (l86 ⊔ l85) (λ (X-- : Or l87 l85 A C) -> Or l86 l85 B C) (λ (auto : A) -> or-introl l86 l85 B C (H1 auto)) (λ (auto : C) -> or-intror l86 l85 B C auto) X-clearme0) (λ (X-clearme0 : Or l86 l85 B C) -> match-Or l86 l85 B C (l87 ⊔ l85) (λ (X-- : Or l86 l85 B C) -> Or l87 l85 A C) (λ (auto : B) -> or-introl l87 l85 A C (H2 auto)) (λ (auto : C) -> or-intror l87 l85 A C auto) X-clearme0)) X-clearme

R0 : (l1 : Level) -> (T : Set l1) -> (X-t : T) -> T
R0 = λ (l1 : Level) -> λ (T : Set l1) -> λ (t : T) -> t

R1 : (l13 l8 : Level) -> (A : Set l13) -> (X-x : A) -> (Q- : (x-19 : A) -> (X-x-20 : eq l13 A X-x x-19) -> Set l8) -> (X-H-refl : Q- X-x (refl l13 A X-x)) -> (x-19 : A) -> (x-20 : eq l13 A X-x x-19) -> Q- x-19 x-20
R1 = λ (l13 l8 : Level) -> eq-rect-Type0 l13 l8

R2 : (l42 l37 l26 : Level) -> (T0 : Set l42) -> (a0 : T0) -> (T1 : (x0 : T0) -> (X-- : eq l42 T0 a0 x0) -> Set l37) -> (a1 : T1 a0 (refl l42 T0 a0)) -> (T2 : (x0 : T0) -> (p0 : eq l42 T0 a0 x0) -> (x1 : T1 x0 p0) -> (X-- : eq l37 (T1 x0 p0) (R1 l42 l37 T0 a0 T1 a1 x0 p0) x1) -> Set l26) -> (X-a2 : T2 a0 (refl l42 T0 a0) a1 (refl l37 (T1 a0 (refl l42 T0 a0)) a1)) -> (b0 : T0) -> (e0 : eq l42 T0 a0 b0) -> (b1 : T1 b0 e0) -> (e1 : eq l37 (T1 b0 e0) (R1 l42 l37 T0 a0 T1 a1 b0 e0) b1) -> T2 b0 e0 b1 e1
R2 = λ (l42 l37 l26 : Level) -> λ (T0 : Set l42) -> λ (a0 : T0) -> λ (T1 : (x0 : T0) -> (X-- : eq l42 T0 a0 x0) -> Set l37) -> λ (a1 : T1 a0 (refl l42 T0 a0)) -> λ (T2 : (x0 : T0) -> (p0 : eq l42 T0 a0 x0) -> (x1 : T1 x0 p0) -> (X-- : eq l37 (T1 x0 p0) (R1 l42 l37 T0 a0 T1 a1 x0 p0) x1) -> Set l26) -> λ (a2 : T2 a0 (refl l42 T0 a0) a1 (refl l37 (T1 a0 (refl l42 T0 a0)) a1)) -> λ (b0 : T0) -> λ (e0 : eq l42 T0 a0 b0) -> λ (b1 : T1 b0 e0) -> λ (e1 : eq l37 (T1 b0 e0) (R1 l42 l37 T0 a0 T1 a1 b0 e0) b1) -> eq-rect-Type0 l37 l26 (T1 b0 e0) (R1 l42 l37 T0 a0 T1 a1 b0 e0) (T2 b0 e0) (R1 l42 l26 T0 a0 (λ (x-19 : T0) -> λ (X-x-20 : eq l42 T0 a0 x-19) -> T2 x-19 X-x-20 (R1 l42 l37 T0 a0 T1 a1 x-19 X-x-20) (refl l37 (T1 x-19 X-x-20) (R1 l42 l37 T0 a0 T1 a1 x-19 X-x-20))) a2 b0 e0) b1 e1

R3 : (l80 l75 l64 l45 : Level) -> (T0 : Set l80) -> (a0 : T0) -> (T1 : (x0 : T0) -> (X-- : eq l80 T0 a0 x0) -> Set l75) -> (a1 : T1 a0 (refl l80 T0 a0)) -> (T2 : (x0 : T0) -> (p0 : eq l80 T0 a0 x0) -> (x1 : T1 x0 p0) -> (X-- : eq l75 (T1 x0 p0) (R1 l80 l75 T0 a0 T1 a1 x0 p0) x1) -> Set l64) -> (a2 : T2 a0 (refl l80 T0 a0) a1 (refl l75 (T1 a0 (refl l80 T0 a0)) a1)) -> (T3 : (x0 : T0) -> (p0 : eq l80 T0 a0 x0) -> (x1 : T1 x0 p0) -> (p1 : eq l75 (T1 x0 p0) (R1 l80 l75 T0 a0 T1 a1 x0 p0) x1) -> (x2 : T2 x0 p0 x1 p1) -> (X-- : eq l64 (T2 x0 p0 x1 p1) (R2 l80 l75 l64 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2) -> Set l45) -> (X-a3 : T3 a0 (refl l80 T0 a0) a1 (refl l75 (T1 a0 (refl l80 T0 a0)) a1) a2 (refl l64 (T2 a0 (refl l80 T0 a0) a1 (refl l75 (T1 a0 (refl l80 T0 a0)) a1)) a2)) -> (b0 : T0) -> (e0 : eq l80 T0 a0 b0) -> (b1 : T1 b0 e0) -> (e1 : eq l75 (T1 b0 e0) (R1 l80 l75 T0 a0 T1 a1 b0 e0) b1) -> (b2 : T2 b0 e0 b1 e1) -> (e2 : eq l64 (T2 b0 e0 b1 e1) (R2 l80 l75 l64 T0 a0 T1 a1 T2 a2 b0 e0 b1 e1) b2) -> T3 b0 e0 b1 e1 b2 e2
R3 = λ (l80 l75 l64 l45 : Level) -> λ (T0 : Set l80) -> λ (a0 : T0) -> λ (T1 : (x0 : T0) -> (X-- : eq l80 T0 a0 x0) -> Set l75) -> λ (a1 : T1 a0 (refl l80 T0 a0)) -> λ (T2 : (x0 : T0) -> (p0 : eq l80 T0 a0 x0) -> (x1 : T1 x0 p0) -> (X-- : eq l75 (T1 x0 p0) (R1 l80 l75 T0 a0 T1 a1 x0 p0) x1) -> Set l64) -> λ (a2 : T2 a0 (refl l80 T0 a0) a1 (refl l75 (T1 a0 (refl l80 T0 a0)) a1)) -> λ (T3 : (x0 : T0) -> (p0 : eq l80 T0 a0 x0) -> (x1 : T1 x0 p0) -> (p1 : eq l75 (T1 x0 p0) (R1 l80 l75 T0 a0 T1 a1 x0 p0) x1) -> (x2 : T2 x0 p0 x1 p1) -> (X-- : eq l64 (T2 x0 p0 x1 p1) (R2 l80 l75 l64 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2) -> Set l45) -> λ (a3 : T3 a0 (refl l80 T0 a0) a1 (refl l75 (T1 a0 (refl l80 T0 a0)) a1) a2 (refl l64 (T2 a0 (refl l80 T0 a0) a1 (refl l75 (T1 a0 (refl l80 T0 a0)) a1)) a2)) -> λ (b0 : T0) -> λ (e0 : eq l80 T0 a0 b0) -> λ (b1 : T1 b0 e0) -> λ (e1 : eq l75 (T1 b0 e0) (R1 l80 l75 T0 a0 T1 a1 b0 e0) b1) -> λ (b2 : T2 b0 e0 b1 e1) -> λ (e2 : eq l64 (T2 b0 e0 b1 e1) (R2 l80 l75 l64 T0 a0 T1 a1 T2 a2 b0 e0 b1 e1) b2) -> eq-rect-Type0 l64 l45 (T2 b0 e0 b1 e1) (R2 l80 l75 l64 T0 a0 T1 a1 T2 a2 b0 e0 b1 e1) (T3 b0 e0 b1 e1) (R2 l80 l75 l45 T0 a0 T1 a1 (λ (x0 : T0) -> λ (p0 : eq l80 T0 a0 x0) -> λ (x1 : T1 x0 p0) -> λ (X-- : eq l75 (T1 x0 p0) (R1 l80 l75 T0 a0 T1 a1 x0 p0) x1) -> T3 x0 p0 x1 X-- (R2 l80 l75 l64 T0 a0 T1 a1 T2 a2 x0 p0 x1 X--) (refl l64 (T2 x0 p0 x1 X--) (R2 l80 l75 l64 T0 a0 T1 a1 T2 a2 x0 p0 x1 X--))) a3 b0 e0 b1 e1) b2 e2

R4 : (l135 l130 l119 l100 l70 : Level) -> (T0 : Set l135) -> (a0 : T0) -> (T1 : (x0 : T0) -> (X-- : eq l135 T0 a0 x0) -> Set l130) -> (a1 : T1 a0 (refl l135 T0 a0)) -> (T2 : (x0 : T0) -> (p0 : eq l135 T0 a0 x0) -> (x1 : T1 x0 p0) -> (X-- : eq l130 (T1 x0 p0) (R1 l135 l130 T0 a0 T1 a1 x0 p0) x1) -> Set l119) -> (a2 : T2 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1)) -> (T3 : (x0 : T0) -> (p0 : eq l135 T0 a0 x0) -> (x1 : T1 x0 p0) -> (p1 : eq l130 (T1 x0 p0) (R1 l135 l130 T0 a0 T1 a1 x0 p0) x1) -> (x2 : T2 x0 p0 x1 p1) -> (X-- : eq l119 (T2 x0 p0 x1 p1) (R2 l135 l130 l119 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2) -> Set l100) -> (a3 : T3 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1) a2 (refl l119 (T2 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1)) a2)) -> (T4 : (x0 : T0) -> (p0 : eq l135 T0 a0 x0) -> (x1 : T1 x0 p0) -> (p1 : eq l130 (T1 x0 p0) (R1 l135 l130 T0 a0 T1 a1 x0 p0) x1) -> (x2 : T2 x0 p0 x1 p1) -> (p2 : eq l119 (T2 x0 p0 x1 p1) (R2 l135 l130 l119 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2) -> (x3 : T3 x0 p0 x1 p1 x2 p2) -> (X-p3 : eq l100 (T3 x0 p0 x1 p1 x2 p2) (R3 l135 l130 l119 l100 T0 a0 T1 a1 T2 a2 T3 a3 x0 p0 x1 p1 x2 p2) x3) -> Set l70) -> (X-a4 : T4 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1) a2 (refl l119 (T2 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1)) a2) a3 (refl l100 (T3 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1) a2 (refl l119 (T2 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1)) a2)) a3)) -> (b0 : T0) -> (e0 : eq l135 T0 a0 b0) -> (b1 : T1 b0 e0) -> (e1 : eq l130 (T1 b0 e0) (R1 l135 l130 T0 a0 T1 a1 b0 e0) b1) -> (b2 : T2 b0 e0 b1 e1) -> (e2 : eq l119 (T2 b0 e0 b1 e1) (R2 l135 l130 l119 T0 a0 T1 a1 T2 a2 b0 e0 b1 e1) b2) -> (b3 : T3 b0 e0 b1 e1 b2 e2) -> (e3 : eq l100 (T3 b0 e0 b1 e1 b2 e2) (R3 l135 l130 l119 l100 T0 a0 T1 a1 T2 a2 T3 a3 b0 e0 b1 e1 b2 e2) b3) -> T4 b0 e0 b1 e1 b2 e2 b3 e3
R4 = λ (l135 l130 l119 l100 l70 : Level) -> λ (T0 : Set l135) -> λ (a0 : T0) -> λ (T1 : (x0 : T0) -> (X-- : eq l135 T0 a0 x0) -> Set l130) -> λ (a1 : T1 a0 (refl l135 T0 a0)) -> λ (T2 : (x0 : T0) -> (p0 : eq l135 T0 a0 x0) -> (x1 : T1 x0 p0) -> (X-- : eq l130 (T1 x0 p0) (R1 l135 l130 T0 a0 T1 a1 x0 p0) x1) -> Set l119) -> λ (a2 : T2 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1)) -> λ (T3 : (x0 : T0) -> (p0 : eq l135 T0 a0 x0) -> (x1 : T1 x0 p0) -> (p1 : eq l130 (T1 x0 p0) (R1 l135 l130 T0 a0 T1 a1 x0 p0) x1) -> (x2 : T2 x0 p0 x1 p1) -> (X-- : eq l119 (T2 x0 p0 x1 p1) (R2 l135 l130 l119 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2) -> Set l100) -> λ (a3 : T3 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1) a2 (refl l119 (T2 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1)) a2)) -> λ (T4 : (x0 : T0) -> (p0 : eq l135 T0 a0 x0) -> (x1 : T1 x0 p0) -> (p1 : eq l130 (T1 x0 p0) (R1 l135 l130 T0 a0 T1 a1 x0 p0) x1) -> (x2 : T2 x0 p0 x1 p1) -> (p2 : eq l119 (T2 x0 p0 x1 p1) (R2 l135 l130 l119 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2) -> (x3 : T3 x0 p0 x1 p1 x2 p2) -> (X-p3 : eq l100 (T3 x0 p0 x1 p1 x2 p2) (R3 l135 l130 l119 l100 T0 a0 T1 a1 T2 a2 T3 a3 x0 p0 x1 p1 x2 p2) x3) -> Set l70) -> λ (a4 : T4 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1) a2 (refl l119 (T2 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1)) a2) a3 (refl l100 (T3 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1) a2 (refl l119 (T2 a0 (refl l135 T0 a0) a1 (refl l130 (T1 a0 (refl l135 T0 a0)) a1)) a2)) a3)) -> λ (b0 : T0) -> λ (e0 : eq l135 T0 a0 b0) -> λ (b1 : T1 b0 e0) -> λ (e1 : eq l130 (T1 b0 e0) (R1 l135 l130 T0 a0 T1 a1 b0 e0) b1) -> λ (b2 : T2 b0 e0 b1 e1) -> λ (e2 : eq l119 (T2 b0 e0 b1 e1) (R2 l135 l130 l119 T0 a0 T1 a1 T2 a2 b0 e0 b1 e1) b2) -> λ (b3 : T3 b0 e0 b1 e1 b2 e2) -> λ (e3 : eq l100 (T3 b0 e0 b1 e1 b2 e2) (R3 l135 l130 l119 l100 T0 a0 T1 a1 T2 a2 T3 a3 b0 e0 b1 e1 b2 e2) b3) -> eq-rect-Type0 l100 l70 (T3 b0 e0 b1 e1 b2 e2) (R3 l135 l130 l119 l100 T0 a0 T1 a1 T2 a2 T3 a3 b0 e0 b1 e1 b2 e2) (T4 b0 e0 b1 e1 b2 e2) (R3 l135 l130 l119 l70 T0 a0 T1 a1 T2 a2 (λ (x0 : T0) -> λ (p0 : eq l135 T0 a0 x0) -> λ (x1 : T1 x0 p0) -> λ (p1 : eq l130 (T1 x0 p0) (R1 l135 l130 T0 a0 T1 a1 x0 p0) x1) -> λ (x2 : T2 x0 p0 x1 p1) -> λ (X-- : eq l119 (T2 x0 p0 x1 p1) (R2 l135 l130 l119 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2) -> T4 x0 p0 x1 p1 x2 X-- (R3 l135 l130 l119 l100 T0 a0 T1 a1 T2 a2 T3 a3 x0 p0 x1 p1 x2 X--) (refl l100 (T3 x0 p0 x1 p1 x2 X--) (R3 l135 l130 l119 l100 T0 a0 T1 a1 T2 a2 T3 a3 x0 p0 x1 p1 x2 X--))) a4 b0 e0 b1 e1 b2 e2) b3 e3

eqProp : (l1 : Level) -> (A : Set l1) -> (X-x : A) -> (X-- : A) -> Set l1
eqProp = λ (l1 : Level) -> λ (A : Set l1) -> eq l1 A


streicherK : (?7v ?4v : Level) -> (Tv : Set ?7v) -> (tv : Tv) -> (Pv : (X--v : eq ?7v Tv tv tv) -> Set ?4v) -> (X--v : Pv (refl ?7v Tv tv)) -> (pv : eq ?7v Tv tv tv) -> Pv pv
streicherK _ _ _ _ _ p refl' = p
