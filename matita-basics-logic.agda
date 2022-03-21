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



eq-rect-r : (?35v ?16v : Level) -> (Av : Set ?35v) -> (av : Av) -> (xv : Av) -> (pv : eq ?35v Av xv av) -> (Pv : (x0v : Av) -> (X--v : eq ?35v Av x0v av) -> Set ?16v) -> (X--v : Pv av (refl ?35v Av av)) -> Pv xv pv
eq-rect-r = λ (?35v ?16v : Level) -> λ (Av : Set ?35v) -> λ (av : Av) -> λ (xv : Av) -> λ (pv : eq ?35v Av xv av) -> match-eq ?35v Av xv ((lsuc lzero) ⊔ (?35v ⊔ (lsuc ?16v))) (λ (X--v : Av) -> λ (X-0v : eq ?35v Av xv X--v) -> (Pv : (x0v : Av) -> (X--1v : eq ?35v Av x0v X--v) -> Set ?16v) -> (X--1v : Pv X--v (refl ?35v Av X--v)) -> Pv xv X-0v) (λ (Pv : (x0v : Av) -> (X--v : eq ?35v Av x0v xv) -> Set ?16v) -> λ (autov : Pv xv (refl ?35v Av xv)) -> autov) av pv

eq-ind-r : (?15v ?10v : Level) -> (Av : Set ?15v) -> (av : Av) -> (Pv : (xv : Av) -> (X--v : eq ?15v Av xv av) -> Set ?10v) -> (X--v : Pv av (refl ?15v Av av)) -> (xv : Av) -> (pv : eq ?15v Av xv av) -> Pv xv pv
eq-ind-r = λ (?15v ?10v : Level) -> λ (Av : Set ?15v) -> λ (av : Av) -> λ (Pv : (xv : Av) -> (X--v : eq ?15v Av xv av) -> Set ?10v) -> λ (pv : Pv av (refl ?15v Av av)) -> λ (x0v : Av) -> λ (p0v : eq ?15v Av x0v av) -> eq-rect-r ?15v ?10v Av av x0v p0v (λ (x01v : Av) -> λ (X--v : eq ?15v Av x01v av) -> Pv x01v X--v) pv

eq-rect-Type0-r : (?41v ?36v : Level) -> (Av : Set ?41v) -> (av : Av) -> (Pv : (xv : Av) -> (X--v : eq ?41v Av xv av) -> Set ?36v) -> (X--v : Pv av (refl ?41v Av av)) -> (xv : Av) -> (pv : eq ?41v Av xv av) -> Pv xv pv
eq-rect-Type0-r = λ (?41v ?36v : Level) -> λ (Av : Set ?41v) -> λ (av : Av) -> λ (Pv : (xv : Av) -> (X--v : eq ?41v Av xv av) -> Set ?36v) -> λ (Hv : Pv av (refl ?41v Av av)) -> λ (xv : Av) -> λ (pv : eq ?41v Av xv av) -> match-eq ?41v Av xv ((lsuc lzero) ⊔ (?41v ⊔ (lsuc ?36v))) (λ (X--v : Av) -> λ (X-0v : eq ?41v Av xv X--v) -> (fv : (x0v : Av) -> (X--1v : eq ?41v Av x0v X--v) -> Set ?36v) -> (X--1v : fv X--v (refl ?41v Av X--v)) -> fv xv X-0v) (λ (fv : (x0v : Av) -> (X--v : eq ?41v Av x0v xv) -> Set ?36v) -> λ (autov : fv xv (refl ?41v Av xv)) -> autov) av pv Pv Hv

eq-rect-Type1-r : (?41v ?36v : Level) -> (Av : Set ?41v) -> (av : Av) -> (Pv : (xv : Av) -> (X--v : eq ?41v Av xv av) -> Set ?36v) -> (X--v : Pv av (refl ?41v Av av)) -> (xv : Av) -> (pv : eq ?41v Av xv av) -> Pv xv pv
eq-rect-Type1-r = λ (?41v ?36v : Level) -> λ (Av : Set ?41v) -> λ (av : Av) -> λ (Pv : (xv : Av) -> (X--v : eq ?41v Av xv av) -> Set ?36v) -> λ (Hv : Pv av (refl ?41v Av av)) -> λ (xv : Av) -> λ (pv : eq ?41v Av xv av) -> match-eq ?41v Av xv ((lsuc lzero) ⊔ (?41v ⊔ (lsuc ?36v))) (λ (X--v : Av) -> λ (X-0v : eq ?41v Av xv X--v) -> (fv : (x0v : Av) -> (X--1v : eq ?41v Av x0v X--v) -> Set ?36v) -> (X--1v : fv X--v (refl ?41v Av X--v)) -> fv xv X-0v) (λ (fv : (x0v : Av) -> (X--v : eq ?41v Av x0v xv) -> Set ?36v) -> λ (autov : fv xv (refl ?41v Av xv)) -> autov) av pv Pv Hv

eq-rect-Type2-r : (?41v ?36v : Level) -> (Av : Set ?41v) -> (av : Av) -> (Pv : (xv : Av) -> (X--v : eq ?41v Av xv av) -> Set ?36v) -> (X--v : Pv av (refl ?41v Av av)) -> (xv : Av) -> (pv : eq ?41v Av xv av) -> Pv xv pv
eq-rect-Type2-r = λ (?41v ?36v : Level) -> λ (Av : Set ?41v) -> λ (av : Av) -> λ (Pv : (xv : Av) -> (X--v : eq ?41v Av xv av) -> Set ?36v) -> λ (Hv : Pv av (refl ?41v Av av)) -> λ (xv : Av) -> λ (pv : eq ?41v Av xv av) -> match-eq ?41v Av xv ((lsuc lzero) ⊔ (?41v ⊔ (lsuc ?36v))) (λ (X--v : Av) -> λ (X-0v : eq ?41v Av xv X--v) -> (fv : (x0v : Av) -> (X--1v : eq ?41v Av x0v X--v) -> Set ?36v) -> (X--1v : fv X--v (refl ?41v Av X--v)) -> fv xv X-0v) (λ (fv : (x0v : Av) -> (X--v : eq ?41v Av x0v xv) -> Set ?36v) -> λ (autov : fv xv (refl ?41v Av xv)) -> autov) av pv Pv Hv

eq-rect-Type3-r : (?41v ?36v : Level) -> (Av : Set ?41v) -> (av : Av) -> (Pv : (xv : Av) -> (X--v : eq ?41v Av xv av) -> Set ?36v) -> (X--v : Pv av (refl ?41v Av av)) -> (xv : Av) -> (pv : eq ?41v Av xv av) -> Pv xv pv
eq-rect-Type3-r = λ (?41v ?36v : Level) -> λ (Av : Set ?41v) -> λ (av : Av) -> λ (Pv : (xv : Av) -> (X--v : eq ?41v Av xv av) -> Set ?36v) -> λ (Hv : Pv av (refl ?41v Av av)) -> λ (xv : Av) -> λ (pv : eq ?41v Av xv av) -> match-eq ?41v Av xv ((lsuc lzero) ⊔ (?41v ⊔ (lsuc ?36v))) (λ (X--v : Av) -> λ (X-0v : eq ?41v Av xv X--v) -> (fv : (x0v : Av) -> (X--1v : eq ?41v Av x0v X--v) -> Set ?36v) -> (X--1v : fv X--v (refl ?41v Av X--v)) -> fv xv X-0v) (λ (fv : (x0v : Av) -> (X--v : eq ?41v Av x0v xv) -> Set ?36v) -> λ (autov : fv xv (refl ?41v Av xv)) -> autov) av pv Pv Hv

rewrite-l : (?12v ?9v : Level) -> (Av : Set ?12v) -> (xv : Av) -> (Pv : (X--v : Av) -> Set ?9v) -> (X--v : Pv xv) -> (yv : Av) -> (X--1v : eq ?12v Av xv yv) -> Pv yv
rewrite-l = λ (?12v ?9v : Level) -> λ (Av : Set ?12v) -> λ (xv : Av) -> λ (Pv : (X--v : Av) -> Set ?9v) -> λ (Hxv : Pv xv) -> λ (yv : Av) -> λ (Heqv : eq ?12v Av xv yv) -> match-eq ?12v Av xv ?9v (λ (X--v : Av) -> λ (X-0v : eq ?12v Av xv X--v) -> Pv X--v) Hxv yv Heqv

sym-eq : (?14v : Level) -> (Av : Set ?14v) -> (xv : Av) -> (yv : Av) -> (X--v : eq ?14v Av xv yv) -> eq ?14v Av yv xv
sym-eq = λ (?14v : Level) -> λ (Av : Set ?14v) -> λ (xv : Av) -> λ (yv : Av) -> λ (Heqv : eq ?14v Av xv yv) -> rewrite-l ?14v ?14v Av xv (λ (X--v : Av) -> eq ?14v Av X--v xv) (refl ?14v Av xv) yv (rewrite-l ?14v ?14v Av xv (λ (X--v : Av) -> eq ?14v Av xv X--v) (refl ?14v Av xv) yv Heqv)

rewrite-r : (?13v ?10v : Level) -> (Av : Set ?13v) -> (xv : Av) -> (Pv : (X--v : Av) -> Set ?10v) -> (X--v : Pv xv) -> (yv : Av) -> (X--1v : eq ?13v Av yv xv) -> Pv yv
rewrite-r = λ (?13v ?10v : Level) -> λ (Av : Set ?13v) -> λ (xv : Av) -> λ (Pv : (X--v : Av) -> Set ?10v) -> λ (Hxv : Pv xv) -> λ (yv : Av) -> λ (Heqv : eq ?13v Av yv xv) -> match-eq ?13v Av xv ?10v (λ (X--v : Av) -> λ (X-0v : eq ?13v Av xv X--v) -> Pv X--v) Hxv yv (sym-eq ?13v Av yv xv Heqv)

eq-coerc : (?12v : Level) -> (Av : Set ?12v) -> (Bv : Set ?12v) -> (X--v : Av) -> (X--1v : eq ((lsuc lzero) ⊔ (lsuc ?12v)) (Set ?12v) Av Bv) -> Bv
eq-coerc = λ (?12v : Level) -> λ (Av : Set ?12v) -> λ (Bv : Set ?12v) -> λ (Hav : Av) -> λ (Heqv : eq ((lsuc lzero) ⊔ (lsuc ?12v)) (Set ?12v) Av Bv) -> eq-rect-Type0 ((lsuc lzero) ⊔ (lsuc ?12v)) ?12v (Set ?12v) Av (λ (x-19v : Set ?12v) -> λ (X-x-20v : eq ((lsuc lzero) ⊔ (lsuc ?12v)) (Set ?12v) Av x-19v) -> x-19v) Hav Bv Heqv

trans-eq : (?26v : Level) -> (Av : Set ?26v) -> (xv : Av) -> (yv : Av) -> (zv : Av) -> (X--v : eq ?26v Av xv yv) -> (X--1v : eq ?26v Av yv zv) -> eq ?26v Av xv zv
trans-eq = λ (?26v : Level) -> λ (Av : Set ?26v) -> λ (xv : Av) -> λ (yv : Av) -> λ (zv : Av) -> λ (H1v : eq ?26v Av xv yv) -> λ (H2v : eq ?26v Av yv zv) -> eq-ind-r ?26v ?26v Av yv (λ (x0v : Av) -> λ (X--v : eq ?26v Av x0v yv) -> eq ?26v Av x0v zv) (rewrite-l ?26v ?26v Av xv (λ (X--v : Av) -> eq ?26v Av X--v zv) (rewrite-l ?26v ?26v Av xv (λ (X--v : Av) -> eq ?26v Av xv X--v) (refl ?26v Av xv) zv (rewrite-r ?26v ?26v Av yv (λ (X--v : Av) -> eq ?26v Av X--v zv) H2v xv H1v)) yv H1v) xv H1v

eq-f : (?22v ?21v : Level) -> (Av : Set ?22v) -> (Bv : Set ?21v) -> (fv : (X--v : Av) -> Bv) -> (xv : Av) -> (yv : Av) -> (X--v : eq ?22v Av xv yv) -> eq ?21v Bv (fv xv) (fv yv)
eq-f = λ (?22v ?21v : Level) -> λ (Av : Set ?22v) -> λ (Bv : Set ?21v) -> λ (fv : (X--v : Av) -> Bv) -> λ (xv : Av) -> λ (yv : Av) -> λ (Hv : eq ?22v Av xv yv) -> eq-ind-r ?22v ?21v Av yv (λ (x0v : Av) -> λ (X--v : eq ?22v Av x0v yv) -> eq ?21v Bv (fv x0v) (fv yv)) (rewrite-l ?22v ?21v Av xv (λ (X--v : Av) -> eq ?21v Bv (fv X--v) (fv yv)) (rewrite-l ?22v ?21v Av xv (λ (X--v : Av) -> eq ?21v Bv (fv xv) (fv X--v)) (refl ?21v Bv (fv xv)) yv Hv) yv Hv) xv Hv

eq-f2 : (?42v ?41v ?40v : Level) -> (Av : Set ?42v) -> (Bv : Set ?41v) -> (Cv : Set ?40v) -> (fv : (X--v : Av) -> (X--1v : Bv) -> Cv) -> (x1v : Av) -> (x2v : Av) -> (y1v : Bv) -> (y2v : Bv) -> (X--v : eq ?42v Av x1v x2v) -> (X--1v : eq ?41v Bv y1v y2v) -> eq ?40v Cv (fv x1v y1v) (fv x2v y2v)
eq-f2 = λ (?42v ?41v ?40v : Level) -> λ (Av : Set ?42v) -> λ (Bv : Set ?41v) -> λ (Cv : Set ?40v) -> λ (fv : (X--v : Av) -> (X--1v : Bv) -> Cv) -> λ (x1v : Av) -> λ (x2v : Av) -> λ (y1v : Bv) -> λ (y2v : Bv) -> λ (E1v : eq ?42v Av x1v x2v) -> λ (E2v : eq ?41v Bv y1v y2v) -> eq-ind-r ?42v ?40v Av x2v (λ (xv : Av) -> λ (X--v : eq ?42v Av xv x2v) -> eq ?40v Cv (fv xv y1v) (fv x2v y2v)) (eq-ind-r ?41v ?40v Bv y2v (λ (xv : Bv) -> λ (X--v : eq ?41v Bv xv y2v) -> eq ?40v Cv (fv x2v xv) (fv x2v y2v)) (rewrite-l ?42v ?40v Av x1v (λ (X--v : Av) -> eq ?40v Cv (fv X--v y2v) (fv x2v y2v)) (rewrite-l ?41v ?40v Bv y1v (λ (X--v : Bv) -> eq ?40v Cv (fv x1v X--v) (fv x2v y2v)) (rewrite-l ?42v ?40v Av x1v (λ (X--v : Av) -> eq ?40v Cv (fv x1v y1v) (fv X--v y2v)) (rewrite-l ?41v ?40v Bv y1v (λ (X--v : Bv) -> eq ?40v Cv (fv x1v y1v) (fv x1v X--v)) (refl ?40v Cv (fv x1v y1v)) y2v E2v) x2v E1v) y2v E2v) x2v E1v) y1v E2v) x1v E1v

eq-f3 : (?62v ?61v ?60v ?59v : Level) -> (Av : Set ?62v) -> (Bv : Set ?61v) -> (Cv : Set ?60v) -> (Dv : Set ?59v) -> (fv : (X--v : Av) -> (X--1v : Bv) -> (X--2v : Cv) -> Dv) -> (x1v : Av) -> (x2v : Av) -> (y1v : Bv) -> (y2v : Bv) -> (z1v : Cv) -> (z2v : Cv) -> (X--v : eq ?62v Av x1v x2v) -> (X--1v : eq ?61v Bv y1v y2v) -> (X--2v : eq ?60v Cv z1v z2v) -> eq ?59v Dv (fv x1v y1v z1v) (fv x2v y2v z2v)
eq-f3 = λ (?62v ?61v ?60v ?59v : Level) -> λ (Av : Set ?62v) -> λ (Bv : Set ?61v) -> λ (Cv : Set ?60v) -> λ (Dv : Set ?59v) -> λ (fv : (X--v : Av) -> (X--1v : Bv) -> (X--2v : Cv) -> Dv) -> λ (x1v : Av) -> λ (x2v : Av) -> λ (y1v : Bv) -> λ (y2v : Bv) -> λ (z1v : Cv) -> λ (z2v : Cv) -> λ (E1v : eq ?62v Av x1v x2v) -> λ (E2v : eq ?61v Bv y1v y2v) -> λ (E3v : eq ?60v Cv z1v z2v) -> eq-ind-r ?62v ?59v Av x2v (λ (xv : Av) -> λ (X--v : eq ?62v Av xv x2v) -> eq ?59v Dv (fv xv y1v z1v) (fv x2v y2v z2v)) (eq-ind-r ?61v ?59v Bv y2v (λ (xv : Bv) -> λ (X--v : eq ?61v Bv xv y2v) -> eq ?59v Dv (fv x2v xv z1v) (fv x2v y2v z2v)) (eq-ind-r ?60v ?59v Cv z2v (λ (xv : Cv) -> λ (X--v : eq ?60v Cv xv z2v) -> eq ?59v Dv (fv x2v y2v xv) (fv x2v y2v z2v)) (rewrite-l ?62v ?59v Av x1v (λ (X--v : Av) -> eq ?59v Dv (fv X--v y2v z2v) (fv x2v y2v z2v)) (rewrite-l ?61v ?59v Bv y1v (λ (X--v : Bv) -> eq ?59v Dv (fv x1v X--v z2v) (fv x2v y2v z2v)) (rewrite-l ?60v ?59v Cv z1v (λ (X--v : Cv) -> eq ?59v Dv (fv x1v y1v X--v) (fv x2v y2v z2v)) (rewrite-l ?62v ?59v Av x1v (λ (X--v : Av) -> eq ?59v Dv (fv x1v y1v z1v) (fv X--v y2v z2v)) (rewrite-l ?61v ?59v Bv y1v (λ (X--v : Bv) -> eq ?59v Dv (fv x1v y1v z1v) (fv x1v X--v z2v)) (rewrite-l ?60v ?59v Cv z1v (λ (X--v : Cv) -> eq ?59v Dv (fv x1v y1v z1v) (fv x1v y1v X--v)) (refl ?59v Dv (fv x1v y1v z1v)) z2v E3v) y2v E2v) x2v E1v) z2v E3v) y2v E2v) x2v E1v) z1v E3v) y1v E2v) x1v E1v

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


True-inv-ind : (?23v ?19v : Level) -> (Htermv : True ?23v) -> (Pv : (X-z125v : True ?23v) -> Set ?19v) -> (X-H1v : (X-z126v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> Pv Htermv
True-inv-ind = λ (?23v ?19v : Level) -> λ (Htermv : True ?23v) -> λ (Pv : (X-z125v : True ?23v) -> Set ?19v) -> λ (H1v : (X-z126v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> True-ind ?23v (?23v ⊔ ?19v) (λ (X-x-40v : True ?23v) -> (X-z126v : eq ?23v (True ?23v) Htermv X-x-40v) -> Pv X-x-40v) H1v Htermv (refl ?23v (True ?23v) Htermv)

True-inv-rect-Type4 : (?23v ?19v : Level) -> (Htermv : True ?23v) -> (Pv : (X-z131v : True ?23v) -> Set ?19v) -> (X-H1v : (X-z132v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> Pv Htermv
True-inv-rect-Type4 = λ (?23v ?19v : Level) -> λ (Htermv : True ?23v) -> λ (Pv : (X-z131v : True ?23v) -> Set ?19v) -> λ (H1v : (X-z132v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> True-rect-Type4 ?23v (?23v ⊔ ?19v) (λ (X-x-42v : True ?23v) -> (X-z132v : eq ?23v (True ?23v) Htermv X-x-42v) -> Pv X-x-42v) H1v Htermv (refl ?23v (True ?23v) Htermv)

True-inv-rect-Type3 : (?23v ?19v : Level) -> (Htermv : True ?23v) -> (Pv : (X-z137v : True ?23v) -> Set ?19v) -> (X-H1v : (X-z138v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> Pv Htermv
True-inv-rect-Type3 = λ (?23v ?19v : Level) -> λ (Htermv : True ?23v) -> λ (Pv : (X-z137v : True ?23v) -> Set ?19v) -> λ (H1v : (X-z138v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> True-rect-Type3 ?23v (?23v ⊔ ?19v) (λ (X-x-46v : True ?23v) -> (X-z138v : eq ?23v (True ?23v) Htermv X-x-46v) -> Pv X-x-46v) H1v Htermv (refl ?23v (True ?23v) Htermv)

True-inv-rect-Type2 : (?23v ?19v : Level) -> (Htermv : True ?23v) -> (Pv : (X-z143v : True ?23v) -> Set ?19v) -> (X-H1v : (X-z144v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> Pv Htermv
True-inv-rect-Type2 = λ (?23v ?19v : Level) -> λ (Htermv : True ?23v) -> λ (Pv : (X-z143v : True ?23v) -> Set ?19v) -> λ (H1v : (X-z144v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> True-rect-Type2 ?23v (?23v ⊔ ?19v) (λ (X-x-48v : True ?23v) -> (X-z144v : eq ?23v (True ?23v) Htermv X-x-48v) -> Pv X-x-48v) H1v Htermv (refl ?23v (True ?23v) Htermv)

True-inv-rect-Type1 : (?23v ?19v : Level) -> (Htermv : True ?23v) -> (Pv : (X-z149v : True ?23v) -> Set ?19v) -> (X-H1v : (X-z150v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> Pv Htermv
True-inv-rect-Type1 = λ (?23v ?19v : Level) -> λ (Htermv : True ?23v) -> λ (Pv : (X-z149v : True ?23v) -> Set ?19v) -> λ (H1v : (X-z150v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> True-rect-Type1 ?23v (?23v ⊔ ?19v) (λ (X-x-50v : True ?23v) -> (X-z150v : eq ?23v (True ?23v) Htermv X-x-50v) -> Pv X-x-50v) H1v Htermv (refl ?23v (True ?23v) Htermv)

True-inv-rect-Type0 : (?23v ?19v : Level) -> (Htermv : True ?23v) -> (Pv : (X-z155v : True ?23v) -> Set ?19v) -> (X-H1v : (X-z156v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> Pv Htermv
True-inv-rect-Type0 = λ (?23v ?19v : Level) -> λ (Htermv : True ?23v) -> λ (Pv : (X-z155v : True ?23v) -> Set ?19v) -> λ (H1v : (X-z156v : eq ?23v (True ?23v) Htermv (I ?23v)) -> Pv (I ?23v)) -> True-rect-Type0 ?23v (?23v ⊔ ?19v) (λ (X-x-52v : True ?23v) -> (X-z156v : eq ?23v (True ?23v) Htermv X-x-52v) -> Pv X-x-52v) H1v Htermv (refl ?23v (True ?23v) Htermv)

True-discr : (?58v ?68v : Level) -> (xv : True ?58v) -> (yv : True ?58v) -> (X-ev : eq ?58v (True ?58v) xv yv) -> match-True ?58v ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc ?68v))) (λ (X--v : True ?58v) -> Set ((lsuc lzero) ⊔ (lsuc ?68v))) (match-True ?58v ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc ?68v))) (λ (X--v : True ?58v) -> Set ((lsuc lzero) ⊔ (lsuc ?68v))) ((Pv : Set ?68v) -> (X-z5v : Pv) -> Pv) yv) xv
True-discr = λ (?58v ?68v : Level) -> λ (xv : True ?58v) -> λ (yv : True ?58v) -> λ (Deqv : eq ?58v (True ?58v) xv yv) -> eq-rect-Type2 ?58v ((lsuc lzero) ⊔ (lsuc ?68v)) (True ?58v) xv (λ (x-13v : True ?58v) -> λ (X-x-14v : eq ?58v (True ?58v) xv x-13v) -> match-True ?58v ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc ?68v))) (λ (X--v : True ?58v) -> Set ((lsuc lzero) ⊔ (lsuc ?68v))) (match-True ?58v ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc ?68v))) (λ (X--v : True ?58v) -> Set ((lsuc lzero) ⊔ (lsuc ?68v))) ((Pv : Set ?68v) -> (X-z5v : Pv) -> Pv) x-13v) xv) (match-True ?58v ((lsuc lzero) ⊔ (lsuc ?68v)) (λ (X--v : True ?58v) -> match-True ?58v ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc ?68v))) (λ (X-0v : True ?58v) -> Set ((lsuc lzero) ⊔ (lsuc ?68v))) (match-True ?58v ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc ?68v))) (λ (X-0v : True ?58v) -> Set ((lsuc lzero) ⊔ (lsuc ?68v))) ((Pv : Set ?68v) -> (X-z5v : Pv) -> Pv) X--v) X--v) (λ (Pv : Set ?68v) -> λ (DHv : Pv) -> DHv) xv) yv Deqv

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



Not-inv-ind : (?27v ?22v : Level) -> (x1v : Set ?27v) -> (Htermv : Not ?27v x1v) -> (Pv : (X-z257v : Not ?27v x1v) -> Set ?22v) -> (X-H1v : (x-80v : (X--v : x1v) -> False ?27v) -> (X-z258v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-80v)) -> Pv (nmk ?27v x1v x-80v)) -> Pv Htermv
Not-inv-ind = λ (?27v ?22v : Level) -> λ (x1v : Set ?27v) -> λ (Htermv : Not ?27v x1v) -> λ (Pv : (X-z257v : Not ?27v x1v) -> Set ?22v) -> λ (H1v : (x-80v : (X--v : x1v) -> False ?27v) -> (X-z258v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-80v)) -> Pv (nmk ?27v x1v x-80v)) -> Not-ind ?27v (?27v ⊔ ?22v) x1v (λ (X-x-79v : Not ?27v x1v) -> (X-z258v : eq ?27v (Not ?27v x1v) Htermv X-x-79v) -> Pv X-x-79v) H1v Htermv (refl ?27v (Not ?27v x1v) Htermv)

Not-inv-rect-Type4 : (?27v ?22v : Level) -> (x1v : Set ?27v) -> (Htermv : Not ?27v x1v) -> (Pv : (X-z263v : Not ?27v x1v) -> Set ?22v) -> (X-H1v : (x-83v : (X--v : x1v) -> False ?27v) -> (X-z264v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-83v)) -> Pv (nmk ?27v x1v x-83v)) -> Pv Htermv
Not-inv-rect-Type4 = λ (?27v ?22v : Level) -> λ (x1v : Set ?27v) -> λ (Htermv : Not ?27v x1v) -> λ (Pv : (X-z263v : Not ?27v x1v) -> Set ?22v) -> λ (H1v : (x-83v : (X--v : x1v) -> False ?27v) -> (X-z264v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-83v)) -> Pv (nmk ?27v x1v x-83v)) -> Not-rect-Type4 ?27v (?27v ⊔ ?22v) x1v (λ (X-x-82v : Not ?27v x1v) -> (X-z264v : eq ?27v (Not ?27v x1v) Htermv X-x-82v) -> Pv X-x-82v) H1v Htermv (refl ?27v (Not ?27v x1v) Htermv)

Not-inv-rect-Type3 : (?27v ?22v : Level) -> (x1v : Set ?27v) -> (Htermv : Not ?27v x1v) -> (Pv : (X-z269v : Not ?27v x1v) -> Set ?22v) -> (X-H1v : (x-89v : (X--v : x1v) -> False ?27v) -> (X-z270v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-89v)) -> Pv (nmk ?27v x1v x-89v)) -> Pv Htermv
Not-inv-rect-Type3 = λ (?27v ?22v : Level) -> λ (x1v : Set ?27v) -> λ (Htermv : Not ?27v x1v) -> λ (Pv : (X-z269v : Not ?27v x1v) -> Set ?22v) -> λ (H1v : (x-89v : (X--v : x1v) -> False ?27v) -> (X-z270v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-89v)) -> Pv (nmk ?27v x1v x-89v)) -> Not-rect-Type3 ?27v (?27v ⊔ ?22v) x1v (λ (X-x-88v : Not ?27v x1v) -> (X-z270v : eq ?27v (Not ?27v x1v) Htermv X-x-88v) -> Pv X-x-88v) H1v Htermv (refl ?27v (Not ?27v x1v) Htermv)

Not-inv-rect-Type2 : (?27v ?22v : Level) -> (x1v : Set ?27v) -> (Htermv : Not ?27v x1v) -> (Pv : (X-z275v : Not ?27v x1v) -> Set ?22v) -> (X-H1v : (x-92v : (X--v : x1v) -> False ?27v) -> (X-z276v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-92v)) -> Pv (nmk ?27v x1v x-92v)) -> Pv Htermv
Not-inv-rect-Type2 = λ (?27v ?22v : Level) -> λ (x1v : Set ?27v) -> λ (Htermv : Not ?27v x1v) -> λ (Pv : (X-z275v : Not ?27v x1v) -> Set ?22v) -> λ (H1v : (x-92v : (X--v : x1v) -> False ?27v) -> (X-z276v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-92v)) -> Pv (nmk ?27v x1v x-92v)) -> Not-rect-Type2 ?27v (?27v ⊔ ?22v) x1v (λ (X-x-91v : Not ?27v x1v) -> (X-z276v : eq ?27v (Not ?27v x1v) Htermv X-x-91v) -> Pv X-x-91v) H1v Htermv (refl ?27v (Not ?27v x1v) Htermv)

Not-inv-rect-Type1 : (?27v ?22v : Level) -> (x1v : Set ?27v) -> (Htermv : Not ?27v x1v) -> (Pv : (X-z281v : Not ?27v x1v) -> Set ?22v) -> (X-H1v : (x-95v : (X--v : x1v) -> False ?27v) -> (X-z282v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-95v)) -> Pv (nmk ?27v x1v x-95v)) -> Pv Htermv
Not-inv-rect-Type1 = λ (?27v ?22v : Level) -> λ (x1v : Set ?27v) -> λ (Htermv : Not ?27v x1v) -> λ (Pv : (X-z281v : Not ?27v x1v) -> Set ?22v) -> λ (H1v : (x-95v : (X--v : x1v) -> False ?27v) -> (X-z282v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-95v)) -> Pv (nmk ?27v x1v x-95v)) -> Not-rect-Type1 ?27v (?27v ⊔ ?22v) x1v (λ (X-x-94v : Not ?27v x1v) -> (X-z282v : eq ?27v (Not ?27v x1v) Htermv X-x-94v) -> Pv X-x-94v) H1v Htermv (refl ?27v (Not ?27v x1v) Htermv)

Not-inv-rect-Type0 : (?27v ?22v : Level) -> (x1v : Set ?27v) -> (Htermv : Not ?27v x1v) -> (Pv : (X-z287v : Not ?27v x1v) -> Set ?22v) -> (X-H1v : (x-98v : (X--v : x1v) -> False ?27v) -> (X-z288v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-98v)) -> Pv (nmk ?27v x1v x-98v)) -> Pv Htermv
Not-inv-rect-Type0 = λ (?27v ?22v : Level) -> λ (x1v : Set ?27v) -> λ (Htermv : Not ?27v x1v) -> λ (Pv : (X-z287v : Not ?27v x1v) -> Set ?22v) -> λ (H1v : (x-98v : (X--v : x1v) -> False ?27v) -> (X-z288v : eq ?27v (Not ?27v x1v) Htermv (nmk ?27v x1v x-98v)) -> Pv (nmk ?27v x1v x-98v)) -> Not-rect-Type0 ?27v (?27v ⊔ ?22v) x1v (λ (X-x-97v : Not ?27v x1v) -> (X-z288v : eq ?27v (Not ?27v x1v) Htermv X-x-97v) -> Pv X-x-97v) H1v Htermv (refl ?27v (Not ?27v x1v) Htermv)

absurd : (?11v : Level) -> (Av : Set ?11v) -> (X--v : Av) -> (X--1v : Not ?11v Av) -> False ?11v
absurd = λ (?11v : Level) -> λ (Av : Set ?11v) -> λ (Hv : Av) -> λ (Hnv : Not ?11v Av) -> Not-ind ?11v ?11v Av (λ (X-x-79v : Not ?11v Av) -> False ?11v) (λ (X-x-80v : (X--v : Av) -> False ?11v) -> X-x-80v Hv) Hnv

not-to-not : (?8v : Level) -> (Av : Set ?8v) -> (Bv : Set ?8v) -> (X--v : (X--v : Av) -> Bv) -> (X--1v : Not ?8v Bv) -> Not ?8v Av
not-to-not = λ (?8v : Level) -> λ (Av : Set ?8v) -> λ (Bv : Set ?8v) -> λ (autov : (X--v : Av) -> Bv) -> λ (auto'v : Not ?8v Bv) -> nmk ?8v Av (λ (auto''v : Av) -> absurd ?8v Bv (autov auto''v) auto'v)

sym-not-eq : (?16v : Level) -> (Av : Set ?16v) -> (xv : Av) -> (yv : Av) -> (X--v : Not ?16v (eq ?16v Av xv yv)) -> Not ?16v (eq ?16v Av yv xv)
sym-not-eq = λ (?16v : Level) -> λ (Av : Set ?16v) -> λ (xv : Av) -> λ (yv : Av) -> λ (autov : Not ?16v (eq ?16v Av xv yv)) -> nmk ?16v (eq ?16v Av yv xv) (λ (auto'v : eq ?16v Av yv xv) -> absurd ?16v (eq ?16v Av xv yv) (rewrite-r ?16v ?16v Av xv (λ (X--v : Av) -> eq ?16v Av xv X--v) (refl ?16v Av xv) yv auto'v) autov)


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


And-inv-ind : (?37v ?36v ?29v : Level) -> (x1v : Set ?37v) -> (x2v : Set ?36v) -> (Htermv : And ?37v ?36v x1v x2v) -> (Pv : (X-z323v : And ?37v ?36v x1v x2v) -> Set ?29v) -> (X-H1v : (x-120v : x1v) -> (x-119v : x2v) -> (X-z324v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-120v x-119v)) -> Pv (conj ?37v ?36v x1v x2v x-120v x-119v)) -> Pv Htermv
And-inv-ind = λ (?37v ?36v ?29v : Level) -> λ (x1v : Set ?37v) -> λ (x2v : Set ?36v) -> λ (Htermv : And ?37v ?36v x1v x2v) -> λ (Pv : (X-z323v : And ?37v ?36v x1v x2v) -> Set ?29v) -> λ (H1v : (x-120v : x1v) -> (x-119v : x2v) -> (X-z324v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-120v x-119v)) -> Pv (conj ?37v ?36v x1v x2v x-120v x-119v)) -> And-ind ?37v ?36v ((?37v ⊔ ?36v) ⊔ ?29v) x1v x2v (λ (X-x-118v : And ?37v ?36v x1v x2v) -> (X-z324v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv X-x-118v) -> Pv X-x-118v) H1v Htermv (refl (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv)

And-inv-rect-Type4 : (?37v ?36v ?29v : Level) -> (x1v : Set ?37v) -> (x2v : Set ?36v) -> (Htermv : And ?37v ?36v x1v x2v) -> (Pv : (X-z329v : And ?37v ?36v x1v x2v) -> Set ?29v) -> (X-H1v : (x-124v : x1v) -> (x-123v : x2v) -> (X-z330v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-124v x-123v)) -> Pv (conj ?37v ?36v x1v x2v x-124v x-123v)) -> Pv Htermv
And-inv-rect-Type4 = λ (?37v ?36v ?29v : Level) -> λ (x1v : Set ?37v) -> λ (x2v : Set ?36v) -> λ (Htermv : And ?37v ?36v x1v x2v) -> λ (Pv : (X-z329v : And ?37v ?36v x1v x2v) -> Set ?29v) -> λ (H1v : (x-124v : x1v) -> (x-123v : x2v) -> (X-z330v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-124v x-123v)) -> Pv (conj ?37v ?36v x1v x2v x-124v x-123v)) -> And-rect-Type4 ?37v ?36v ((?37v ⊔ ?36v) ⊔ ?29v) x1v x2v (λ (X-x-122v : And ?37v ?36v x1v x2v) -> (X-z330v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv X-x-122v) -> Pv X-x-122v) H1v Htermv (refl (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv)

And-inv-rect-Type3 : (?37v ?36v ?29v : Level) -> (x1v : Set ?37v) -> (x2v : Set ?36v) -> (Htermv : And ?37v ?36v x1v x2v) -> (Pv : (X-z335v : And ?37v ?36v x1v x2v) -> Set ?29v) -> (X-H1v : (x-132v : x1v) -> (x-131v : x2v) -> (X-z336v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-132v x-131v)) -> Pv (conj ?37v ?36v x1v x2v x-132v x-131v)) -> Pv Htermv
And-inv-rect-Type3 = λ (?37v ?36v ?29v : Level) -> λ (x1v : Set ?37v) -> λ (x2v : Set ?36v) -> λ (Htermv : And ?37v ?36v x1v x2v) -> λ (Pv : (X-z335v : And ?37v ?36v x1v x2v) -> Set ?29v) -> λ (H1v : (x-132v : x1v) -> (x-131v : x2v) -> (X-z336v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-132v x-131v)) -> Pv (conj ?37v ?36v x1v x2v x-132v x-131v)) -> And-rect-Type3 ?37v ?36v ((?37v ⊔ ?36v) ⊔ ?29v) x1v x2v (λ (X-x-130v : And ?37v ?36v x1v x2v) -> (X-z336v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv X-x-130v) -> Pv X-x-130v) H1v Htermv (refl (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv)

And-inv-rect-Type2 : (?37v ?36v ?29v : Level) -> (x1v : Set ?37v) -> (x2v : Set ?36v) -> (Htermv : And ?37v ?36v x1v x2v) -> (Pv : (X-z341v : And ?37v ?36v x1v x2v) -> Set ?29v) -> (X-H1v : (x-136v : x1v) -> (x-135v : x2v) -> (X-z342v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-136v x-135v)) -> Pv (conj ?37v ?36v x1v x2v x-136v x-135v)) -> Pv Htermv
And-inv-rect-Type2 = λ (?37v ?36v ?29v : Level) -> λ (x1v : Set ?37v) -> λ (x2v : Set ?36v) -> λ (Htermv : And ?37v ?36v x1v x2v) -> λ (Pv : (X-z341v : And ?37v ?36v x1v x2v) -> Set ?29v) -> λ (H1v : (x-136v : x1v) -> (x-135v : x2v) -> (X-z342v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-136v x-135v)) -> Pv (conj ?37v ?36v x1v x2v x-136v x-135v)) -> And-rect-Type2 ?37v ?36v ((?37v ⊔ ?36v) ⊔ ?29v) x1v x2v (λ (X-x-134v : And ?37v ?36v x1v x2v) -> (X-z342v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv X-x-134v) -> Pv X-x-134v) H1v Htermv (refl (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv)

And-inv-rect-Type1 : (?37v ?36v ?29v : Level) -> (x1v : Set ?37v) -> (x2v : Set ?36v) -> (Htermv : And ?37v ?36v x1v x2v) -> (Pv : (X-z347v : And ?37v ?36v x1v x2v) -> Set ?29v) -> (X-H1v : (x-140v : x1v) -> (x-139v : x2v) -> (X-z348v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-140v x-139v)) -> Pv (conj ?37v ?36v x1v x2v x-140v x-139v)) -> Pv Htermv
And-inv-rect-Type1 = λ (?37v ?36v ?29v : Level) -> λ (x1v : Set ?37v) -> λ (x2v : Set ?36v) -> λ (Htermv : And ?37v ?36v x1v x2v) -> λ (Pv : (X-z347v : And ?37v ?36v x1v x2v) -> Set ?29v) -> λ (H1v : (x-140v : x1v) -> (x-139v : x2v) -> (X-z348v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-140v x-139v)) -> Pv (conj ?37v ?36v x1v x2v x-140v x-139v)) -> And-rect-Type1 ?37v ?36v ((?37v ⊔ ?36v) ⊔ ?29v) x1v x2v (λ (X-x-138v : And ?37v ?36v x1v x2v) -> (X-z348v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv X-x-138v) -> Pv X-x-138v) H1v Htermv (refl (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv)

And-inv-rect-Type0 : (?37v ?36v ?29v : Level) -> (x1v : Set ?37v) -> (x2v : Set ?36v) -> (Htermv : And ?37v ?36v x1v x2v) -> (Pv : (X-z353v : And ?37v ?36v x1v x2v) -> Set ?29v) -> (X-H1v : (x-144v : x1v) -> (x-143v : x2v) -> (X-z354v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-144v x-143v)) -> Pv (conj ?37v ?36v x1v x2v x-144v x-143v)) -> Pv Htermv
And-inv-rect-Type0 = λ (?37v ?36v ?29v : Level) -> λ (x1v : Set ?37v) -> λ (x2v : Set ?36v) -> λ (Htermv : And ?37v ?36v x1v x2v) -> λ (Pv : (X-z353v : And ?37v ?36v x1v x2v) -> Set ?29v) -> λ (H1v : (x-144v : x1v) -> (x-143v : x2v) -> (X-z354v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv (conj ?37v ?36v x1v x2v x-144v x-143v)) -> Pv (conj ?37v ?36v x1v x2v x-144v x-143v)) -> And-rect-Type0 ?37v ?36v ((?37v ⊔ ?36v) ⊔ ?29v) x1v x2v (λ (X-x-142v : And ?37v ?36v x1v x2v) -> (X-z354v : eq (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv X-x-142v) -> Pv X-x-142v) H1v Htermv (refl (?37v ⊔ ?36v) (And ?37v ?36v x1v x2v) Htermv)

proj1 : (?12v ?11v : Level) -> (Av : Set ?12v) -> (Bv : Set ?11v) -> (X--v : And ?12v ?11v Av Bv) -> Av
proj1 = λ (?12v ?11v : Level) -> λ (Av : Set ?12v) -> λ (Bv : Set ?11v) -> λ (ABv : And ?12v ?11v Av Bv) -> And-ind ?12v ?11v ?12v Av Bv (λ (X-x-118v : And ?12v ?11v Av Bv) -> Av) (λ (X-x-120v : Av) -> λ (X-x-119v : Bv) -> X-x-120v) ABv

proj2 : (?12v ?11v : Level) -> (Av : Set ?12v) -> (Bv : Set ?11v) -> (X--v : And ?12v ?11v Av Bv) -> Bv
proj2 = λ (?12v ?11v : Level) -> λ (Av : Set ?12v) -> λ (Bv : Set ?11v) -> λ (ABv : And ?12v ?11v Av Bv) -> And-ind ?12v ?11v ?11v Av Bv (λ (X-x-118v : And ?12v ?11v Av Bv) -> Bv) (λ (X-x-120v : Av) -> λ (X-x-119v : Bv) -> X-x-119v) ABv

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

Or-inv-ind : (?46v ?45v ?38v : Level) -> (x1v : Set ?46v) -> (x2v : Set ?45v) -> (Htermv : Or ?46v ?45v x1v x2v) -> (Pv : (X-z389v : Or ?46v ?45v x1v x2v) -> Set ?38v) -> (X-H1v : (x-171v : x1v) -> (X-z390v : eq (?46v ⊔ ?45v) (Or ?46v ?45v x1v x2v) Htermv (or-introl ?46v ?45v x1v x2v x-171v)) -> Pv (or-introl ?46v ?45v x1v x2v x-171v)) -> (X-H2v : (x-172v : x2v) -> (X-z390v : eq (?46v ⊔ ?45v) (Or ?46v ?45v x1v x2v) Htermv (or-intror ?46v ?45v x1v x2v x-172v)) -> Pv (or-intror ?46v ?45v x1v x2v x-172v)) -> Pv Htermv
Or-inv-ind = λ (?46v ?45v ?38v : Level) -> λ (x1v : Set ?46v) -> λ (x2v : Set ?45v) -> λ (Htermv : Or ?46v ?45v x1v x2v) -> λ (Pv : (X-z389v : Or ?46v ?45v x1v x2v) -> Set ?38v) -> λ (H1v : (x-171v : x1v) -> (X-z390v : eq (?46v ⊔ ?45v) (Or ?46v ?45v x1v x2v) Htermv (or-introl ?46v ?45v x1v x2v x-171v)) -> Pv (or-introl ?46v ?45v x1v x2v x-171v)) -> λ (H2v : (x-172v : x2v) -> (X-z390v : eq (?46v ⊔ ?45v) (Or ?46v ?45v x1v x2v) Htermv (or-intror ?46v ?45v x1v x2v x-172v)) -> Pv (or-intror ?46v ?45v x1v x2v x-172v)) -> Or-ind ?46v ?45v ((?46v ⊔ ?45v) ⊔ ?38v) x1v x2v (λ (X-x-170v : Or ?46v ?45v x1v x2v) -> (X-z390v : eq (?46v ⊔ ?45v) (Or ?46v ?45v x1v x2v) Htermv X-x-170v) -> Pv X-x-170v) H1v H2v Htermv (refl (?46v ⊔ ?45v) (Or ?46v ?45v x1v x2v) Htermv)

decidable : (?3v : Level) -> (X--v : Set ?3v) -> Set ?3v
decidable = λ (?3v : Level) -> λ (Av : Set ?3v) -> Or ?3v ?3v Av (Not ?3v Av)

data ex (?2v ?1v : Level)  (Av : Set ?2v)  (X-Pv : (X--v : Av) -> Set ?1v) : Set (lzero ⊔ (?2v ⊔ ?1v)) where
  ex-intro' : (x : Av) -> (px : X-Pv x) -> ex ?2v ?1v Av X-Pv

ex-intro : (?1v ?3v : Level) -> (Av : Set ?1v) -> (Pv : (X--v : Av) -> Set ?3v) -> (xv : Av) -> (X--v : Pv xv) -> ex ?1v ?3v Av Pv
ex-intro _ _ _ _ = ex-intro'

match-ex : (?8v ?7v : Level) -> (Av : Set ?8v) -> (X-Pv : (X--v : Av) -> Set ?7v) -> (return-sortv : Level) -> (return-typev : (zv : ex ?8v ?7v Av X-Pv) -> Set return-sortv) -> (case-ex-introv : (xv : Av) -> (X--v : X-Pv xv) -> return-typev (ex-intro ?8v ?7v Av X-Pv xv X--v)) -> (zv : ex ?8v ?7v Av X-Pv) -> return-typev zv
match-ex _ _ _ _ _ _ case-ex-intro (ex-intro' x px) = case-ex-intro x px

ex-ind : (?11v ?10v ?6v : Level) -> (Av : Set ?11v) -> (X-Pv : (X--v : Av) -> Set ?10v) -> (Q-v : (X-x-235v : ex ?11v ?10v Av X-Pv) -> Set ?6v) -> (X-H-ex-introv : (xv : Av) -> (x-236v : X-Pv xv) -> Q-v (ex-intro ?11v ?10v Av X-Pv xv x-236v)) -> (x-235v : ex ?11v ?10v Av X-Pv) -> Q-v x-235v
ex-ind _ _ _ _ _ _ case-ex-intro (ex-intro' x px) = case-ex-intro x px


ex-inv-ind : (?38v ?36v ?29v : Level) -> (x1v : Set ?38v) -> (x2v : (X--v : x1v) -> Set ?36v) -> (Htermv : ex ?38v ?36v x1v x2v) -> (Pv : (X-z455v : ex ?38v ?36v x1v x2v) -> Set ?29v) -> (X-H1v : (xv : x1v) -> (x-236v : x2v xv) -> (X-z456v : eq (?38v ⊔ ?36v) (ex ?38v ?36v x1v x2v) Htermv (ex-intro ?38v ?36v x1v x2v xv x-236v)) -> Pv (ex-intro ?38v ?36v x1v x2v xv x-236v)) -> Pv Htermv
ex-inv-ind = λ (?38v ?36v ?29v : Level) -> λ (x1v : Set ?38v) -> λ (x2v : (X--v : x1v) -> Set ?36v) -> λ (Htermv : ex ?38v ?36v x1v x2v) -> λ (Pv : (X-z455v : ex ?38v ?36v x1v x2v) -> Set ?29v) -> λ (H1v : (xv : x1v) -> (x-236v : x2v xv) -> (X-z456v : eq (?38v ⊔ ?36v) (ex ?38v ?36v x1v x2v) Htermv (ex-intro ?38v ?36v x1v x2v xv x-236v)) -> Pv (ex-intro ?38v ?36v x1v x2v xv x-236v)) -> ex-ind ?38v ?36v ((?38v ⊔ ?36v) ⊔ ?29v) x1v x2v (λ (X-x-235v : ex ?38v ?36v x1v x2v) -> (X-z456v : eq (?38v ⊔ ?36v) (ex ?38v ?36v x1v x2v) Htermv X-x-235v) -> Pv X-x-235v) H1v Htermv (refl (?38v ⊔ ?36v) (ex ?38v ?36v x1v x2v) Htermv)

data ex2 (?4v ?3v ?1v : Level)  (Av : Set ?4v)  (X-Pv : (X--v : Av) -> Set ?3v)  (X-Qv : (X--v : Av) -> Set ?1v) : Set (lzero ⊔ ((?4v ⊔ ?3v) ⊔ ?1v)) where
  ex2-intro' : (x : Av) -> (xP : X-Pv x) -> (xQ : X-Qv x) -> ex2 ?4v ?3v ?1v Av X-Pv X-Qv

ex2-intro : (?2v ?5v ?4v : Level) -> (Av : Set ?2v) -> (Pv : (X--v : Av) -> Set ?5v) -> (Qv : (X--v : Av) -> Set ?4v) -> (xv : Av) -> (X--v : Pv xv) -> (X--1v : Qv xv) -> ex2 ?2v ?5v ?4v Av Pv Qv
ex2-intro _ _ _ _ _ _ = ex2-intro'

match-ex2 : (?12v ?10v ?11v : Level) -> (Av : Set ?12v) -> (X-Pv : (X--v : Av) -> Set ?10v) -> (X-Qv : (X--v : Av) -> Set ?11v) -> (return-sortv : Level) -> (return-typev : (zv : ex2 ?12v ?10v ?11v Av X-Pv X-Qv) -> Set return-sortv) -> (case-ex2-introv : (xv : Av) -> (X--v : X-Pv xv) -> (X--1v : X-Qv xv) -> return-typev (ex2-intro ?12v ?10v ?11v Av X-Pv X-Qv xv X--v X--1v)) -> (zv : ex2 ?12v ?10v ?11v Av X-Pv X-Qv) -> return-typev zv
match-ex2 _ _ _ _ _ _ _ _ case-ex2-intro (ex2-intro' x xp xq) = case-ex2-intro x xp xq

ex2-ind : (?15v ?13v ?14v ?8v : Level) -> (Av : Set ?15v) -> (X-Pv : (X--v : Av) -> Set ?13v) -> (X-Qv : (X--v : Av) -> Set ?14v) -> (Q-v : (X-x-274v : ex2 ?15v ?13v ?14v Av X-Pv X-Qv) -> Set ?8v) -> (X-H-ex2-introv : (xv : Av) -> (x-276v : X-Pv xv) -> (x-275v : X-Qv xv) -> Q-v (ex2-intro ?15v ?13v ?14v Av X-Pv X-Qv xv x-276v x-275v)) -> (x-274v : ex2 ?15v ?13v ?14v Av X-Pv X-Qv) -> Q-v x-274v
ex2-ind _ _ _ _ _ _ _ _ case-ex2-intro (ex2-intro' x xp xq) = case-ex2-intro x xp xq


ex2-inv-ind : (?51v ?49v ?47v ?38v : Level) -> (x1v : Set ?51v) -> (x2v : (X--v : x1v) -> Set ?49v) -> (x3v : (X--v : x1v) -> Set ?47v) -> (Htermv : ex2 ?51v ?49v ?47v x1v x2v x3v) -> (Pv : (X-z521v : ex2 ?51v ?49v ?47v x1v x2v x3v) -> Set ?38v) -> (X-H1v : (xv : x1v) -> (x-276v : x2v xv) -> (x-275v : x3v xv) -> (X-z522v : eq ((?47v ⊔ ?49v) ⊔ ?51v) (ex2 ?51v ?49v ?47v x1v x2v x3v) Htermv (ex2-intro ?51v ?49v ?47v x1v x2v x3v xv x-276v x-275v)) -> Pv (ex2-intro ?51v ?49v ?47v x1v x2v x3v xv x-276v x-275v)) -> Pv Htermv
ex2-inv-ind = λ (?51v ?49v ?47v ?38v : Level) -> λ (x1v : Set ?51v) -> λ (x2v : (X--v : x1v) -> Set ?49v) -> λ (x3v : (X--v : x1v) -> Set ?47v) -> λ (Htermv : ex2 ?51v ?49v ?47v x1v x2v x3v) -> λ (Pv : (X-z521v : ex2 ?51v ?49v ?47v x1v x2v x3v) -> Set ?38v) -> λ (H1v : (xv : x1v) -> (x-276v : x2v xv) -> (x-275v : x3v xv) -> (X-z522v : eq ((?47v ⊔ ?49v) ⊔ ?51v) (ex2 ?51v ?49v ?47v x1v x2v x3v) Htermv (ex2-intro ?51v ?49v ?47v x1v x2v x3v xv x-276v x-275v)) -> Pv (ex2-intro ?51v ?49v ?47v x1v x2v x3v xv x-276v x-275v)) -> ex2-ind ?51v ?49v ?47v (((?47v ⊔ ?51v) ⊔ ?38v) ⊔ ?49v) x1v x2v x3v (λ (X-x-274v : ex2 ?51v ?49v ?47v x1v x2v x3v) -> (X-z522v : eq ((?47v ⊔ ?49v) ⊔ ?51v) (ex2 ?51v ?49v ?47v x1v x2v x3v) Htermv X-x-274v) -> Pv X-x-274v) H1v Htermv (refl ((?47v ⊔ ?49v) ⊔ ?51v) (ex2 ?51v ?49v ?47v x1v x2v x3v) Htermv)

ex2-commute : (?44v ?33v ?31v : Level) -> (A0v : Set ?44v) -> (P0v : (X--v : A0v) -> Set ?33v) -> (P1v : (X--v : A0v) -> Set ?31v) -> (X--v : ex2 ?44v ?33v ?31v A0v (λ (x0v : A0v) -> P0v x0v) (λ (x0v : A0v) -> P1v x0v)) -> ex2 ?44v ?31v ?33v A0v (λ (x0v : A0v) -> P1v x0v) (λ (x0v : A0v) -> P0v x0v)
ex2-commute = λ (?44v ?33v ?31v : Level) -> λ (A0v : Set ?44v) -> λ (P0v : (X--v : A0v) -> Set ?33v) -> λ (P1v : (X--v : A0v) -> Set ?31v) -> λ (X-clearmev : ex2 ?44v ?33v ?31v A0v (λ (x0v : A0v) -> P0v x0v) (λ (x0v : A0v) -> P1v x0v)) -> match-ex2 ?44v ?33v ?31v A0v (λ (x0v : A0v) -> P0v x0v) (λ (x0v : A0v) -> P1v x0v) ((?44v ⊔ ?33v) ⊔ ?31v) (λ (X--v : ex2 ?44v ?33v ?31v A0v (λ (x0v : A0v) -> P0v x0v) (λ (x0v : A0v) -> P1v x0v)) -> ex2 ?44v ?31v ?33v A0v (λ (x0v : A0v) -> P1v x0v) (λ (x0v : A0v) -> P0v x0v)) (λ (xv : A0v) -> λ (autov : P0v xv) -> λ (auto'v : P1v xv) -> ex2-intro ?44v ?31v ?33v A0v (λ (x0v : A0v) -> P1v x0v) (λ (x0v : A0v) -> P0v x0v) xv auto'v autov) X-clearmev

iff : (?9v ?8v : Level) -> (X-Av : Set ?9v) -> (X-Bv : Set ?8v) -> Set (lzero ⊔ (?9v ⊔ ?8v))
iff = λ (?9v ?8v : Level) -> λ (Av : Set ?9v) -> λ (Bv : Set ?8v) -> And (?9v ⊔ ?8v) (?9v ⊔ ?8v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av)

iff-sym : (?38v ?37v : Level) -> (Av : Set ?38v) -> (Bv : Set ?37v) -> (X--v : iff ?38v ?37v Av Bv) -> iff ?37v ?38v Bv Av
iff-sym = λ (?38v ?37v : Level) -> λ (Av : Set ?38v) -> λ (Bv : Set ?37v) -> λ (X-clearmev : iff ?38v ?37v Av Bv) -> match-And (?38v ⊔ ?37v) (?38v ⊔ ?37v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av) (?38v ⊔ ?37v) (λ (X--v : And (?38v ⊔ ?37v) (?38v ⊔ ?37v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av)) -> iff ?37v ?38v Bv Av) (λ (autov : (X--v : Av) -> Bv) -> λ (auto'v : (X--v : Bv) -> Av) -> conj (?38v ⊔ ?37v) (?38v ⊔ ?37v) ((X--v : Bv) -> Av) ((X--v : Av) -> Bv) (λ (auto''v : Bv) -> auto'v auto''v) (λ (auto''v : Av) -> autov auto''v)) X-clearmev

iff-trans : (?73v ?72v ?71v : Level) -> (Av : Set ?73v) -> (Bv : Set ?72v) -> (Cv : Set ?71v) -> (X--v : iff ?73v ?72v Av Bv) -> (X--1v : iff ?72v ?71v Bv Cv) -> iff ?73v ?71v Av Cv
iff-trans = λ (?73v ?72v ?71v : Level) -> λ (Av : Set ?73v) -> λ (Bv : Set ?72v) -> λ (Cv : Set ?71v) -> λ (X-clearmev : iff ?73v ?72v Av Bv) -> match-And (?73v ⊔ ?72v) (?73v ⊔ ?72v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av) ((?73v ⊔ ?72v) ⊔ ?71v) (λ (X--v : And (?73v ⊔ ?72v) (?73v ⊔ ?72v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av)) -> (X--1v : iff ?72v ?71v Bv Cv) -> iff ?73v ?71v Av Cv) (λ (H1v : (X--v : Av) -> Bv) -> λ (H2v : (X--v : Bv) -> Av) -> λ (X-clearme0v : iff ?72v ?71v Bv Cv) -> match-And (?72v ⊔ ?71v) (?72v ⊔ ?71v) ((X--v : Bv) -> Cv) ((X--v : Cv) -> Bv) (?73v ⊔ ?71v) (λ (X--v : And (?72v ⊔ ?71v) (?72v ⊔ ?71v) ((X--v : Bv) -> Cv) ((X--v : Cv) -> Bv)) -> iff ?73v ?71v Av Cv) (λ (H3v : (X--v : Bv) -> Cv) -> λ (H4v : (X--v : Cv) -> Bv) -> conj (?73v ⊔ ?71v) (?73v ⊔ ?71v) ((X--v : Av) -> Cv) ((X--v : Cv) -> Av) (λ (autov : Av) -> H3v (H1v autov)) (λ (autov : Cv) -> H2v (H4v autov))) X-clearme0v) X-clearmev

iff-not : (??1v ??0v : Level) -> (Av : Set (lzero ⊔ (??1v ⊔ ??0v))) -> (Bv : Set (lzero ⊔ (??1v ⊔ ??0v))) -> (X--v : iff (??1v ⊔ ??0v) (??1v ⊔ ??0v) Av Bv) -> iff (??1v ⊔ ??0v) (??1v ⊔ ??0v) (Not (??1v ⊔ ??0v) Av) (Not (??1v ⊔ ??0v) Bv)
iff-not = λ (??1v ??0v : Level) -> λ (Av : Set (lzero ⊔ (??1v ⊔ ??0v))) -> λ (Bv : Set (lzero ⊔ (??1v ⊔ ??0v))) -> λ (X-clearmev : iff (??1v ⊔ ??0v) (??1v ⊔ ??0v) Av Bv) -> match-And (??1v ⊔ ??0v) (??1v ⊔ ??0v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av) (??1v ⊔ ??0v) (λ (X--v : And (??1v ⊔ ??0v) (??1v ⊔ ??0v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av)) -> iff (??1v ⊔ ??0v) (??1v ⊔ ??0v) (Not (??1v ⊔ ??0v) Av) (Not (??1v ⊔ ??0v) Bv)) (λ (H1v : (X--v : Av) -> Bv) -> λ (H2v : (X--v : Bv) -> Av) -> conj (??1v ⊔ ??0v) (??1v ⊔ ??0v) ((X--v : Not (??1v ⊔ ??0v) Av) -> Not (??1v ⊔ ??0v) Bv) ((X--v : Not (??1v ⊔ ??0v) Bv) -> Not (??1v ⊔ ??0v) Av) (λ (autov : Not (??1v ⊔ ??0v) Av) -> not-to-not (??1v ⊔ ??0v) Bv Av (λ (auto'v : Bv) -> H2v auto'v) autov) (λ (autov : Not (??1v ⊔ ??0v) Bv) -> not-to-not (??1v ⊔ ??0v) Av Bv (λ (auto'v : Av) -> H1v auto'v) autov)) X-clearmev

iff-and-l : (?83v ?82v ?81v : Level) -> (Av : Set ?83v) -> (Bv : Set ?82v) -> (Cv : Set ?81v) -> (X--v : iff ?83v ?82v Av Bv) -> iff (?83v ⊔ ?81v) (?82v ⊔ ?81v) (And ?81v ?83v Cv Av) (And ?81v ?82v Cv Bv)
iff-and-l = λ (?83v ?82v ?81v : Level) -> λ (Av : Set ?83v) -> λ (Bv : Set ?82v) -> λ (Cv : Set ?81v) -> λ (X-clearmev : iff ?83v ?82v Av Bv) -> match-And (?83v ⊔ ?82v) (?83v ⊔ ?82v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av) ((?83v ⊔ ?82v) ⊔ ?81v) (λ (X--v : And (?83v ⊔ ?82v) (?83v ⊔ ?82v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av)) -> iff (?83v ⊔ ?81v) (?82v ⊔ ?81v) (And ?81v ?83v Cv Av) (And ?81v ?82v Cv Bv)) (λ (H1v : (X--v : Av) -> Bv) -> λ (H2v : (X--v : Bv) -> Av) -> conj ((?83v ⊔ ?82v) ⊔ ?81v) ((?83v ⊔ ?82v) ⊔ ?81v) ((X--v : And ?81v ?83v Cv Av) -> And ?81v ?82v Cv Bv) ((X--v : And ?81v ?82v Cv Bv) -> And ?81v ?83v Cv Av) (λ (X-clearme0v : And ?81v ?83v Cv Av) -> match-And ?81v ?83v Cv Av (?82v ⊔ ?81v) (λ (X--v : And ?81v ?83v Cv Av) -> And ?81v ?82v Cv Bv) (λ (autov : Cv) -> λ (auto'v : Av) -> conj ?81v ?82v Cv Bv autov (H1v auto'v)) X-clearme0v) (λ (X-clearme0v : And ?81v ?82v Cv Bv) -> match-And ?81v ?82v Cv Bv (?83v ⊔ ?81v) (λ (X--v : And ?81v ?82v Cv Bv) -> And ?81v ?83v Cv Av) (λ (autov : Cv) -> λ (auto'v : Bv) -> conj ?81v ?83v Cv Av autov (H2v auto'v)) X-clearme0v)) X-clearmev

iff-and-r : (?83v ?82v ?81v : Level) -> (Av : Set ?83v) -> (Bv : Set ?82v) -> (Cv : Set ?81v) -> (X--v : iff ?83v ?82v Av Bv) -> iff (?83v ⊔ ?81v) (?82v ⊔ ?81v) (And ?83v ?81v Av Cv) (And ?82v ?81v Bv Cv)
iff-and-r = λ (?83v ?82v ?81v : Level) -> λ (Av : Set ?83v) -> λ (Bv : Set ?82v) -> λ (Cv : Set ?81v) -> λ (X-clearmev : iff ?83v ?82v Av Bv) -> match-And (?83v ⊔ ?82v) (?83v ⊔ ?82v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av) ((?83v ⊔ ?82v) ⊔ ?81v) (λ (X--v : And (?83v ⊔ ?82v) (?83v ⊔ ?82v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av)) -> iff (?83v ⊔ ?81v) (?82v ⊔ ?81v) (And ?83v ?81v Av Cv) (And ?82v ?81v Bv Cv)) (λ (H1v : (X--v : Av) -> Bv) -> λ (H2v : (X--v : Bv) -> Av) -> conj ((?83v ⊔ ?82v) ⊔ ?81v) ((?83v ⊔ ?82v) ⊔ ?81v) ((X--v : And ?83v ?81v Av Cv) -> And ?82v ?81v Bv Cv) ((X--v : And ?82v ?81v Bv Cv) -> And ?83v ?81v Av Cv) (λ (X-clearme0v : And ?83v ?81v Av Cv) -> match-And ?83v ?81v Av Cv (?82v ⊔ ?81v) (λ (X--v : And ?83v ?81v Av Cv) -> And ?82v ?81v Bv Cv) (λ (autov : Av) -> λ (auto'v : Cv) -> conj ?82v ?81v Bv Cv (H1v autov) auto'v) X-clearme0v) (λ (X-clearme0v : And ?82v ?81v Bv Cv) -> match-And ?82v ?81v Bv Cv (?83v ⊔ ?81v) (λ (X--v : And ?82v ?81v Bv Cv) -> And ?83v ?81v Av Cv) (λ (autov : Bv) -> λ (auto'v : Cv) -> conj ?83v ?81v Av Cv (H2v autov) auto'v) X-clearme0v)) X-clearmev

iff-or-l : (?87v ?86v ?85v : Level) -> (Av : Set ?87v) -> (Bv : Set ?86v) -> (Cv : Set ?85v) -> (X--v : iff ?87v ?86v Av Bv) -> iff (?87v ⊔ ?85v) (?86v ⊔ ?85v) (Or ?85v ?87v Cv Av) (Or ?85v ?86v Cv Bv)
iff-or-l = λ (?87v ?86v ?85v : Level) -> λ (Av : Set ?87v) -> λ (Bv : Set ?86v) -> λ (Cv : Set ?85v) -> λ (X-clearmev : iff ?87v ?86v Av Bv) -> match-And (?87v ⊔ ?86v) (?87v ⊔ ?86v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av) ((?87v ⊔ ?86v) ⊔ ?85v) (λ (X--v : And (?87v ⊔ ?86v) (?87v ⊔ ?86v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av)) -> iff (?87v ⊔ ?85v) (?86v ⊔ ?85v) (Or ?85v ?87v Cv Av) (Or ?85v ?86v Cv Bv)) (λ (H1v : (X--v : Av) -> Bv) -> λ (H2v : (X--v : Bv) -> Av) -> conj ((?87v ⊔ ?86v) ⊔ ?85v) ((?87v ⊔ ?86v) ⊔ ?85v) ((X--v : Or ?85v ?87v Cv Av) -> Or ?85v ?86v Cv Bv) ((X--v : Or ?85v ?86v Cv Bv) -> Or ?85v ?87v Cv Av) (λ (X-clearme0v : Or ?85v ?87v Cv Av) -> match-Or ?85v ?87v Cv Av (?86v ⊔ ?85v) (λ (X--v : Or ?85v ?87v Cv Av) -> Or ?85v ?86v Cv Bv) (λ (autov : Cv) -> or-introl ?85v ?86v Cv Bv autov) (λ (autov : Av) -> or-intror ?85v ?86v Cv Bv (H1v autov)) X-clearme0v) (λ (X-clearme0v : Or ?85v ?86v Cv Bv) -> match-Or ?85v ?86v Cv Bv (?87v ⊔ ?85v) (λ (X--v : Or ?85v ?86v Cv Bv) -> Or ?85v ?87v Cv Av) (λ (autov : Cv) -> or-introl ?85v ?87v Cv Av autov) (λ (autov : Bv) -> or-intror ?85v ?87v Cv Av (H2v autov)) X-clearme0v)) X-clearmev

iff-or-r : (?87v ?86v ?85v : Level) -> (Av : Set ?87v) -> (Bv : Set ?86v) -> (Cv : Set ?85v) -> (X--v : iff ?87v ?86v Av Bv) -> iff (?87v ⊔ ?85v) (?86v ⊔ ?85v) (Or ?87v ?85v Av Cv) (Or ?86v ?85v Bv Cv)
iff-or-r = λ (?87v ?86v ?85v : Level) -> λ (Av : Set ?87v) -> λ (Bv : Set ?86v) -> λ (Cv : Set ?85v) -> λ (X-clearmev : iff ?87v ?86v Av Bv) -> match-And (?87v ⊔ ?86v) (?87v ⊔ ?86v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av) ((?87v ⊔ ?86v) ⊔ ?85v) (λ (X--v : And (?87v ⊔ ?86v) (?87v ⊔ ?86v) ((X--v : Av) -> Bv) ((X--v : Bv) -> Av)) -> iff (?87v ⊔ ?85v) (?86v ⊔ ?85v) (Or ?87v ?85v Av Cv) (Or ?86v ?85v Bv Cv)) (λ (H1v : (X--v : Av) -> Bv) -> λ (H2v : (X--v : Bv) -> Av) -> conj ((?87v ⊔ ?86v) ⊔ ?85v) ((?87v ⊔ ?86v) ⊔ ?85v) ((X--v : Or ?87v ?85v Av Cv) -> Or ?86v ?85v Bv Cv) ((X--v : Or ?86v ?85v Bv Cv) -> Or ?87v ?85v Av Cv) (λ (X-clearme0v : Or ?87v ?85v Av Cv) -> match-Or ?87v ?85v Av Cv (?86v ⊔ ?85v) (λ (X--v : Or ?87v ?85v Av Cv) -> Or ?86v ?85v Bv Cv) (λ (autov : Av) -> or-introl ?86v ?85v Bv Cv (H1v autov)) (λ (autov : Cv) -> or-intror ?86v ?85v Bv Cv autov) X-clearme0v) (λ (X-clearme0v : Or ?86v ?85v Bv Cv) -> match-Or ?86v ?85v Bv Cv (?87v ⊔ ?85v) (λ (X--v : Or ?86v ?85v Bv Cv) -> Or ?87v ?85v Av Cv) (λ (autov : Bv) -> or-introl ?87v ?85v Av Cv (H2v autov)) (λ (autov : Cv) -> or-intror ?87v ?85v Av Cv autov) X-clearme0v)) X-clearmev

R0 : (?1v : Level) -> (Tv : Set ?1v) -> (X-tv : Tv) -> Tv
R0 = λ (?1v : Level) -> λ (Tv : Set ?1v) -> λ (tv : Tv) -> tv

R1 : (?13v ?8v : Level) -> (Av : Set ?13v) -> (X-xv : Av) -> (Q-v : (x-19v : Av) -> (X-x-20v : eq ?13v Av X-xv x-19v) -> Set ?8v) -> (X-H-reflv : Q-v X-xv (refl ?13v Av X-xv)) -> (x-19v : Av) -> (x-20v : eq ?13v Av X-xv x-19v) -> Q-v x-19v x-20v
R1 = λ (?13v ?8v : Level) -> eq-rect-Type0 ?13v ?8v

R2 : (?42v ?37v ?26v : Level) -> (T0v : Set ?42v) -> (a0v : T0v) -> (T1v : (x0v : T0v) -> (X--v : eq ?42v T0v a0v x0v) -> Set ?37v) -> (a1v : T1v a0v (refl ?42v T0v a0v)) -> (T2v : (x0v : T0v) -> (p0v : eq ?42v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (X--v : eq ?37v (T1v x0v p0v) (R1 ?42v ?37v T0v a0v T1v a1v x0v p0v) x1v) -> Set ?26v) -> (X-a2v : T2v a0v (refl ?42v T0v a0v) a1v (refl ?37v (T1v a0v (refl ?42v T0v a0v)) a1v)) -> (b0v : T0v) -> (e0v : eq ?42v T0v a0v b0v) -> (b1v : T1v b0v e0v) -> (e1v : eq ?37v (T1v b0v e0v) (R1 ?42v ?37v T0v a0v T1v a1v b0v e0v) b1v) -> T2v b0v e0v b1v e1v
R2 = λ (?42v ?37v ?26v : Level) -> λ (T0v : Set ?42v) -> λ (a0v : T0v) -> λ (T1v : (x0v : T0v) -> (X--v : eq ?42v T0v a0v x0v) -> Set ?37v) -> λ (a1v : T1v a0v (refl ?42v T0v a0v)) -> λ (T2v : (x0v : T0v) -> (p0v : eq ?42v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (X--v : eq ?37v (T1v x0v p0v) (R1 ?42v ?37v T0v a0v T1v a1v x0v p0v) x1v) -> Set ?26v) -> λ (a2v : T2v a0v (refl ?42v T0v a0v) a1v (refl ?37v (T1v a0v (refl ?42v T0v a0v)) a1v)) -> λ (b0v : T0v) -> λ (e0v : eq ?42v T0v a0v b0v) -> λ (b1v : T1v b0v e0v) -> λ (e1v : eq ?37v (T1v b0v e0v) (R1 ?42v ?37v T0v a0v T1v a1v b0v e0v) b1v) -> eq-rect-Type0 ?37v ?26v (T1v b0v e0v) (R1 ?42v ?37v T0v a0v T1v a1v b0v e0v) (T2v b0v e0v) (R1 ?42v ?26v T0v a0v (λ (x-19v : T0v) -> λ (X-x-20v : eq ?42v T0v a0v x-19v) -> T2v x-19v X-x-20v (R1 ?42v ?37v T0v a0v T1v a1v x-19v X-x-20v) (refl ?37v (T1v x-19v X-x-20v) (R1 ?42v ?37v T0v a0v T1v a1v x-19v X-x-20v))) a2v b0v e0v) b1v e1v

R3 : (?80v ?75v ?64v ?45v : Level) -> (T0v : Set ?80v) -> (a0v : T0v) -> (T1v : (x0v : T0v) -> (X--v : eq ?80v T0v a0v x0v) -> Set ?75v) -> (a1v : T1v a0v (refl ?80v T0v a0v)) -> (T2v : (x0v : T0v) -> (p0v : eq ?80v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (X--v : eq ?75v (T1v x0v p0v) (R1 ?80v ?75v T0v a0v T1v a1v x0v p0v) x1v) -> Set ?64v) -> (a2v : T2v a0v (refl ?80v T0v a0v) a1v (refl ?75v (T1v a0v (refl ?80v T0v a0v)) a1v)) -> (T3v : (x0v : T0v) -> (p0v : eq ?80v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (p1v : eq ?75v (T1v x0v p0v) (R1 ?80v ?75v T0v a0v T1v a1v x0v p0v) x1v) -> (x2v : T2v x0v p0v x1v p1v) -> (X--v : eq ?64v (T2v x0v p0v x1v p1v) (R2 ?80v ?75v ?64v T0v a0v T1v a1v T2v a2v x0v p0v x1v p1v) x2v) -> Set ?45v) -> (X-a3v : T3v a0v (refl ?80v T0v a0v) a1v (refl ?75v (T1v a0v (refl ?80v T0v a0v)) a1v) a2v (refl ?64v (T2v a0v (refl ?80v T0v a0v) a1v (refl ?75v (T1v a0v (refl ?80v T0v a0v)) a1v)) a2v)) -> (b0v : T0v) -> (e0v : eq ?80v T0v a0v b0v) -> (b1v : T1v b0v e0v) -> (e1v : eq ?75v (T1v b0v e0v) (R1 ?80v ?75v T0v a0v T1v a1v b0v e0v) b1v) -> (b2v : T2v b0v e0v b1v e1v) -> (e2v : eq ?64v (T2v b0v e0v b1v e1v) (R2 ?80v ?75v ?64v T0v a0v T1v a1v T2v a2v b0v e0v b1v e1v) b2v) -> T3v b0v e0v b1v e1v b2v e2v
R3 = λ (?80v ?75v ?64v ?45v : Level) -> λ (T0v : Set ?80v) -> λ (a0v : T0v) -> λ (T1v : (x0v : T0v) -> (X--v : eq ?80v T0v a0v x0v) -> Set ?75v) -> λ (a1v : T1v a0v (refl ?80v T0v a0v)) -> λ (T2v : (x0v : T0v) -> (p0v : eq ?80v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (X--v : eq ?75v (T1v x0v p0v) (R1 ?80v ?75v T0v a0v T1v a1v x0v p0v) x1v) -> Set ?64v) -> λ (a2v : T2v a0v (refl ?80v T0v a0v) a1v (refl ?75v (T1v a0v (refl ?80v T0v a0v)) a1v)) -> λ (T3v : (x0v : T0v) -> (p0v : eq ?80v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (p1v : eq ?75v (T1v x0v p0v) (R1 ?80v ?75v T0v a0v T1v a1v x0v p0v) x1v) -> (x2v : T2v x0v p0v x1v p1v) -> (X--v : eq ?64v (T2v x0v p0v x1v p1v) (R2 ?80v ?75v ?64v T0v a0v T1v a1v T2v a2v x0v p0v x1v p1v) x2v) -> Set ?45v) -> λ (a3v : T3v a0v (refl ?80v T0v a0v) a1v (refl ?75v (T1v a0v (refl ?80v T0v a0v)) a1v) a2v (refl ?64v (T2v a0v (refl ?80v T0v a0v) a1v (refl ?75v (T1v a0v (refl ?80v T0v a0v)) a1v)) a2v)) -> λ (b0v : T0v) -> λ (e0v : eq ?80v T0v a0v b0v) -> λ (b1v : T1v b0v e0v) -> λ (e1v : eq ?75v (T1v b0v e0v) (R1 ?80v ?75v T0v a0v T1v a1v b0v e0v) b1v) -> λ (b2v : T2v b0v e0v b1v e1v) -> λ (e2v : eq ?64v (T2v b0v e0v b1v e1v) (R2 ?80v ?75v ?64v T0v a0v T1v a1v T2v a2v b0v e0v b1v e1v) b2v) -> eq-rect-Type0 ?64v ?45v (T2v b0v e0v b1v e1v) (R2 ?80v ?75v ?64v T0v a0v T1v a1v T2v a2v b0v e0v b1v e1v) (T3v b0v e0v b1v e1v) (R2 ?80v ?75v ?45v T0v a0v T1v a1v (λ (x0v : T0v) -> λ (p0v : eq ?80v T0v a0v x0v) -> λ (x1v : T1v x0v p0v) -> λ (X--v : eq ?75v (T1v x0v p0v) (R1 ?80v ?75v T0v a0v T1v a1v x0v p0v) x1v) -> T3v x0v p0v x1v X--v (R2 ?80v ?75v ?64v T0v a0v T1v a1v T2v a2v x0v p0v x1v X--v) (refl ?64v (T2v x0v p0v x1v X--v) (R2 ?80v ?75v ?64v T0v a0v T1v a1v T2v a2v x0v p0v x1v X--v))) a3v b0v e0v b1v e1v) b2v e2v

R4 : (?135v ?130v ?119v ?100v ?70v : Level) -> (T0v : Set ?135v) -> (a0v : T0v) -> (T1v : (x0v : T0v) -> (X--v : eq ?135v T0v a0v x0v) -> Set ?130v) -> (a1v : T1v a0v (refl ?135v T0v a0v)) -> (T2v : (x0v : T0v) -> (p0v : eq ?135v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (X--v : eq ?130v (T1v x0v p0v) (R1 ?135v ?130v T0v a0v T1v a1v x0v p0v) x1v) -> Set ?119v) -> (a2v : T2v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v)) -> (T3v : (x0v : T0v) -> (p0v : eq ?135v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (p1v : eq ?130v (T1v x0v p0v) (R1 ?135v ?130v T0v a0v T1v a1v x0v p0v) x1v) -> (x2v : T2v x0v p0v x1v p1v) -> (X--v : eq ?119v (T2v x0v p0v x1v p1v) (R2 ?135v ?130v ?119v T0v a0v T1v a1v T2v a2v x0v p0v x1v p1v) x2v) -> Set ?100v) -> (a3v : T3v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v) a2v (refl ?119v (T2v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v)) a2v)) -> (T4v : (x0v : T0v) -> (p0v : eq ?135v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (p1v : eq ?130v (T1v x0v p0v) (R1 ?135v ?130v T0v a0v T1v a1v x0v p0v) x1v) -> (x2v : T2v x0v p0v x1v p1v) -> (p2v : eq ?119v (T2v x0v p0v x1v p1v) (R2 ?135v ?130v ?119v T0v a0v T1v a1v T2v a2v x0v p0v x1v p1v) x2v) -> (x3v : T3v x0v p0v x1v p1v x2v p2v) -> (X-p3v : eq ?100v (T3v x0v p0v x1v p1v x2v p2v) (R3 ?135v ?130v ?119v ?100v T0v a0v T1v a1v T2v a2v T3v a3v x0v p0v x1v p1v x2v p2v) x3v) -> Set ?70v) -> (X-a4v : T4v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v) a2v (refl ?119v (T2v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v)) a2v) a3v (refl ?100v (T3v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v) a2v (refl ?119v (T2v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v)) a2v)) a3v)) -> (b0v : T0v) -> (e0v : eq ?135v T0v a0v b0v) -> (b1v : T1v b0v e0v) -> (e1v : eq ?130v (T1v b0v e0v) (R1 ?135v ?130v T0v a0v T1v a1v b0v e0v) b1v) -> (b2v : T2v b0v e0v b1v e1v) -> (e2v : eq ?119v (T2v b0v e0v b1v e1v) (R2 ?135v ?130v ?119v T0v a0v T1v a1v T2v a2v b0v e0v b1v e1v) b2v) -> (b3v : T3v b0v e0v b1v e1v b2v e2v) -> (e3v : eq ?100v (T3v b0v e0v b1v e1v b2v e2v) (R3 ?135v ?130v ?119v ?100v T0v a0v T1v a1v T2v a2v T3v a3v b0v e0v b1v e1v b2v e2v) b3v) -> T4v b0v e0v b1v e1v b2v e2v b3v e3v
R4 = λ (?135v ?130v ?119v ?100v ?70v : Level) -> λ (T0v : Set ?135v) -> λ (a0v : T0v) -> λ (T1v : (x0v : T0v) -> (X--v : eq ?135v T0v a0v x0v) -> Set ?130v) -> λ (a1v : T1v a0v (refl ?135v T0v a0v)) -> λ (T2v : (x0v : T0v) -> (p0v : eq ?135v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (X--v : eq ?130v (T1v x0v p0v) (R1 ?135v ?130v T0v a0v T1v a1v x0v p0v) x1v) -> Set ?119v) -> λ (a2v : T2v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v)) -> λ (T3v : (x0v : T0v) -> (p0v : eq ?135v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (p1v : eq ?130v (T1v x0v p0v) (R1 ?135v ?130v T0v a0v T1v a1v x0v p0v) x1v) -> (x2v : T2v x0v p0v x1v p1v) -> (X--v : eq ?119v (T2v x0v p0v x1v p1v) (R2 ?135v ?130v ?119v T0v a0v T1v a1v T2v a2v x0v p0v x1v p1v) x2v) -> Set ?100v) -> λ (a3v : T3v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v) a2v (refl ?119v (T2v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v)) a2v)) -> λ (T4v : (x0v : T0v) -> (p0v : eq ?135v T0v a0v x0v) -> (x1v : T1v x0v p0v) -> (p1v : eq ?130v (T1v x0v p0v) (R1 ?135v ?130v T0v a0v T1v a1v x0v p0v) x1v) -> (x2v : T2v x0v p0v x1v p1v) -> (p2v : eq ?119v (T2v x0v p0v x1v p1v) (R2 ?135v ?130v ?119v T0v a0v T1v a1v T2v a2v x0v p0v x1v p1v) x2v) -> (x3v : T3v x0v p0v x1v p1v x2v p2v) -> (X-p3v : eq ?100v (T3v x0v p0v x1v p1v x2v p2v) (R3 ?135v ?130v ?119v ?100v T0v a0v T1v a1v T2v a2v T3v a3v x0v p0v x1v p1v x2v p2v) x3v) -> Set ?70v) -> λ (a4v : T4v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v) a2v (refl ?119v (T2v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v)) a2v) a3v (refl ?100v (T3v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v) a2v (refl ?119v (T2v a0v (refl ?135v T0v a0v) a1v (refl ?130v (T1v a0v (refl ?135v T0v a0v)) a1v)) a2v)) a3v)) -> λ (b0v : T0v) -> λ (e0v : eq ?135v T0v a0v b0v) -> λ (b1v : T1v b0v e0v) -> λ (e1v : eq ?130v (T1v b0v e0v) (R1 ?135v ?130v T0v a0v T1v a1v b0v e0v) b1v) -> λ (b2v : T2v b0v e0v b1v e1v) -> λ (e2v : eq ?119v (T2v b0v e0v b1v e1v) (R2 ?135v ?130v ?119v T0v a0v T1v a1v T2v a2v b0v e0v b1v e1v) b2v) -> λ (b3v : T3v b0v e0v b1v e1v b2v e2v) -> λ (e3v : eq ?100v (T3v b0v e0v b1v e1v b2v e2v) (R3 ?135v ?130v ?119v ?100v T0v a0v T1v a1v T2v a2v T3v a3v b0v e0v b1v e1v b2v e2v) b3v) -> eq-rect-Type0 ?100v ?70v (T3v b0v e0v b1v e1v b2v e2v) (R3 ?135v ?130v ?119v ?100v T0v a0v T1v a1v T2v a2v T3v a3v b0v e0v b1v e1v b2v e2v) (T4v b0v e0v b1v e1v b2v e2v) (R3 ?135v ?130v ?119v ?70v T0v a0v T1v a1v T2v a2v (λ (x0v : T0v) -> λ (p0v : eq ?135v T0v a0v x0v) -> λ (x1v : T1v x0v p0v) -> λ (p1v : eq ?130v (T1v x0v p0v) (R1 ?135v ?130v T0v a0v T1v a1v x0v p0v) x1v) -> λ (x2v : T2v x0v p0v x1v p1v) -> λ (X--v : eq ?119v (T2v x0v p0v x1v p1v) (R2 ?135v ?130v ?119v T0v a0v T1v a1v T2v a2v x0v p0v x1v p1v) x2v) -> T4v x0v p0v x1v p1v x2v X--v (R3 ?135v ?130v ?119v ?100v T0v a0v T1v a1v T2v a2v T3v a3v x0v p0v x1v p1v x2v X--v) (refl ?100v (T3v x0v p0v x1v p1v x2v X--v) (R3 ?135v ?130v ?119v ?100v T0v a0v T1v a1v T2v a2v T3v a3v x0v p0v x1v p1v x2v X--v))) a4v b0v e0v b1v e1v b2v e2v) b3v e3v

eqProp : (?1v : Level) -> (Av : Set ?1v) -> (X-xv : Av) -> (X--v : Av) -> Set ?1v
eqProp = λ (?1v : Level) -> λ (Av : Set ?1v) -> eq ?1v Av

streicherK : (?7v ?4v : Level) -> (Tv : Set ?7v) -> (tv : Tv) -> (Pv : (X--v : eq ?7v Tv tv tv) -> Set ?4v) -> (X--v : Pv (refl ?7v Tv tv)) -> (pv : eq ?7v Tv tv tv) -> Pv pv
streicherK _ _ _ _ _ p refl' = p

