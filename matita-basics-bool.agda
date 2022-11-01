open import Agda.Primitive
open import matita-basics-relations
open import matita-basics-logic

data bool : Set where
  true : bool
  false : bool

match-bool : (return-sort-v : Level) -> (return-type-v : (z-v : bool) -> Set return-sort-v) -> (case-true-v : return-type-v true) -> (case-false-v : return-type-v false) -> (z-v : bool) -> return-type-v z-v
match-bool _ _ casetrue casefalse true = casetrue
match-bool _ _ casetrue casefalse false = casefalse


bool-ind : (l3-v : Level) -> (Q--v : (X-x-326-v : bool) -> Set l3-v) -> (X-H-true-v : Q--v true) -> (X-H-false-v : Q--v false) -> (x-326-v : bool) -> Q--v x-326-v
bool-ind _ _ casetrue casefalse true = casetrue
bool-ind _ _ casetrue casefalse false = casefalse

bool-rect-Type4 : (l3-v : Level) -> (Q--v : (X-x-329-v : bool) -> Set l3-v) -> (X-H-true-v : Q--v true) -> (X-H-false-v : Q--v false) -> (x-329-v : bool) -> Q--v x-329-v
bool-rect-Type4 _ _ casetrue casefalse true = casetrue
bool-rect-Type4 _ _ casetrue casefalse false = casefalse

bool-rect-Type5 : (l3-v : Level) -> (Q--v : (X-x-329-v : bool) -> Set l3-v) -> (X-H-true-v : Q--v true) -> (X-H-false-v : Q--v false) -> (x-329-v : bool) -> Q--v x-329-v
bool-rect-Type5 _ _ casetrue casefalse true = casetrue
bool-rect-Type5 _ _ casetrue casefalse false = casefalse

bool-rect-Type3 : (l3-v : Level) -> (Q--v : (X-x-329-v : bool) -> Set l3-v) -> (X-H-true-v : Q--v true) -> (X-H-false-v : Q--v false) -> (x-329-v : bool) -> Q--v x-329-v
bool-rect-Type3 _ _ casetrue casefalse true = casetrue
bool-rect-Type3 _ _ casetrue casefalse false = casefalse

bool-rect-Type2 : (l3-v : Level) -> (Q--v : (X-x-329-v : bool) -> Set l3-v) -> (X-H-true-v : Q--v true) -> (X-H-false-v : Q--v false) -> (x-329-v : bool) -> Q--v x-329-v
bool-rect-Type2 _ _ casetrue casefalse true = casetrue
bool-rect-Type2 _ _ casetrue casefalse false = casefalse

bool-rect-Type1 : (l3-v : Level) -> (Q--v : (X-x-329-v : bool) -> Set l3-v) -> (X-H-true-v : Q--v true) -> (X-H-false-v : Q--v false) -> (x-329-v : bool) -> Q--v x-329-v
bool-rect-Type1 _ _ casetrue casefalse true = casetrue
bool-rect-Type1 _ _ casetrue casefalse false = casefalse

bool-rect-Type0 : (l3-v : Level) -> (Q--v : (X-x-329-v : bool) -> Set l3-v) -> (X-H-true-v : Q--v true) -> (X-H-false-v : Q--v false) -> (x-329-v : bool) -> Q--v x-329-v
bool-rect-Type0 _ _ casetrue casefalse true = casetrue
bool-rect-Type0 _ _ casetrue casefalse false = casefalse



bool-inv-ind : (l14 : Level) -> (Hterm : bool) -> (P : (X-z587 : bool) -> Set l14) -> (X-H1 : (X-z588 : eq lzero bool Hterm true) -> P true) -> (X-H2 : (X-z588 : eq lzero bool Hterm false) -> P false) -> P Hterm
bool-inv-ind = λ (l14 : Level) -> λ (Hterm : bool) -> λ (P : (X-z587 : bool) -> Set l14) -> λ (H1 : (X-z588 : eq lzero bool Hterm true) -> P true) -> λ (H2 : (X-z588 : eq lzero bool Hterm false) -> P false) -> bool-ind l14 (λ (X-x-326 : bool) -> (X-z588 : eq lzero bool Hterm X-x-326) -> P X-x-326) H1 H2 Hterm (refl lzero bool Hterm)

bool-inv-rect-Type4 : (l14 : Level) -> (Hterm : bool) -> (P : (X-z593 : bool) -> Set l14) -> (X-H1 : (X-z594 : eq lzero bool Hterm true) -> P true) -> (X-H2 : (X-z594 : eq lzero bool Hterm false) -> P false) -> P Hterm
bool-inv-rect-Type4 = λ (l14 : Level) -> λ (Hterm : bool) -> λ (P : (X-z593 : bool) -> Set l14) -> λ (H1 : (X-z594 : eq lzero bool Hterm true) -> P true) -> λ (H2 : (X-z594 : eq lzero bool Hterm false) -> P false) -> bool-rect-Type4 l14 (λ (X-x-329 : bool) -> (X-z594 : eq lzero bool Hterm X-x-329) -> P X-x-329) H1 H2 Hterm (refl lzero bool Hterm)

bool-inv-rect-Type3 : (l14 : Level) -> (Hterm : bool) -> (P : (X-z599 : bool) -> Set l14) -> (X-H1 : (X-z600 : eq lzero bool Hterm true) -> P true) -> (X-H2 : (X-z600 : eq lzero bool Hterm false) -> P false) -> P Hterm
bool-inv-rect-Type3 = λ (l14 : Level) -> λ (Hterm : bool) -> λ (P : (X-z599 : bool) -> Set l14) -> λ (H1 : (X-z600 : eq lzero bool Hterm true) -> P true) -> λ (H2 : (X-z600 : eq lzero bool Hterm false) -> P false) -> bool-rect-Type3 l14 (λ (X-x-335 : bool) -> (X-z600 : eq lzero bool Hterm X-x-335) -> P X-x-335) H1 H2 Hterm (refl lzero bool Hterm)

bool-inv-rect-Type2 : (l14 : Level) -> (Hterm : bool) -> (P : (X-z605 : bool) -> Set l14) -> (X-H1 : (X-z606 : eq lzero bool Hterm true) -> P true) -> (X-H2 : (X-z606 : eq lzero bool Hterm false) -> P false) -> P Hterm
bool-inv-rect-Type2 = λ (l14 : Level) -> λ (Hterm : bool) -> λ (P : (X-z605 : bool) -> Set l14) -> λ (H1 : (X-z606 : eq lzero bool Hterm true) -> P true) -> λ (H2 : (X-z606 : eq lzero bool Hterm false) -> P false) -> bool-rect-Type2 l14 (λ (X-x-338 : bool) -> (X-z606 : eq lzero bool Hterm X-x-338) -> P X-x-338) H1 H2 Hterm (refl lzero bool Hterm)

bool-inv-rect-Type1 : (l14 : Level) -> (Hterm : bool) -> (P : (X-z611 : bool) -> Set l14) -> (X-H1 : (X-z612 : eq lzero bool Hterm true) -> P true) -> (X-H2 : (X-z612 : eq lzero bool Hterm false) -> P false) -> P Hterm
bool-inv-rect-Type1 = λ (l14 : Level) -> λ (Hterm : bool) -> λ (P : (X-z611 : bool) -> Set l14) -> λ (H1 : (X-z612 : eq lzero bool Hterm true) -> P true) -> λ (H2 : (X-z612 : eq lzero bool Hterm false) -> P false) -> bool-rect-Type1 l14 (λ (X-x-341 : bool) -> (X-z612 : eq lzero bool Hterm X-x-341) -> P X-x-341) H1 H2 Hterm (refl lzero bool Hterm)

bool-inv-rect-Type0 : (l14 : Level) -> (Hterm : bool) -> (P : (X-z617 : bool) -> Set l14) -> (X-H1 : (X-z618 : eq lzero bool Hterm true) -> P true) -> (X-H2 : (X-z618 : eq lzero bool Hterm false) -> P false) -> P Hterm
bool-inv-rect-Type0 = λ (l14 : Level) -> λ (Hterm : bool) -> λ (P : (X-z617 : bool) -> Set l14) -> λ (H1 : (X-z618 : eq lzero bool Hterm true) -> P true) -> λ (H2 : (X-z618 : eq lzero bool Hterm false) -> P false) -> bool-rect-Type0 l14 (λ (X-x-344 : bool) -> (X-z618 : eq lzero bool Hterm X-x-344) -> P X-x-344) H1 H2 Hterm (refl lzero bool Hterm)

bool-discr : (l86 : Level) -> (x : bool) -> (y : bool) -> (X-e : eq lzero bool x y) -> match-bool ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l86))) (λ (X-- : bool) -> Set ((lsuc lzero) ⊔ (lsuc l86))) (match-bool ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l86))) (λ (X-- : bool) -> Set ((lsuc lzero) ⊔ (lsuc l86))) ((P : Set l86) -> (X-z19 : P) -> P) ((P : Set l86) -> P) y) (match-bool ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l86))) (λ (X-- : bool) -> Set ((lsuc lzero) ⊔ (lsuc l86))) ((P : Set l86) -> P) ((P : Set l86) -> (X-z20 : P) -> P) y) x
bool-discr = λ (l86 : Level) -> λ (x : bool) -> λ (y : bool) -> λ (Deq : eq lzero bool x y) -> eq-rect-Type2 lzero ((lsuc lzero) ⊔ (lsuc l86)) bool x (λ (x-13 : bool) -> λ (X-x-14 : eq lzero bool x x-13) -> match-bool ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l86))) (λ (X-- : bool) -> Set ((lsuc lzero) ⊔ (lsuc l86))) (match-bool ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l86))) (λ (X-- : bool) -> Set ((lsuc lzero) ⊔ (lsuc l86))) ((P : Set l86) -> (X-z19 : P) -> P) ((P : Set l86) -> P) x-13) (match-bool ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l86))) (λ (X-- : bool) -> Set ((lsuc lzero) ⊔ (lsuc l86))) ((P : Set l86) -> P) ((P : Set l86) -> (X-z20 : P) -> P) x-13) x) (match-bool ((lsuc lzero) ⊔ (lsuc l86)) (λ (X-- : bool) -> match-bool ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l86))) (λ (X-0 : bool) -> Set ((lsuc lzero) ⊔ (lsuc l86))) (match-bool ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l86))) (λ (X-0 : bool) -> Set ((lsuc lzero) ⊔ (lsuc l86))) ((P : Set l86) -> (X-z19 : P) -> P) ((P : Set l86) -> P) X--) (match-bool ((lsuc (lsuc lzero)) ⊔ (lsuc (lsuc l86))) (λ (X-0 : bool) -> Set ((lsuc lzero) ⊔ (lsuc l86))) ((P : Set l86) -> P) ((P : Set l86) -> (X-z20 : P) -> P) X--) X--) (λ (P : Set l86) -> λ (DH : P) -> DH) (λ (P : Set l86) -> λ (DH : P) -> DH) x) y Deq

not-eq-true-false : Not lzero (eq lzero bool true false)
not-eq-true-false = nmk lzero (eq lzero bool true false) (λ (Heq : eq lzero bool true false) -> bool-discr lzero true false Heq (False lzero))

notb : (X-- : bool) -> bool
notb = λ (b : bool) -> match-bool lzero (λ (X-- : bool) -> bool) false true b

notb-elim : (l13 : Level) -> (b : bool) -> (P : (X-- : bool) -> Set l13) -> (X-- : match-bool ((lsuc lzero) ⊔ (lsuc l13)) (λ (X-- : bool) -> Set l13) (P false) (P true) b) -> P (notb b)
notb-elim = λ (l13 : Level) -> λ (b : bool) -> λ (P : (X-- : bool) -> Set l13) -> bool-ind l13 (λ (X-x-326 : bool) -> (X-- : match-bool ((lsuc lzero) ⊔ (lsuc l13)) (λ (X-- : bool) -> Set l13) (P false) (P true) X-x-326) -> P (notb X-x-326)) (λ (auto : P false) -> auto) (λ (auto : P true) -> auto) b

notb-notb : (b : bool) -> eq lzero bool (notb (notb b)) b
notb-notb = λ (b : bool) -> bool-ind lzero (λ (X-x-326 : bool) -> eq lzero bool (notb (notb X-x-326)) X-x-326) (refl lzero bool (notb (notb true))) (refl lzero bool (notb (notb false))) b

injective-notb : ||injective|| lzero lzero bool bool notb
injective-notb = λ (b1 : bool) -> λ (b2 : bool) -> λ (H : eq lzero bool (notb b1) (notb b2)) -> rewrite-r lzero lzero bool b2 (λ (X-- : bool) -> eq lzero bool X-- b2) (refl lzero bool b2) b1 (rewrite-l lzero lzero bool (notb (notb b1)) (λ (X-- : bool) -> eq lzero bool X-- b2) (rewrite-r lzero lzero bool (notb b2) (λ (X-- : bool) -> eq lzero bool (notb X--) b2) (notb-notb b2) (notb b1) H) b1 (notb-notb b1))

noteq-to-eqnot : (b1 : bool) -> (b2 : bool) -> (X-- : Not lzero (eq lzero bool b1 b2)) -> eq lzero bool b1 (notb b2)
noteq-to-eqnot = λ (X-clearme : bool) -> match-bool lzero (λ (X-- : bool) -> (b2 : bool) -> (X--1 : Not lzero (eq lzero bool X-- b2)) -> eq lzero bool X-- (notb b2)) (λ (X-clearme0 : bool) -> match-bool lzero (λ (X-- : bool) -> (X--1 : Not lzero (eq lzero bool true X--)) -> eq lzero bool true (notb X--)) (λ (H : Not lzero (eq lzero bool true true)) -> False-ind lzero lzero (λ (X-x-66 : False lzero) -> eq lzero bool true (notb true)) (absurd lzero (eq lzero bool true true) (refl lzero bool true) H)) (λ (auto : Not lzero (eq lzero bool true false)) -> refl lzero bool true) X-clearme0) (λ (X-clearme0 : bool) -> match-bool lzero (λ (X-- : bool) -> (X--1 : Not lzero (eq lzero bool false X--)) -> eq lzero bool false (notb X--)) (λ (auto : Not lzero (eq lzero bool false true)) -> refl lzero bool false) (λ (H : Not lzero (eq lzero bool false false)) -> False-ind lzero lzero (λ (X-x-66 : False lzero) -> eq lzero bool false (notb false)) (absurd lzero (eq lzero bool false false) (refl lzero bool false) H)) X-clearme0) X-clearme

eqnot-to-noteq : (b1 : bool) -> (b2 : bool) -> (X-- : eq lzero bool b1 (notb b2)) -> Not lzero (eq lzero bool b1 b2)
eqnot-to-noteq = λ (X-clearme : bool) -> match-bool lzero (λ (X-- : bool) -> (b2 : bool) -> (X--1 : eq lzero bool X-- (notb b2)) -> Not lzero (eq lzero bool X-- b2)) (λ (X-clearme0 : bool) -> match-bool lzero (λ (X-- : bool) -> (X--1 : eq lzero bool true (notb X--)) -> Not lzero (eq lzero bool true X--)) (λ (auto : eq lzero bool true false) -> eq-coerc lzero (Not lzero (eq lzero bool true false)) (Not lzero (eq lzero bool true true)) not-eq-true-false (rewrite-l lzero (lsuc lzero) bool true (λ (X-- : bool) -> eq (lsuc lzero) (Set (lzero)) (Not lzero (eq lzero bool true X--)) (Not lzero (eq lzero bool true true))) (refl (lsuc lzero) (Set (lzero)) (Not lzero (eq lzero bool true true))) false auto)) (λ (auto : eq lzero bool true true) -> not-eq-true-false) X-clearme0) (λ (X-clearme0 : bool) -> match-bool lzero (λ (X-- : bool) -> (X--1 : eq lzero bool false (notb X--)) -> Not lzero (eq lzero bool false X--)) (λ (X-- : eq lzero bool false false) -> not-to-not lzero (eq lzero bool false true) (eq lzero bool true false) (λ (auto : eq lzero bool false true) -> rewrite-r lzero lzero bool true (λ (X--1 : bool) -> eq lzero bool true X--1) (refl lzero bool true) false auto) not-eq-true-false) (λ (auto : eq lzero bool false true) -> eq-coerc lzero (Not lzero (eq lzero bool true false)) (Not lzero (eq lzero bool false false)) not-eq-true-false (rewrite-r lzero (lsuc lzero) bool true (λ (X-- : bool) -> eq (lsuc lzero) (Set (lzero)) (Not lzero (eq lzero bool true X--)) (Not lzero (eq lzero bool false false))) (rewrite-r lzero (lsuc lzero) bool true (λ (X-- : bool) -> eq (lsuc lzero) (Set (lzero)) (Not lzero (eq lzero bool true true)) (Not lzero (eq lzero bool X-- false))) (rewrite-r lzero (lsuc lzero) bool true (λ (X-- : bool) -> eq (lsuc lzero) (Set (lzero)) (Not lzero (eq lzero bool true true)) (Not lzero (eq lzero bool true X--))) (refl (lsuc lzero) (Set (lzero)) (Not lzero (eq lzero bool true true))) false auto) false auto) false auto)) X-clearme0) X-clearme

andb : (X-- : bool) -> (X--1 : bool) -> bool
andb = λ (b1 : bool) -> λ (b2 : bool) -> match-bool lzero (λ (X-- : bool) -> bool) b2 false b1

andb-elim : (l13 : Level) -> (b1 : bool) -> (b2 : bool) -> (P : (X-- : bool) -> Set l13) -> (X-- : match-bool ((lsuc lzero) ⊔ (lsuc l13)) (λ (X-- : bool) -> Set l13) (P b2) (P false) b1) -> P (andb b1 b2)
andb-elim = λ (l13 : Level) -> λ (b1 : bool) -> λ (b2 : bool) -> λ (P : (X-- : bool) -> Set l13) -> bool-ind l13 (λ (X-x-326 : bool) -> (X-- : match-bool ((lsuc lzero) ⊔ (lsuc l13)) (λ (X-- : bool) -> Set l13) (P b2) (P false) X-x-326) -> P (andb X-x-326 b2)) (λ (auto : P b2) -> auto) (λ (auto : P false) -> auto) b1

true-to-andb-true : (b1 : bool) -> (b2 : bool) -> (X-- : eq lzero bool b1 true) -> (X--1 : eq lzero bool b2 true) -> eq lzero bool (andb b1 b2) true
true-to-andb-true = λ (b1 : bool) -> match-bool lzero (λ (X-- : bool) -> (b2 : bool) -> (X--1 : eq lzero bool X-- true) -> (X--2 : eq lzero bool b2 true) -> eq lzero bool (andb X-- b2) true) (λ (b2 : bool) -> λ (auto : eq lzero bool true true) -> λ (auto' : eq lzero bool b2 true) -> rewrite-l lzero lzero bool b2 (λ (X-- : bool) -> eq lzero bool b2 X--) (refl lzero bool b2) true auto') (λ (b2 : bool) -> λ (auto : eq lzero bool false true) -> λ (auto' : eq lzero bool b2 true) -> rewrite-r lzero lzero bool b2 (λ (X-- : bool) -> eq lzero bool X-- true) (rewrite-l lzero lzero bool b2 (λ (X-- : bool) -> eq lzero bool b2 X--) (refl lzero bool b2) true auto') false (rewrite-r lzero lzero bool true (λ (X-- : bool) -> eq lzero bool false X--) auto b2 auto')) b1

andb-true-l : (b1 : bool) -> (b2 : bool) -> (X-- : eq lzero bool (andb b1 b2) true) -> eq lzero bool b1 true
andb-true-l = λ (b1 : bool) -> match-bool lzero (λ (X-- : bool) -> (b2 : bool) -> (X--1 : eq lzero bool (andb X-- b2) true) -> eq lzero bool X-- true) (λ (b2 : bool) -> λ (auto : eq lzero bool b2 true) -> rewrite-l lzero lzero bool b2 (λ (X-- : bool) -> eq lzero bool X-- true) (rewrite-l lzero lzero bool b2 (λ (X-- : bool) -> eq lzero bool b2 X--) (refl lzero bool b2) true auto) true auto) (λ (X-b2 : bool) -> λ (auto : eq lzero bool false true) -> rewrite-r lzero lzero bool true (λ (X-- : bool) -> eq lzero bool X-- true) (refl lzero bool true) false auto) b1

andb-true-r : (b1 : bool) -> (b2 : bool) -> (X-- : eq lzero bool (andb b1 b2) true) -> eq lzero bool b2 true
andb-true-r = λ (b1 : bool) -> λ (b2 : bool) -> match-bool lzero (λ (X-- : bool) -> (X--1 : eq lzero bool (andb X-- b2) true) -> eq lzero bool b2 true) (λ (auto : eq lzero bool b2 true) -> rewrite-l lzero lzero bool b2 (λ (X-- : bool) -> eq lzero bool b2 X--) (refl lzero bool b2) true auto) (match-bool lzero (λ (X-- : bool) -> (X--1 : eq lzero bool false true) -> eq lzero bool X-- true) (λ (auto : eq lzero bool false true) -> refl lzero bool true) (λ (auto : eq lzero bool false true) -> rewrite-r lzero lzero bool true (λ (X-- : bool) -> eq lzero bool X-- true) (refl lzero bool true) false auto) b2) b1

andb-true : (b1 : bool) -> (b2 : bool) -> (X-- : eq lzero bool (andb b1 b2) true) -> And lzero lzero (eq lzero bool b1 true) (eq lzero bool b2 true)
andb-true = λ (b1 : bool) -> λ (b2 : bool) -> λ (auto : eq lzero bool (andb b1 b2) true) -> conj lzero lzero (eq lzero bool b1 true) (eq lzero bool b2 true) (andb-true-l b1 b2 (rewrite-r lzero lzero bool true (λ (X-- : bool) -> eq lzero bool X-- true) (refl lzero bool true) (andb b1 b2) auto)) (andb-true-r b1 b2 (rewrite-r lzero lzero bool true (λ (X-- : bool) -> eq lzero bool X-- true) (refl lzero bool true) (andb b1 b2) auto))

orb : (X-- : bool) -> (X--1 : bool) -> bool
orb = λ (b1 : bool) -> λ (b2 : bool) -> match-bool lzero (λ (X-- : bool) -> bool) true b2 b1

orb-elim : (l13 : Level) -> (b1 : bool) -> (b2 : bool) -> (P : (X-- : bool) -> Set l13) -> (X-- : match-bool ((lsuc lzero) ⊔ (lsuc l13)) (λ (X-- : bool) -> Set l13) (P true) (P b2) b1) -> P (orb b1 b2)
orb-elim = λ (l13 : Level) -> λ (b1 : bool) -> λ (b2 : bool) -> λ (P : (X-- : bool) -> Set l13) -> bool-ind l13 (λ (X-x-326 : bool) -> (X-- : match-bool ((lsuc lzero) ⊔ (lsuc l13)) (λ (X-- : bool) -> Set l13) (P true) (P b2) X-x-326) -> P (orb X-x-326 b2)) (λ (auto : P true) -> auto) (λ (auto : P b2) -> auto) b1

orb-true-r1 : (b1 : bool) -> (b2 : bool) -> (X-- : eq lzero bool b1 true) -> eq lzero bool (orb b1 b2) true
orb-true-r1 = λ (b1 : bool) -> λ (b2 : bool) -> λ (H : eq lzero bool b1 true) -> eq-ind-r lzero lzero bool true (λ (x : bool) -> λ (X-- : eq lzero bool x true) -> eq lzero bool (orb x b2) true) (refl lzero bool (orb true b2)) b1 H

orb-true-r2 : (b1 : bool) -> (b2 : bool) -> (X-- : eq lzero bool b2 true) -> eq lzero bool (orb b1 b2) true
orb-true-r2 = λ (b1 : bool) -> λ (b2 : bool) -> λ (H : eq lzero bool b2 true) -> eq-ind-r lzero lzero bool true (λ (x : bool) -> λ (X-- : eq lzero bool x true) -> eq lzero bool (orb b1 x) true) (match-bool lzero (λ (X-- : bool) -> eq lzero bool (orb X-- true) true) (refl lzero bool (orb true true)) (refl lzero bool (orb false true)) b1) b2 H

orb-true-l : (b1 : bool) -> (b2 : bool) -> (X-- : eq lzero bool (orb b1 b2) true) -> Or lzero lzero (eq lzero bool b1 true) (eq lzero bool b2 true)
orb-true-l = λ (X-clearme : bool) -> match-bool lzero (λ (X-- : bool) -> (b2 : bool) -> (X--1 : eq lzero bool (orb X-- b2) true) -> Or lzero lzero (eq lzero bool X-- true) (eq lzero bool b2 true)) (λ (b2 : bool) -> λ (auto : eq lzero bool true true) -> or-introl lzero lzero (eq lzero bool true true) (eq lzero bool b2 true) (refl lzero bool true)) (λ (b2 : bool) -> λ (auto : eq lzero bool b2 true) -> or-intror lzero lzero (eq lzero bool false true) (eq lzero bool b2 true) (rewrite-l lzero lzero bool b2 (λ (X-- : bool) -> eq lzero bool b2 X--) (refl lzero bool b2) true auto)) X-clearme

xorb : (X-- : bool) -> (X--1 : bool) -> bool
xorb = λ (b1 : bool) -> λ (b2 : bool) -> match-bool lzero (λ (X-- : bool) -> bool) (match-bool lzero (λ (X-- : bool) -> bool) false true b2) (match-bool lzero (λ (X-- : bool) -> bool) true false b2) b1

bool-to-decidable-eq : (b1 : bool) -> (b2 : bool) -> decidable lzero (eq lzero bool b1 b2)
bool-to-decidable-eq = λ (b1 : bool) -> λ (b2 : bool) -> match-bool lzero (λ (X-- : bool) -> decidable lzero (eq lzero bool X-- b2)) (match-bool lzero (λ (X-- : bool) -> decidable lzero (eq lzero bool true X--)) (or-introl lzero lzero (eq lzero bool true true) (Not lzero (eq lzero bool true true)) (refl lzero bool true)) (or-intror lzero lzero (eq lzero bool true false) (Not lzero (eq lzero bool true false)) not-eq-true-false) b2) (match-bool lzero (λ (X-- : bool) -> decidable lzero (eq lzero bool false X--)) (or-intror lzero lzero (eq lzero bool false true) (Not lzero (eq lzero bool false true)) (nmk lzero (eq lzero bool false true) (λ (auto : eq lzero bool false true) -> absurd lzero (eq lzero bool true false) (rewrite-r lzero lzero bool true (λ (X-- : bool) -> eq lzero bool true X--) (refl lzero bool true) false auto) not-eq-true-false))) (or-introl lzero lzero (eq lzero bool false false) (Not lzero (eq lzero bool false false)) (refl lzero bool false)) b2) b1

true-or-false : (b : bool) -> Or lzero lzero (eq lzero bool b true) (eq lzero bool b false)
true-or-false = λ (b : bool) -> match-bool lzero (λ (X-- : bool) -> Or lzero lzero (eq lzero bool X-- true) (eq lzero bool X-- false)) (or-introl lzero lzero (eq lzero bool true true) (eq lzero bool true false) (refl lzero bool true)) (RC-reflexive lzero lzero bool (λ (X-- : bool) -> λ (X-0 : bool) -> eq lzero bool false true) false) b

