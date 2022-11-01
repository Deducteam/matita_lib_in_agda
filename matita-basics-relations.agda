open import Agda.Primitive
open import matita-basics-logic
predicate : (l4 l1 : Level) -> (X-- : Set l4) -> Set ((lsuc lzero) ⊔ (l4 ⊔ (lsuc l1)))
predicate = λ (l4 l1 : Level) -> λ (A : Set l4) -> (X-- : A) -> Set l1

relation : (l7 l2 : Level) -> (X-- : Set l7) -> Set ((lsuc lzero) ⊔ (l7 ⊔ (lsuc l2)))
relation = λ (l7 l2 : Level) -> λ (A : Set l7) -> (X-- : A) -> (X--1 : A) -> Set l2

relation2 : (l8 l7 l2 : Level) -> (X-- : Set l8) -> (X--1 : Set l7) -> Set ((lsuc lzero) ⊔ ((l8 ⊔ l7) ⊔ (lsuc l2)))
relation2 = λ (l8 l7 l2 : Level) -> λ (A : Set l8) -> λ (B : Set l7) -> (X-- : A) -> (X--1 : B) -> Set l2

relation3 : (l12 l11 l10 l3 : Level) -> (X-- : Set l12) -> (X--1 : Set l11) -> (X--2 : Set l10) -> Set ((lsuc lzero) ⊔ (((l11 ⊔ (lsuc l3)) ⊔ l10) ⊔ l12))
relation3 = λ (l12 l11 l10 l3 : Level) -> λ (A : Set l12) -> λ (B : Set l11) -> λ (C : Set l10) -> (X-- : A) -> (X--1 : B) -> (X--2 : C) -> Set l3

relation4 : (l16 l15 l14 l13 l4 : Level) -> (X-- : Set l16) -> (X--1 : Set l15) -> (X--2 : Set l14) -> (X--3 : Set l13) -> Set ((lsuc lzero) ⊔ ((((l15 ⊔ l14) ⊔ l13) ⊔ l16) ⊔ (lsuc l4)))
relation4 = λ (l16 l15 l14 l13 l4 : Level) -> λ (A : Set l16) -> λ (B : Set l15) -> λ (C : Set l14) -> λ (D : Set l13) -> (X-- : A) -> (X--1 : B) -> (X--2 : C) -> (X--3 : D) -> Set l4

reflexive : (l6 l3 : Level) -> (A : Set l6) -> (X-R : relation l6 l3 A) -> Set (lzero ⊔ (l6 ⊔ l3))
reflexive = λ (l6 l3 : Level) -> λ (A : Set l6) -> λ (R : relation l6 l3 A) -> (x : A) -> R x x

symmetric : (l12 l9 : Level) -> (A : Set l12) -> (X-R : relation l12 l9 A) -> Set (lzero ⊔ (l9 ⊔ l12))
symmetric = λ (l12 l9 : Level) -> λ (A : Set l12) -> λ (R : relation l12 l9 A) -> (x : A) -> (y : A) -> (X-- : R x y) -> R y x

transitive : (l18 l15 : Level) -> (A : Set l18) -> (X-R : relation l18 l15 A) -> Set (lzero ⊔ (l18 ⊔ l15))
transitive = λ (l18 l15 : Level) -> λ (A : Set l18) -> λ (R : relation l18 l15 A) -> (x : A) -> (y : A) -> (z : A) -> (X-- : R x y) -> (X--1 : R y z) -> R x z

irreflexive : (l7 l4 : Level) -> (A : Set l7) -> (X-R : relation l7 l4 A) -> Set (lzero ⊔ (l7 ⊔ l4))
irreflexive = λ (l7 l4 : Level) -> λ (A : Set l7) -> λ (R : relation l7 l4 A) -> (x : A) -> Not l4 (R x x)

cotransitive : (l17 l14 : Level) -> (A : Set l17) -> (X-R : relation l17 l14 A) -> Set (lzero ⊔ (l17 ⊔ l14))
cotransitive = λ (l17 l14 : Level) -> λ (A : Set l17) -> λ (R : relation l17 l14 A) -> (x : A) -> (y : A) -> (X-- : R x y) -> (z : A) -> Or l14 l14 (R x z) (R z y)

tight-apart : (l23 l20 l17 : Level) -> (A : Set l23) -> (X-eq : relation l23 l20 A) -> (X-ap : relation l23 l17 A) -> Set (lzero ⊔ ((l23 ⊔ l20) ⊔ l17))
tight-apart = λ (l23 l20 l17 : Level) -> λ (A : Set l23) -> λ (eq-v : relation l23 l20 A) -> λ (ap : relation l23 l17 A) -> (x : A) -> (y : A) -> And (l20 ⊔ l17) (l20 ⊔ l17) ((X-- : Not l17 (ap x y)) -> eq-v x y) ((X-- : eq-v x y) -> Not l17 (ap x y))

antisymmetric : (l13 l10 : Level) -> (A : Set l13) -> (X-R : relation l13 l10 A) -> Set (lzero ⊔ (l13 ⊔ l10))
antisymmetric = λ (l13 l10 : Level) -> λ (A : Set l13) -> λ (R : relation l13 l10 A) -> (x : A) -> (y : A) -> (X-- : R x y) -> Not l10 (R y x)

singlevalued : (l21 l20 l17 : Level) -> (A : Set l21) -> (B : Set l20) -> predicate ((lsuc lzero) ⊔ (((lsuc l17) ⊔ l20) ⊔ l21)) ((l17 ⊔ l20) ⊔ l21) (relation2 l21 l20 l17 A B)
singlevalued = λ (l21 l20 l17 : Level) -> λ (A : Set l21) -> λ (B : Set l20) -> λ (R : relation2 l21 l20 l17 A B) -> (a : A) -> (b1 : B) -> (X-- : R a b1) -> (b2 : B) -> (X--1 : R a b2) -> eq l20 B b1 b2

confluent1 : (l21 l18 : Level) -> (A : Set l21) -> (X-- : relation l21 l18 A) -> predicate l21 (l21 ⊔ l18) A
confluent1 = λ (l21 l18 : Level) -> λ (A : Set l21) -> λ (R : relation l21 l18 A) -> λ (a0 : A) -> (a1 : A) -> (X-- : R a0 a1) -> (a2 : A) -> (X--1 : R a0 a2) -> ex2 l21 l18 l18 A (λ (a : A) -> R a1 a) (λ (a : A) -> R a2 a)

confluent : (l8 l5 : Level) -> (A : Set l8) -> predicate ((lsuc lzero) ⊔ (l8 ⊔ (lsuc l5))) (l8 ⊔ l5) (relation l8 l5 A)
confluent = λ (l8 l5 : Level) -> λ (A : Set l8) -> λ (R : relation l8 l5 A) -> (a0 : A) -> confluent1 l8 l5 A R a0

Conf3 : (l23 l22 l19 l15 : Level) -> (A : Set l23) -> (B : Set l22) -> (X-- : relation2 l23 l22 l19 A B) -> (X--1 : relation l23 l15 A) -> Set (lzero ⊔ (((l19 ⊔ l23) ⊔ l15) ⊔ l22))
Conf3 = λ (l23 l22 l19 l15 : Level) -> λ (A : Set l23) -> λ (B : Set l22) -> λ (S : relation2 l23 l22 l19 A B) -> λ (R : relation l23 l15 A) -> (b : B) -> (a1 : A) -> (X-- : S a1 b) -> (a2 : A) -> (X--1 : R a1 a2) -> S a2 b

RC : (l8 l5 : Level) -> (A : Set l8) -> (X-- : relation l8 l5 A) -> relation l8 (l8 ⊔ l5) A
RC = λ (l8 l5 : Level) -> λ (A : Set l8) -> λ (R : relation l8 l5 A) -> λ (x : A) -> λ (y : A) -> Or l5 l8 (R x y) (eq l8 A x y)

RC-reflexive : (l8 l5 : Level) -> (A : Set l8) -> (R : relation l8 l5 A) -> reflexive l8 (l8 ⊔ l5) A (RC l8 l5 A R)
RC-reflexive = λ (l8 l5 : Level) -> λ (A : Set l8) -> λ (R : relation l8 l5 A) -> λ (x : A) -> or-intror l5 l8 (R x x) (eq l8 A x x) (refl l8 A x)

Rcomp : (l13 l10 l7 : Level) -> (A : Set l13) -> (X-R1 : relation l13 l10 A) -> (X-R2 : relation l13 l7 A) -> (X-a1 : A) -> (X-a2 : A) -> Set (lzero ⊔ ((l7 ⊔ l13) ⊔ l10))
Rcomp = λ (l13 l10 l7 : Level) -> λ (A : Set l13) -> λ (R1-v : relation l13 l10 A) -> λ (R2-v : relation l13 l7 A) -> λ (a1 : A) -> λ (a2 : A) -> ex l13 (l7 ⊔ l10) A (λ (am : A) -> And l10 l7 (R1-v a1 am) (R2-v am a2))

Runion : (l10 l7 l4 : Level) -> (A : Set l10) -> (X-R1 : relation l10 l7 A) -> (X-R2 : relation l10 l4 A) -> (X-a : A) -> (X-b : A) -> Set (lzero ⊔ (l7 ⊔ l4))
Runion = λ (l10 l7 l4 : Level) -> λ (A : Set l10) -> λ (R1-v : relation l10 l7 A) -> λ (R2-v : relation l10 l4 A) -> λ (a : A) -> λ (b : A) -> Or l7 l4 (R1-v a b) (R2-v a b)

Rintersection : (l10 l7 l4 : Level) -> (A : Set l10) -> (X-R1 : relation l10 l7 A) -> (X-R2 : relation l10 l4 A) -> (X-a : A) -> (X-b : A) -> Set (lzero ⊔ (l7 ⊔ l4))
Rintersection = λ (l10 l7 l4 : Level) -> λ (A : Set l10) -> λ (R1-v : relation l10 l7 A) -> λ (R2-v : relation l10 l4 A) -> λ (a : A) -> λ (b : A) -> And l7 l4 (R1-v a b) (R2-v a b)

inv : (l5 l2 : Level) -> (A : Set l5) -> (X-R : relation l5 l2 A) -> (X-a : A) -> (X-b : A) -> Set l2
inv = λ (l5 l2 : Level) -> λ (A : Set l5) -> λ (R : relation l5 l2 A) -> λ (a : A) -> λ (b : A) -> R b a

subR : (l15 l12 l9 : Level) -> (A : Set l15) -> (X-R : relation l15 l12 A) -> (X-S : relation l15 l9 A) -> Set (lzero ⊔ ((l9 ⊔ l15) ⊔ l12))
subR = λ (l15 l12 l9 : Level) -> λ (A : Set l15) -> λ (R : relation l15 l12 A) -> λ (S : relation l15 l9 A) -> (a : A) -> (b : A) -> (X-- : R a b) -> S a b

sub-reflexive : (l6 l3 : Level) -> (T : Set l6) -> (R : relation l6 l3 T) -> subR l6 l3 l3 T R R
sub-reflexive = λ (l6 l3 : Level) -> λ (T : Set l6) -> λ (R : relation l6 l3 T) -> λ (x : T) -> λ (b : T) -> λ (auto : R x b) -> auto

sub-comp-l : (l56 l53 l50 l47 : Level) -> (A : Set l56) -> (R : relation l56 l53 A) -> (R1-v : relation l56 l50 A) -> (R2-v : relation l56 l47 A) -> (X-- : subR l56 l50 l47 A R1-v R2-v) -> subR l56 ((l50 ⊔ l53) ⊔ l56) ((l47 ⊔ l53) ⊔ l56) A (Rcomp l56 l50 l53 A R1-v R) (Rcomp l56 l47 l53 A R2-v R)
sub-comp-l = λ (l56 l53 l50 l47 : Level) -> λ (A : Set l56) -> λ (R : relation l56 l53 A) -> λ (R1-v : relation l56 l50 A) -> λ (R2-v : relation l56 l47 A) -> λ (Hsub : subR l56 l50 l47 A R1-v R2-v) -> λ (a : A) -> λ (b : A) -> λ (X-clearme : Rcomp l56 l50 l53 A R1-v R a b) -> match-ex l56 (l53 ⊔ l50) A (λ (am : A) -> And l50 l53 (R1-v a am) (R am b)) ((l56 ⊔ l53) ⊔ l47) (λ (X-- : ex l56 (l53 ⊔ l50) A (λ (am : A) -> And l50 l53 (R1-v a am) (R am b))) -> Rcomp l56 l47 l53 A R2-v R a b) (λ (c : A) -> λ (X-clearme0 : And l50 l53 (R1-v a c) (R c b)) -> match-And l50 l53 (R1-v a c) (R c b) ((l56 ⊔ l53) ⊔ l47) (λ (X-- : And l50 l53 (R1-v a c) (R c b)) -> Rcomp l56 l47 l53 A R2-v R a b) (λ (auto : R1-v a c) -> λ (auto' : R c b) -> ex-intro l56 (l53 ⊔ l47) A (λ (am : A) -> And l47 l53 (R2-v a am) (R am b)) c (conj l47 l53 (R2-v a c) (R c b) (Hsub a c auto) auto')) X-clearme0) X-clearme

sub-comp-r : (l56 l53 l50 l47 : Level) -> (A : Set l56) -> (R : relation l56 l53 A) -> (R1-v : relation l56 l50 A) -> (R2-v : relation l56 l47 A) -> (X-- : subR l56 l50 l47 A R1-v R2-v) -> subR l56 ((l50 ⊔ l53) ⊔ l56) ((l47 ⊔ l53) ⊔ l56) A (Rcomp l56 l53 l50 A R R1-v) (Rcomp l56 l53 l47 A R R2-v)
sub-comp-r = λ (l56 l53 l50 l47 : Level) -> λ (A : Set l56) -> λ (R : relation l56 l53 A) -> λ (R1-v : relation l56 l50 A) -> λ (R2-v : relation l56 l47 A) -> λ (Hsub : subR l56 l50 l47 A R1-v R2-v) -> λ (a : A) -> λ (b : A) -> λ (X-clearme : Rcomp l56 l53 l50 A R R1-v a b) -> match-ex l56 (l53 ⊔ l50) A (λ (am : A) -> And l53 l50 (R a am) (R1-v am b)) ((l56 ⊔ l53) ⊔ l47) (λ (X-- : ex l56 (l53 ⊔ l50) A (λ (am : A) -> And l53 l50 (R a am) (R1-v am b))) -> Rcomp l56 l53 l47 A R R2-v a b) (λ (c : A) -> λ (X-clearme0 : And l53 l50 (R a c) (R1-v c b)) -> match-And l53 l50 (R a c) (R1-v c b) ((l56 ⊔ l53) ⊔ l47) (λ (X-- : And l53 l50 (R a c) (R1-v c b)) -> Rcomp l56 l53 l47 A R R2-v a b) (λ (auto : R a c) -> λ (auto' : R1-v c b) -> ex-intro l56 (l53 ⊔ l47) A (λ (am : A) -> And l53 l47 (R a am) (R2-v am b)) c (conj l53 l47 (R a c) (R2-v c b) auto (Hsub c b auto'))) X-clearme0) X-clearme

sub-assoc-l : (l128 l125 l122 l119 : Level) -> (A : Set l128) -> (R1-v : relation l128 l125 A) -> (R2-v : relation l128 l122 A) -> (R3-v : relation l128 l119 A) -> subR l128 (((l122 ⊔ l125) ⊔ l128) ⊔ l119) (((l122 ⊔ l125) ⊔ l128) ⊔ l119) A (Rcomp l128 l125 ((l128 ⊔ l122) ⊔ l119) A R1-v (Rcomp l128 l122 l119 A R2-v R3-v)) (Rcomp l128 ((l128 ⊔ l125) ⊔ l122) l119 A (Rcomp l128 l125 l122 A R1-v R2-v) R3-v)
sub-assoc-l = λ (l128 l125 l122 l119 : Level) -> λ (A : Set l128) -> λ (R1-v : relation l128 l125 A) -> λ (R2-v : relation l128 l122 A) -> λ (R3-v : relation l128 l119 A) -> λ (a : A) -> λ (b : A) -> λ (X-clearme : Rcomp l128 l125 ((l119 ⊔ l122) ⊔ l128) A R1-v (Rcomp l128 l122 l119 A R2-v R3-v) a b) -> match-ex l128 (((l122 ⊔ l128) ⊔ l119) ⊔ l125) A (λ (am : A) -> And l125 ((l128 ⊔ l122) ⊔ l119) (R1-v a am) (Rcomp l128 l122 l119 A R2-v R3-v am b)) (((l122 ⊔ l128) ⊔ l119) ⊔ l125) (λ (X-- : ex l128 (((l122 ⊔ l125) ⊔ l128) ⊔ l119) A (λ (am : A) -> And l125 ((l128 ⊔ l122) ⊔ l119) (R1-v a am) (Rcomp l128 l122 l119 A R2-v R3-v am b))) -> Rcomp l128 ((l128 ⊔ l125) ⊔ l122) l119 A (Rcomp l128 l125 l122 A R1-v R2-v) R3-v a b) (λ (c : A) -> λ (X-clearme0 : And l125 ((l119 ⊔ l122) ⊔ l128) (R1-v a c) (Rcomp l128 l122 l119 A R2-v R3-v c b)) -> match-And l125 ((l128 ⊔ l122) ⊔ l119) (R1-v a c) (Rcomp l128 l122 l119 A R2-v R3-v c b) (((l122 ⊔ l128) ⊔ l119) ⊔ l125) (λ (X-- : And l125 ((l119 ⊔ l122) ⊔ l128) (R1-v a c) (Rcomp l128 l122 l119 A R2-v R3-v c b)) -> Rcomp l128 ((l128 ⊔ l125) ⊔ l122) l119 A (Rcomp l128 l125 l122 A R1-v R2-v) R3-v a b) (λ (Hac : R1-v a c) -> λ (X-clearme1 : Rcomp l128 l122 l119 A R2-v R3-v c b) -> match-ex l128 (l122 ⊔ l119) A (λ (am : A) -> And l122 l119 (R2-v c am) (R3-v am b)) (((l122 ⊔ l128) ⊔ l119) ⊔ l125) (λ (X-- : ex l128 (l122 ⊔ l119) A (λ (am : A) -> And l122 l119 (R2-v c am) (R3-v am b))) -> Rcomp l128 ((l128 ⊔ l125) ⊔ l122) l119 A (Rcomp l128 l125 l122 A R1-v R2-v) R3-v a b) (λ (d : A) -> λ (X-clearme2 : And l122 l119 (R2-v c d) (R3-v d b)) -> match-And l122 l119 (R2-v c d) (R3-v d b) (((l122 ⊔ l128) ⊔ l119) ⊔ l125) (λ (X-- : And l122 l119 (R2-v c d) (R3-v d b)) -> Rcomp l128 ((l128 ⊔ l125) ⊔ l122) l119 A (Rcomp l128 l125 l122 A R1-v R2-v) R3-v a b) (λ (auto : R2-v c d) -> λ (auto' : R3-v d b) -> ex-intro l128 (((l122 ⊔ l128) ⊔ l119) ⊔ l125) A (λ (am : A) -> And ((l128 ⊔ l125) ⊔ l122) l119 (Rcomp l128 l125 l122 A R1-v R2-v a am) (R3-v am b)) d (conj ((l122 ⊔ l125) ⊔ l128) l119 (Rcomp l128 l125 l122 A R1-v R2-v a d) (R3-v d b) (ex-intro l128 (l125 ⊔ l122) A (λ (am : A) -> And l125 l122 (R1-v a am) (R2-v am d)) c (conj l125 l122 (R1-v a c) (R2-v c d) Hac auto)) auto')) X-clearme2) X-clearme1) X-clearme0) X-clearme

sub-assoc-r : (l134 l131 l128 l125 : Level) -> (A : Set l134) -> (R1-v : relation l134 l131 A) -> (R2-v : relation l134 l128 A) -> (R3-v : relation l134 l125 A) -> subR l134 (((l128 ⊔ l131) ⊔ l134) ⊔ l125) (((l128 ⊔ l131) ⊔ l134) ⊔ l125) A (Rcomp l134 ((l134 ⊔ l131) ⊔ l128) l125 A (Rcomp l134 l131 l128 A R1-v R2-v) R3-v) (Rcomp l134 l131 ((l134 ⊔ l128) ⊔ l125) A R1-v (Rcomp l134 l128 l125 A R2-v R3-v))
sub-assoc-r = λ (l134 l131 l128 l125 : Level) -> λ (A : Set l134) -> λ (R1-v : relation l134 l131 A) -> λ (R2-v : relation l134 l128 A) -> λ (R3-v : relation l134 l125 A) -> λ (a : A) -> λ (b : A) -> λ (X-clearme : Rcomp l134 ((l128 ⊔ l131) ⊔ l134) l125 A (Rcomp l134 l131 l128 A R1-v R2-v) R3-v a b) -> match-ex l134 (((l128 ⊔ l134) ⊔ l125) ⊔ l131) A (λ (am : A) -> And ((l134 ⊔ l131) ⊔ l128) l125 (Rcomp l134 l131 l128 A R1-v R2-v a am) (R3-v am b)) (((l128 ⊔ l134) ⊔ l125) ⊔ l131) (λ (X-- : ex l134 (((l128 ⊔ l131) ⊔ l134) ⊔ l125) A (λ (am : A) -> And ((l134 ⊔ l131) ⊔ l128) l125 (Rcomp l134 l131 l128 A R1-v R2-v a am) (R3-v am b))) -> Rcomp l134 l131 ((l134 ⊔ l128) ⊔ l125) A R1-v (Rcomp l134 l128 l125 A R2-v R3-v) a b) (λ (c : A) -> λ (X-clearme0 : And ((l128 ⊔ l131) ⊔ l134) l125 (Rcomp l134 l131 l128 A R1-v R2-v a c) (R3-v c b)) -> match-And ((l134 ⊔ l131) ⊔ l128) l125 (Rcomp l134 l131 l128 A R1-v R2-v a c) (R3-v c b) (((l128 ⊔ l134) ⊔ l125) ⊔ l131) (λ (X-- : And ((l128 ⊔ l131) ⊔ l134) l125 (Rcomp l134 l131 l128 A R1-v R2-v a c) (R3-v c b)) -> Rcomp l134 l131 ((l134 ⊔ l128) ⊔ l125) A R1-v (Rcomp l134 l128 l125 A R2-v R3-v) a b) (λ (X-clearme1 : Rcomp l134 l131 l128 A R1-v R2-v a c) -> match-ex l134 (l131 ⊔ l128) A (λ (am : A) -> And l131 l128 (R1-v a am) (R2-v am c)) (((l128 ⊔ l134) ⊔ l125) ⊔ l131) (λ (X-- : ex l134 (l131 ⊔ l128) A (λ (am : A) -> And l131 l128 (R1-v a am) (R2-v am c))) -> (X--1 : R3-v c b) -> Rcomp l134 l131 ((l134 ⊔ l128) ⊔ l125) A R1-v (Rcomp l134 l128 l125 A R2-v R3-v) a b) (λ (d : A) -> λ (X-clearme2 : And l131 l128 (R1-v a d) (R2-v d c)) -> match-And l131 l128 (R1-v a d) (R2-v d c) (((l128 ⊔ l134) ⊔ l125) ⊔ l131) (λ (X-- : And l131 l128 (R1-v a d) (R2-v d c)) -> (X--1 : R3-v c b) -> Rcomp l134 l131 ((l134 ⊔ l128) ⊔ l125) A R1-v (Rcomp l134 l128 l125 A R2-v R3-v) a b) (λ (auto : R1-v a d) -> λ (auto' : R2-v d c) -> λ (auto'' : R3-v c b) -> ex-intro l134 (((l128 ⊔ l134) ⊔ l125) ⊔ l131) A (λ (am : A) -> And l131 ((l134 ⊔ l128) ⊔ l125) (R1-v a am) (Rcomp l134 l128 l125 A R2-v R3-v am b)) d (conj l131 ((l125 ⊔ l128) ⊔ l134) (R1-v a d) (Rcomp l134 l128 l125 A R2-v R3-v d b) auto (ex-intro l134 (l128 ⊔ l125) A (λ (am : A) -> And l128 l125 (R2-v d am) (R3-v am b)) c (conj l128 l125 (R2-v d c) (R3-v c b) auto' auto'')))) X-clearme2) X-clearme1) X-clearme0) X-clearme

compose : (l7 l6 l5 : Level) -> (A : Set l7) -> (B : Set l6) -> (C : Set l5) -> (X-f : (X-- : B) -> C) -> (X-g : (X-- : A) -> B) -> (X-x : A) -> C
compose = λ (l7 l6 l5 : Level) -> λ (A : Set l7) -> λ (B : Set l6) -> λ (C : Set l5) -> λ (f : (X-- : B) -> C) -> λ (g : (X-- : A) -> B) -> λ (x : A) -> f (g x)

||injective|| : (l15 l14 : Level) -> (A : Set l15) -> (B : Set l14) -> (X-f : (X-- : A) -> B) -> Set (lzero ⊔ (l15 ⊔ l14))
||injective|| = λ (l15 l14 : Level) -> λ (A : Set l15) -> λ (B : Set l14) -> λ (f : (X-- : A) -> B) -> (x : A) -> (y : A) -> (X-- : eq l14 B (f x) (f y)) -> eq l15 A x y

surjective : (l10 l9 : Level) -> (A : Set l10) -> (B : Set l9) -> (X-f : (X-- : A) -> B) -> Set (lzero ⊔ (l9 ⊔ l10))
surjective = λ (l10 l9 : Level) -> λ (A : Set l10) -> λ (B : Set l9) -> λ (f : (X-- : A) -> B) -> (z : B) -> ex l10 l9 A (λ (x : A) -> eq l9 B z (f x))

commutative : (l10 : Level) -> (A : Set l10) -> (X-f : (X-- : A) -> (X--1 : A) -> A) -> Set l10
commutative = λ (l10 : Level) -> λ (A : Set l10) -> λ (f : (X-- : A) -> (X--1 : A) -> A) -> (x : A) -> (y : A) -> eq l10 A (f x y) (f y x)

commutative2 : (l11 l10 : Level) -> (A : Set l11) -> (B : Set l10) -> (X-f : (X-- : A) -> (X--1 : A) -> B) -> Set (lzero ⊔ (l11 ⊔ l10))
commutative2 = λ (l11 l10 : Level) -> λ (A : Set l11) -> λ (B : Set l10) -> λ (f : (X-- : A) -> (X--1 : A) -> B) -> (x : A) -> (y : A) -> eq l10 B (f x y) (f y x)

associative : (l13 : Level) -> (A : Set l13) -> (X-f : (X-- : A) -> (X--1 : A) -> A) -> Set l13
associative = λ (l13 : Level) -> λ (A : Set l13) -> λ (f : (X-- : A) -> (X--1 : A) -> A) -> (x : A) -> (y : A) -> (z : A) -> eq l13 A (f (f x y) z) (f x (f y z))

monotonic : (l14 l11 : Level) -> (A : Set l14) -> (X-R : (X-- : A) -> (X--1 : A) -> Set l11) -> (X-f : (X-- : A) -> A) -> Set (lzero ⊔ (l14 ⊔ l11))
monotonic = λ (l14 l11 : Level) -> λ (A : Set l14) -> λ (R : (X-- : A) -> (X--1 : A) -> Set l11) -> λ (f : (X-- : A) -> A) -> (x : A) -> (y : A) -> (X-- : R x y) -> R (f x) (f y)

distributive : (l16 : Level) -> (A : Set l16) -> (X-f : (X-- : A) -> (X--1 : A) -> A) -> (X-g : (X-- : A) -> (X--1 : A) -> A) -> Set l16
distributive = λ (l16 : Level) -> λ (A : Set l16) -> λ (f : (X-- : A) -> (X--1 : A) -> A) -> λ (g : (X-- : A) -> (X--1 : A) -> A) -> (x : A) -> (y : A) -> (z : A) -> eq l16 A (f x (g y z)) (g (f x y) (f x z))

distributive2 : (l17 l16 : Level) -> (A : Set l17) -> (B : Set l16) -> (X-f : (X-- : A) -> (X--1 : B) -> B) -> (X-g : (X-- : B) -> (X--1 : B) -> B) -> Set (lzero ⊔ (l17 ⊔ l16))
distributive2 = λ (l17 l16 : Level) -> λ (A : Set l17) -> λ (B : Set l16) -> λ (f : (X-- : A) -> (X--1 : B) -> B) -> λ (g : (X-- : B) -> (X--1 : B) -> B) -> (x : A) -> (y : B) -> (z : B) -> eq l16 B (f x (g y z)) (g (f x y) (f x z))

injective-compose : (l23 l20 l19 : Level) -> (A : Set l23) -> (B : Set l20) -> (C : Set l19) -> (f : (X-- : A) -> B) -> (g : (X-- : B) -> C) -> (X-- : ||injective|| l23 l20 A B f) -> (X--1 : ||injective|| l20 l19 B C g) -> ||injective|| l23 l19 A C (λ (x : A) -> g (f x))
injective-compose = λ (l23 l20 l19 : Level) -> λ (A : Set l23) -> λ (B : Set l20) -> λ (C : Set l19) -> λ (f : (X-- : A) -> B) -> λ (g : (X-- : B) -> C) -> λ (auto : ||injective|| l23 l20 A B f) -> λ (auto' : ||injective|| l20 l19 B C g) -> λ (x : A) -> λ (y : A) -> λ (auto'' : eq l19 C (g (f x)) (g (f y))) -> auto x y (auto' (f x) (f y) (rewrite-l l19 l19 C (g (f x)) (λ (X-- : C) -> eq l19 C (g (f x)) X--) (refl l19 C (g (f x))) (g (f y)) auto''))

exteqR : (l15 l14 l11 l8 : Level) -> (A : Set l15) -> (B : Set l14) -> (X-R : (X-- : A) -> (X--1 : B) -> Set l11) -> (X-S : (X-- : A) -> (X--1 : B) -> Set l8) -> Set (lzero ⊔ (((l14 ⊔ l8) ⊔ l11) ⊔ l15))
exteqR = λ (l15 l14 l11 l8 : Level) -> λ (A : Set l15) -> λ (B : Set l14) -> λ (R : (X-- : A) -> (X--1 : B) -> Set l11) -> λ (S : (X-- : A) -> (X--1 : B) -> Set l8) -> (a : A) -> (b : B) -> iff l11 l8 (R a b) (S a b)

exteqF : (l9 l8 : Level) -> (A : Set l9) -> (B : Set l8) -> (X-f : (X-- : A) -> B) -> (X-g : (X-- : A) -> B) -> Set (lzero ⊔ (l9 ⊔ l8))
exteqF = λ (l9 l8 : Level) -> λ (A : Set l9) -> λ (B : Set l8) -> λ (f : (X-- : A) -> B) -> λ (g : (X-- : A) -> B) -> (a : A) -> eq l8 B (f a) (g a)

bi-relation : (l14 l13 l4 : Level) -> (X-- : Set l14) -> (X--1 : Set l13) -> Set ((lsuc lzero) ⊔ (((lsuc l4) ⊔ l14) ⊔ l13))
bi-relation = λ (l14 l13 l4 : Level) -> λ (A : Set l14) -> λ (B : Set l13) -> (X-- : A) -> (X--1 : B) -> (X--2 : A) -> (X--3 : B) -> Set l4

bi-reflexive : (l11 l10 l7 : Level) -> (A : Set l11) -> (B : Set l10) -> (X-R : bi-relation l11 l10 l7 A B) -> Set (lzero ⊔ ((l7 ⊔ l11) ⊔ l10))
bi-reflexive = λ (l11 l10 l7 : Level) -> λ (A : Set l11) -> λ (B : Set l10) -> λ (R : bi-relation l11 l10 l7 A B) -> (a : A) -> (b : B) -> R a b a b

bi-symmetric : (l20 l19 l16 : Level) -> (A : Set l20) -> (B : Set l19) -> (X-R : bi-relation l20 l19 l16 A B) -> Set (lzero ⊔ ((l20 ⊔ l19) ⊔ l16))
bi-symmetric = λ (l20 l19 l16 : Level) -> λ (A : Set l20) -> λ (B : Set l19) -> λ (R : bi-relation l20 l19 l16 A B) -> (a1 : A) -> (a2 : A) -> (b1 : B) -> (b2 : B) -> (X-- : R a2 b2 a1 b1) -> R a1 b1 a2 b2

bi-transitive : (l29 l28 l25 : Level) -> (A : Set l29) -> (B : Set l28) -> (X-R : bi-relation l29 l28 l25 A B) -> Set (lzero ⊔ ((l29 ⊔ l28) ⊔ l25))
bi-transitive = λ (l29 l28 l25 : Level) -> λ (A : Set l29) -> λ (B : Set l28) -> λ (R : bi-relation l29 l28 l25 A B) -> (a1 : A) -> (a : A) -> (b1 : B) -> (b : B) -> (X-- : R a1 b1 a b) -> (a2 : A) -> (b2 : B) -> (X--1 : R a b a2 b2) -> R a1 b1 a2 b2

bi-RC : (l15 l14 l11 : Level) -> (A : Set l15) -> (B : Set l14) -> (X-- : bi-relation l15 l14 l11 A B) -> bi-relation l15 l14 ((l11 ⊔ l14) ⊔ l15) A B
bi-RC = λ (l15 l14 l11 : Level) -> λ (A : Set l15) -> λ (B : Set l14) -> λ (R : bi-relation l15 l14 l11 A B) -> λ (a1 : A) -> λ (b1 : B) -> λ (a2 : A) -> λ (b2 : B) -> Or l11 (l15 ⊔ l14) (R a1 b1 a2 b2) (And l15 l14 (eq l15 A a1 a2) (eq l14 B b1 b2))

bi-RC-reflexive : (l19 l18 l15 : Level) -> (A : Set l19) -> (B : Set l18) -> (R : bi-relation l19 l18 l15 A B) -> bi-reflexive l19 l18 ((l15 ⊔ l18) ⊔ l19) A B (bi-RC l19 l18 l15 A B R)
bi-RC-reflexive = λ (l19 l18 l15 : Level) -> λ (A : Set l19) -> λ (B : Set l18) -> λ (R : bi-relation l19 l18 l15 A B) -> λ (a : A) -> λ (b : B) -> or-intror l15 (l19 ⊔ l18) (R a b a b) (And l19 l18 (eq l19 A a a) (eq l18 B b b)) (conj l19 l18 (eq l19 A a a) (eq l18 B b b) (refl l19 A a) (refl l18 B b))

tri-relation : (l21 l20 l19 l6 : Level) -> (X-- : Set l21) -> (X--1 : Set l20) -> (X--2 : Set l19) -> Set ((lsuc lzero) ⊔ (((l20 ⊔ (lsuc l6)) ⊔ l19) ⊔ l21))
tri-relation = λ (l21 l20 l19 l6 : Level) -> λ (A : Set l21) -> λ (B : Set l20) -> λ (C : Set l19) -> (X-- : A) -> (X--1 : B) -> (X--2 : C) -> (X--3 : A) -> (X--4 : B) -> (X--5 : C) -> Set l6

tri-reflexive : (l16 l15 l14 l11 : Level) -> (A : Set l16) -> (B : Set l15) -> (C : Set l14) -> (X-R : tri-relation l16 l15 l14 l11 A B C) -> Set (lzero ⊔ (((l14 ⊔ l16) ⊔ l11) ⊔ l15))
tri-reflexive = λ (l16 l15 l14 l11 : Level) -> λ (A : Set l16) -> λ (B : Set l15) -> λ (C : Set l14) -> λ (R : tri-relation l16 l15 l14 l11 A B C) -> (a : A) -> (b : B) -> (c : C) -> R a b c a b c

tri-symmetric : (l28 l27 l26 l23 : Level) -> (A : Set l28) -> (B : Set l27) -> (C : Set l26) -> (X-R : tri-relation l28 l27 l26 l23 A B C) -> Set (lzero ⊔ (((l26 ⊔ l28) ⊔ l23) ⊔ l27))
tri-symmetric = λ (l28 l27 l26 l23 : Level) -> λ (A : Set l28) -> λ (B : Set l27) -> λ (C : Set l26) -> λ (R : tri-relation l28 l27 l26 l23 A B C) -> (a1 : A) -> (a2 : A) -> (b1 : B) -> (b2 : B) -> (c1 : C) -> (c2 : C) -> (X-- : R a2 b2 c2 a1 b1 c1) -> R a1 b1 c1 a2 b2 c2

tri-transitive : (l40 l39 l38 l35 : Level) -> (A : Set l40) -> (B : Set l39) -> (C : Set l38) -> (X-R : tri-relation l40 l39 l38 l35 A B C) -> Set (lzero ⊔ (((l38 ⊔ l40) ⊔ l35) ⊔ l39))
tri-transitive = λ (l40 l39 l38 l35 : Level) -> λ (A : Set l40) -> λ (B : Set l39) -> λ (C : Set l38) -> λ (R : tri-relation l40 l39 l38 l35 A B C) -> (a1 : A) -> (a : A) -> (b1 : B) -> (b : B) -> (c1 : C) -> (c : C) -> (X-- : R a1 b1 c1 a b c) -> (a2 : A) -> (b2 : B) -> (c2 : C) -> (X--1 : R a b c a2 b2 c2) -> R a1 b1 c1 a2 b2 c2

