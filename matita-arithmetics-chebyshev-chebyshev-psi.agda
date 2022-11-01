open import Agda.Primitive
open import matita-arithmetics-div-and-mod
open import matita-arithmetics-exp
open import matita-arithmetics-bigops
open import matita-arithmetics-sigma-pi
open import matita-arithmetics-log
open import matita-basics-logic
open import matita-arithmetics-primes
open import matita-basics-bool
open import matita-arithmetics-nat
prim : (X-n : nat) -> nat
prim = λ (n : nat) -> bigop (S n) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)

le-prim-n : (n : nat) -> le (prim n) n
le-prim-n = λ (n : nat) -> nat-ind lzero (λ (X-x-365 : nat) -> le (prim X-x-365) X-x-365) (le-n (prim O)) (λ (n0 : nat) -> λ (H : le (prim n0) n0) -> match-bool lzero (λ (X-- : bool) -> le (match-bool lzero (λ (X-0 : bool) -> nat) (plus (S O) (bigop (S n0) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (bigop (S n0) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)) X--) (S n0)) (le-S-S (plus O (bigop (S n0) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) n0 H) (le-S (match-bool lzero (λ (X-- : bool) -> nat) (plus (S O) (bigop n0 (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (bigop n0 (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)) (primeb n0)) n0 H) (primeb (S n0))) n

let-clause-1033''' : (n : nat) -> (ltn : lt (S O) n) -> (X-clearme : prime (times (S (S O)) n)) -> (H : lt (S O) (times (S (S O)) n)) -> (H1 : (m : nat) -> (X-- : divides m (times (S (S O)) n)) -> (X--1 : lt (S O) m) -> eq lzero nat m (times (S (S O)) n)) -> (x2515 : nat) -> (x2516 : nat) -> eq lzero nat x2515 (plus (times x2516 (div x2515 x2516)) (mod x2515 x2516))
let-clause-1033''' = λ (n : nat) -> λ (ltn : lt (S O) n) -> λ (X-clearme : prime (times (S (S O)) n)) -> λ (H : lt (S O) (times (S (S O)) n)) -> λ (H1 : (m : nat) -> (X-- : divides m (times (S (S O)) n)) -> (X--1 : lt (S O) m) -> eq lzero nat m (times (S (S O)) n)) -> λ (x2515 : nat) -> λ (x2516 : nat) -> rewrite-l lzero lzero nat (times (div x2515 x2516) x2516) (λ (X-- : nat) -> eq lzero nat x2515 (plus X-- (mod x2515 x2516))) (div-mod x2515 x2516) (times x2516 (div x2515 x2516)) (commutative-times (div x2515 x2516) x2516)

not-prime-times-2 : (n : nat) -> (X-- : lt (S O) n) -> Not lzero (prime (times (S (S O)) n))
not-prime-times-2 = λ (n : nat) -> λ (ltn : lt (S O) n) -> nmk lzero (prime (times (S (S O)) n)) (λ (X-clearme : prime (times (S (S O)) n)) -> match-And lzero lzero (lt (S O) (times (S (S O)) n)) ((m : nat) -> (X-- : divides m (times (S (S O)) n)) -> (X--1 : lt (S O) m) -> eq lzero nat m (times (S (S O)) n)) lzero (λ (X-- : And lzero lzero (lt (S O) (times (S (S O)) n)) ((m : nat) -> (X-- : divides m (times (S (S O)) n)) -> (X--1 : lt (S O) m) -> eq lzero nat m (times (S (S O)) n))) -> False lzero) (λ (H : lt (S O) (times (S (S O)) n)) -> λ (H1 : (m : nat) -> (X-- : divides m (times (S (S O)) n)) -> (X--1 : lt (S O) m) -> eq lzero nat m (times (S (S O)) n)) -> absurd lzero (eq lzero nat (S (S O)) (times (S (S O)) n)) (H1 (S (S O)) (quotient (S (S O)) (times (S (S O)) n) n (rewrite-r lzero lzero nat (times n (S (S O))) (λ (X-- : nat) -> eq lzero nat X-- (times (S (S O)) n)) (rewrite-l lzero lzero nat (plus n (times n (S O))) (λ (X-- : nat) -> eq lzero nat X-- (times (S (S O)) n)) (rewrite-l lzero lzero nat (plus n (times n O)) (λ (X-- : nat) -> eq lzero nat (plus n X--) (times (S (S O)) n)) (rewrite-l lzero lzero nat O (λ (X-- : nat) -> eq lzero nat (plus n (plus n X--)) (times (S (S O)) n)) (rewrite-l lzero lzero nat n (λ (X-- : nat) -> eq lzero nat (plus n X--) (times (S (S O)) n)) (rewrite-r lzero lzero nat (times n (S (S O))) (λ (X-- : nat) -> eq lzero nat (plus n n) X--) (rewrite-l lzero lzero nat (plus n (times n (S O))) (λ (X-- : nat) -> eq lzero nat (plus n n) X--) (rewrite-l lzero lzero nat (plus n (times n O)) (λ (X-- : nat) -> eq lzero nat (plus n n) (plus n X--)) (rewrite-l lzero lzero nat O (λ (X-- : nat) -> eq lzero nat (plus n n) (plus n (plus n X--))) (rewrite-l lzero lzero nat n (λ (X-- : nat) -> eq lzero nat (plus n n) (plus n X--)) (refl lzero nat (plus n n)) (plus n O) (plus-n-O n)) (times n O) (times-n-O n)) (times n (S O)) (times-n-Sm n O)) (times n (S (S O))) (times-n-Sm n (S O))) (times (S (S O)) n) (commutative-times (S (S O)) n)) (plus n O) (plus-n-O n)) (times n O) (times-n-O n)) (times n (S O)) (times-n-Sm n O)) (times n (S (S O))) (times-n-Sm n (S O))) (times (S (S O)) n) (commutative-times (S (S O)) n))) (eq-coerc lzero (lt (mod (S O) O) (plus (plus (mod (S O) O) (times O (div (S O) O))) (S O))) (lt (S O) (S (S O))) (lt-plus-Sn-r (mod (S O) O) (times O (div (S O) O)) O) (rewrite-l lzero (lsuc lzero) nat (S O) (λ (X-- : nat) -> eq (lsuc lzero) (Set (lzero)) (lt (mod (S O) O) (plus X-- (S O))) (lt (S O) (S (S O)))) (rewrite-l lzero (lsuc lzero) nat (S O) (λ (X-- : nat) -> eq (lsuc lzero) (Set (lzero)) (lt X-- (plus (S O) (S O))) (lt (S O) (S (S O)))) (rewrite-r lzero (lsuc lzero) nat (S (S O)) (λ (X-- : nat) -> eq (lsuc lzero) (Set (lzero)) (lt (S O) X--) (lt (S O) (S (S O)))) (refl (lsuc lzero) (Set (lzero)) (lt (S O) (S (S O)))) (plus (S O) (S O)) (rewrite-r lzero lzero nat (times (S O) (S O)) (λ (X-- : nat) -> eq lzero nat (plus (S O) X--) (S (S O))) (rewrite-r lzero lzero nat (times (S (S O)) (S O)) (λ (X-- : nat) -> eq lzero nat (plus (S O) (times (S O) (S O))) X--) (times-Sn-m (S O) (S O)) (S (S O)) (times-n-1 (S (S O)))) (S O) (times-n-1 (S O)))) (mod (S O) O) (rewrite-r lzero lzero nat (plus O (mod (S O) O)) (λ (X-- : nat) -> eq lzero nat (S O) X--) (rewrite-l lzero lzero nat (plus (mod (S O) O) O) (λ (X-- : nat) -> eq lzero nat (S O) X--) (rewrite-r lzero lzero nat (times O (div (S O) O)) (λ (X-- : nat) -> eq lzero nat (S O) (plus (mod (S O) O) X--)) (rewrite-l lzero lzero nat (plus (times O (div (S O) O)) (mod (S O) O)) (λ (X-- : nat) -> eq lzero nat (S O) X--) (let-clause-1033''' n ltn X-clearme H H1 (S O) O) (plus (mod (S O) O) (times O (div (S O) O))) (commutative-plus (times O (div (S O) O)) (mod (S O) O))) O (times-O-n (div (S O) O))) (plus O (mod (S O) O)) (commutative-plus (mod (S O) O) O)) (mod (S O) O) (plus-O-n (mod (S O) O)))) (plus (mod (S O) O) (times O (div (S O) O))) (rewrite-l lzero lzero nat (plus (times O (div (S O) O)) (mod (S O) O)) (λ (X-- : nat) -> eq lzero nat (S O) X--) (let-clause-1033''' n ltn X-clearme H H1 (S O) O) (plus (mod (S O) O) (times O (div (S O) O))) (commutative-plus (times O (div (S O) O)) (mod (S O) O)))))) (lt-to-not-eq (S (S O)) (times (S (S O)) n) (eq-ind-r lzero lzero nat (times (S (S O)) (S O)) (λ (x : nat) -> λ (X-- : eq lzero nat x (times (S (S O)) (S O))) -> lt x (times (S (S O)) n)) (monotonic-lt-times-r (S (S O)) (lt-O-S (S O)) (S O) n ltn) (S (S O)) (times-n-1 (S (S O)))))) X-clearme)

eq-prim-prim-pred : (n : nat) -> (X-- : lt (S O) n) -> eq lzero nat (prim (times (S (S O)) n)) (prim (pred (times (S (S O)) n)))
eq-prim-prim-pred = λ (n : nat) -> λ (ltn : lt (S O) n) -> eq-ind-r lzero lzero bool false (λ (x : bool) -> λ (X-- : eq lzero bool x false) -> eq lzero nat (match-bool lzero (λ (X-0 : bool) -> nat) (plus (S O) (bigop (times (S (S O)) n) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (bigop (times (S (S O)) n) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)) x) (prim (pred (times (S (S O)) n)))) (eq-ind lzero lzero nat (S (pred (times (S (S O)) n))) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (S (pred (times (S (S O)) n))) x-1) -> eq lzero nat (bigop x-1 (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)) (prim (pred (times (S (S O)) n)))) (refl lzero nat (bigop (S (pred (times (S (S O)) n))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (times (S (S O)) n) (S-pred (times (S (S O)) n) (eq-ind-r lzero lzero nat (times O (S O)) (λ (x : nat) -> λ (X-- : eq lzero nat x (times O (S O))) -> lt x (times (S (S O)) n)) (lt-times O (S (S O)) (S O) n (lt-O-S (S O)) ltn) O (times-n-1 O)))) (primeb (times (S (S O)) n)) (not-prime-to-primeb-false (times (S (S O)) n) (not-prime-times-2 n ltn))

le-prim-n1 : (n : nat) -> (X-- : le (S (S (S (S O)))) n) -> le (prim (S (times (S (S O)) n))) n
le-prim-n1 = λ (n : nat) -> λ (le4 : le (S (S (S (S O)))) n) -> le-ind lzero (S (S (S (S O)))) (λ (x-417 : nat) -> λ (X-x-418 : le (S (S (S (S O)))) x-417) -> le (prim (S (times (S (S O)) x-417))) x-417) (le-n (prim (S (times (S (S O)) (S (S (S (S O)))))))) (λ (m : nat) -> λ (le40 : le (S (S (S (S O)))) m) -> eq-ind-r lzero lzero nat (pred (times (S (S O)) (S m))) (λ (x : nat) -> λ (X-- : eq lzero nat x (pred (times (S (S O)) (S m)))) -> (X-x-421 : le (prim x) m) -> le (prim (S (times (S (S O)) (S m)))) (S m)) (eq-ind lzero lzero nat (prim (times (S (S O)) (S m))) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (prim (times (S (S O)) (S m))) x-1) -> (X-x-421 : le x-1 m) -> le (prim (S (times (S (S O)) (S m)))) (S m)) (λ (H : le (prim (times (S (S O)) (S m))) m) -> match-bool lzero (λ (X-- : bool) -> le (match-bool lzero (λ (X-0 : bool) -> nat) (plus (S O) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)) X--) (S m)) (le-S-S (plus O (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) m H) (le-S (match-bool lzero (λ (X-- : bool) -> nat) (plus (S O) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)) false) m H) (primeb (S (times (S (S O)) (S m))))) (prim (pred (times (S (S O)) (S m)))) (eq-prim-prim-pred (S m) (le-S-S (S O) m (transitive-le (S O) (S (S (S (S O)))) m (lt-O-S (S (S (S O)))) le40)))) (S (times (S (S O)) m)) (rewrite-l lzero lzero nat m (λ (X-- : nat) -> eq lzero nat (S (plus m X--)) (plus m (S (plus m O)))) (rewrite-r lzero lzero nat (plus m (S m)) (λ (X-- : nat) -> eq lzero nat X-- (plus m (S (plus m O)))) (rewrite-l lzero lzero nat m (λ (X-- : nat) -> eq lzero nat (plus m (S m)) (plus m (S X--))) (refl lzero nat (plus m (S m))) (plus m O) (plus-n-O m)) (S (plus m m)) (plus-n-Sm m m)) (plus m O) (plus-n-O m))) n le4

le-prim-n2 : (n : nat) -> (X-- : le (S (S (S (S (S (S (S O))))))) n) -> le (prim (S (times (S (S O)) n))) (pred n)
le-prim-n2 = λ (n : nat) -> λ (le7 : le (S (S (S (S (S (S (S O))))))) n) -> le-ind lzero (S (S (S (S (S (S (S O))))))) (λ (x-417 : nat) -> λ (X-x-418 : le (S (S (S (S (S (S (S O))))))) x-417) -> le (prim (S (times (S (S O)) x-417))) (pred x-417)) (le-n (prim (S (times (S (S O)) (S (S (S (S (S (S (S O))))))))))) (λ (m : nat) -> λ (le70 : le (S (S (S (S (S (S (S O))))))) m) -> eq-ind-r lzero lzero nat (pred (times (S (S O)) (S m))) (λ (x : nat) -> λ (X-- : eq lzero nat x (pred (times (S (S O)) (S m)))) -> (X-x-421 : le (prim x) (pred m)) -> le (prim (S (times (S (S O)) (S m)))) (pred (S m))) (eq-ind lzero lzero nat (prim (times (S (S O)) (S m))) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (prim (times (S (S O)) (S m))) x-1) -> (X-x-421 : le x-1 (pred m)) -> le (prim (S (times (S (S O)) (S m)))) (pred (S m))) (λ (H : le (prim (times (S (S O)) (S m))) (pred m)) -> eq-ind lzero lzero nat (S (pred m)) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (S (pred m)) x-1) -> le (match-bool lzero (λ (X-- : bool) -> nat) (plus (S O) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)) (primeb (S (times (S (S O)) (S m))))) x-1) (match-bool lzero (λ (X-- : bool) -> le (match-bool lzero (λ (X-0 : bool) -> nat) (plus (S O) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)) X--) (S (pred m))) (le-S-S (plus O (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (pred m) H) (le-S (match-bool lzero (λ (X-- : bool) -> nat) (plus (S O) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (bigop (S (times (S (S O)) (S m))) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O)) false) (pred m) H) (primeb (S (times (S (S O)) (S m))))) m (S-pred m (transitive-le (S O) (S (S (S (S (S (S (S O))))))) m (lt-O-S (S (S (S (S (S (S O))))))) le70))) (prim (pred (times (S (S O)) (S m)))) (eq-prim-prim-pred (S m) (le-S-S (S O) m (transitive-le (S O) (S (S (S (S (S (S (S O))))))) m (lt-O-S (S (S (S (S (S (S O))))))) le70)))) (S (times (S (S O)) m)) (rewrite-l lzero lzero nat m (λ (X-- : nat) -> eq lzero nat (S (plus m X--)) (plus m (S (plus m O)))) (rewrite-r lzero lzero nat (plus m (S m)) (λ (X-- : nat) -> eq lzero nat X-- (plus m (S (plus m O)))) (rewrite-l lzero lzero nat m (λ (X-- : nat) -> eq lzero nat (plus m (S m)) (plus m (S X--))) (refl lzero nat (plus m (S m))) (plus m O) (plus-n-O m)) (S (plus m m)) (plus-n-Sm m m)) (plus m O) (plus-n-O m))) n le7

let-clause-1553 : (n : nat) -> (n0 : nat) -> (X-clearme : ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a))))) -> (a : nat) -> (X-clearme0 : Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a)))) -> (Hn : eq lzero nat n0 (S (times (S (S O)) a))) -> eq lzero nat n0 (plus a (S a))
let-clause-1553 = λ (n : nat) -> λ (n0 : nat) -> λ (X-clearme : ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a))))) -> λ (a : nat) -> λ (X-clearme0 : Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a)))) -> λ (Hn : eq lzero nat n0 (S (times (S (S O)) a))) -> rewrite-l lzero lzero nat (S (plus a a)) (λ (X-- : nat) -> eq lzero nat n0 X--) (rewrite-r lzero lzero nat (plus a O) (λ (X-- : nat) -> eq lzero nat n0 (S (plus a X--))) (rewrite-r lzero lzero nat (times a O) (λ (X-- : nat) -> eq lzero nat n0 (S (plus a (plus a X--)))) (rewrite-r lzero lzero nat (times a (S O)) (λ (X-- : nat) -> eq lzero nat n0 (S (plus a X--))) (rewrite-r lzero lzero nat (times a (S (S O))) (λ (X-- : nat) -> eq lzero nat n0 (S X--)) (rewrite-l lzero lzero nat (times (S (S O)) a) (λ (X-- : nat) -> eq lzero nat n0 (S X--)) Hn (times a (S (S O))) (commutative-times (S (S O)) a)) (plus a (times a (S O))) (times-n-Sm a (S O))) (plus a (times a O)) (times-n-Sm a O)) O (times-n-O a)) a (plus-n-O a)) (plus a (S a)) (plus-n-Sm a a)

even-or-odd : (n : nat) -> ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat n (times (S (S O)) a)) (eq lzero nat n (S (times (S (S O)) a))))
even-or-odd = λ (n : nat) -> nat-ind lzero (λ (X-x-365 : nat) -> ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat X-x-365 (times (S (S O)) a)) (eq lzero nat X-x-365 (S (times (S (S O)) a))))) (ex-intro lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat O (times (S (S O)) a)) (eq lzero nat O (S (times (S (S O)) a)))) O (or-introl lzero lzero (eq lzero nat O (times (S (S O)) O)) (eq lzero nat O (S (times (S (S O)) O))) (refl lzero nat O))) (λ (n0 : nat) -> λ (X-clearme : ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a))))) -> match-ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a)))) lzero (λ (X-- : ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a))))) -> ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat (S n0) (times (S (S O)) a)) (eq lzero nat (S n0) (S (times (S (S O)) a))))) (λ (a : nat) -> λ (X-clearme0 : Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a)))) -> match-Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a))) lzero (λ (X-- : Or lzero lzero (eq lzero nat n0 (times (S (S O)) a)) (eq lzero nat n0 (S (times (S (S O)) a)))) -> ex lzero lzero nat (λ (a0 : nat) -> Or lzero lzero (eq lzero nat (S n0) (times (S (S O)) a0)) (eq lzero nat (S n0) (S (times (S (S O)) a0))))) (λ (Hn : eq lzero nat n0 (times (S (S O)) a)) -> ex-intro lzero lzero nat (λ (a0 : nat) -> Or lzero lzero (eq lzero nat (S n0) (times (S (S O)) a0)) (eq lzero nat (S n0) (S (times (S (S O)) a0)))) a (or-intror lzero lzero (eq lzero nat (S n0) (times (S (S O)) a)) (eq lzero nat (S n0) (S (times (S (S O)) a))) (eq-f lzero lzero nat nat S n0 (times (S (S O)) a) Hn))) (λ (Hn : eq lzero nat n0 (S (times (S (S O)) a))) -> ex-intro lzero lzero nat (λ (a0 : nat) -> Or lzero lzero (eq lzero nat (S n0) (times (S (S O)) a0)) (eq lzero nat (S n0) (S (times (S (S O)) a0)))) (S a) (or-introl lzero lzero (eq lzero nat (S n0) (times (S (S O)) (S a))) (eq lzero nat (S n0) (S (times (S (S O)) (S a)))) (eq-ind-r lzero lzero nat (S (times (S (S O)) a)) (λ (x : nat) -> λ (X-- : eq lzero nat x (S (times (S (S O)) a))) -> eq lzero nat (S x) (times (S (S O)) (S a))) (rewrite-l lzero lzero nat a (λ (X-- : nat) -> eq lzero nat (S (S (plus a X--))) (S (plus a (S (plus a O))))) (rewrite-r lzero lzero nat (plus a (S a)) (λ (X-- : nat) -> eq lzero nat (S X--) (S (plus a (S (plus a O))))) (rewrite-l lzero lzero nat n0 (λ (X-- : nat) -> eq lzero nat (S X--) (S (plus a (S (plus a O))))) (rewrite-l lzero lzero nat a (λ (X-- : nat) -> eq lzero nat (S n0) (S (plus a (S X--)))) (rewrite-l lzero lzero nat n0 (λ (X-- : nat) -> eq lzero nat (S n0) (S X--)) (refl lzero nat (S n0)) (plus a (S a)) (let-clause-1553 n n0 X-clearme a X-clearme0 Hn)) (plus a O) (plus-n-O a)) (plus a (S a)) (let-clause-1553 n n0 X-clearme a X-clearme0 Hn)) (S (plus a a)) (plus-n-Sm a a)) (plus a O) (plus-n-O a)) n0 Hn))) X-clearme0) X-clearme) n

le-prim-n3 : (n : nat) -> (X-- : le (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) n) -> le (prim n) (pred (div n (S (S O))))
le-prim-n3 = λ (n : nat) -> λ (len : le (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) n) -> match-ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat (pred n) (times (S (S O)) a)) (eq lzero nat (pred n) (S (times (S (S O)) a)))) lzero (λ (X-- : ex lzero lzero nat (λ (a : nat) -> Or lzero lzero (eq lzero nat (pred n) (times (S (S O)) a)) (eq lzero nat (pred n) (S (times (S (S O)) a))))) -> le (prim n) (pred (div n (S (S O))))) (λ (a : nat) -> λ (X-clearme : Or lzero lzero (eq lzero nat (pred n) (times (S (S O)) a)) (eq lzero nat (pred n) (S (times (S (S O)) a)))) -> match-Or lzero lzero (eq lzero nat (pred n) (times (S (S O)) a)) (eq lzero nat (pred n) (S (times (S (S O)) a))) lzero (λ (X-- : Or lzero lzero (eq lzero nat (pred n) (times (S (S O)) a)) (eq lzero nat (pred n) (S (times (S (S O)) a)))) -> le (prim n) (pred (div n (S (S O))))) (λ (Hpredn : eq lzero nat (pred n) (times (S (S O)) a)) -> eq-ind-r lzero lzero nat (S (times (S (S O)) a)) (λ (x : nat) -> λ (X-- : eq lzero nat x (S (times (S (S O)) a))) -> le (prim x) (pred (div x (S (S O))))) (transitive-le (prim (S (times (S (S O)) a))) (pred a) (pred (div (S (times (S (S O)) a)) (S (S O)))) (le-prim-n2 a (le-times-to-le (S (S O)) (S (S (S (S (S (S (S O))))))) a (lt-O-S (S O)) (le-S-S-to-le (times (S (S O)) (S (S (S (S (S (S (S O)))))))) (times (S (S O)) a) (eq-ind lzero lzero nat n (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat n x-1) -> le (S (times (S (S O)) (S (S (S (S (S (S (S O))))))))) x-1) len (S (times (S (S O)) a)) (eq-ind lzero lzero nat (pred n) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (pred n) x-1) -> eq lzero nat n (S x-1)) (sym-eq lzero nat (S (pred n)) n (S-pred n (transitive-le (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) n (lt-O-S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) len))) (times (S (S O)) a) Hpredn))))) (monotonic-pred a (div (S (times (S (S O)) a)) (S (S O))) (le-times-to-le-div (S (times (S (S O)) a)) (S (S O)) a (lt-O-S (S O)) (le-n-Sn (times (S (S O)) a))))) n (eq-ind lzero lzero nat (pred n) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (pred n) x-1) -> eq lzero nat n (S x-1)) (sym-eq lzero nat (S (pred n)) n (S-pred n (transitive-le (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) n (lt-O-S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) len))) (times (S (S O)) a) Hpredn)) (λ (Hpredn : eq lzero nat (pred n) (S (times (S (S O)) a))) -> eq-ind-r lzero lzero nat (times (S (S O)) (S a)) (λ (x : nat) -> λ (X-- : eq lzero nat x (times (S (S O)) (S a))) -> le (prim x) (pred (div x (S (S O))))) (transitive-le (prim (times (S (S O)) (S a))) (pred a) (pred (div (times (S (S O)) (S a)) (S (S O)))) (eq-ind-r lzero lzero nat (prim (pred (times (S (S O)) (S a)))) (λ (x : nat) -> λ (X-- : eq lzero nat x (prim (pred (times (S (S O)) (S a))))) -> le x (pred a)) (eq-ind lzero lzero nat n (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat n x-1) -> le (prim (pred x-1)) (pred a)) (eq-ind-r lzero lzero nat (S (times (S (S O)) a)) (λ (x : nat) -> λ (X-- : eq lzero nat x (S (times (S (S O)) a))) -> le (prim x) (pred a)) (le-prim-n2 a (le-S-S-to-le (S (S (S (S (S (S (S O))))))) a (lt-times-n-to-lt-r (S (S O)) (S (S (S (S (S (S (S O))))))) (S a) (eq-ind lzero lzero nat n (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat n x-1) -> lt (times (S (S O)) (S (S (S (S (S (S (S O)))))))) x-1) len (times (S (S O)) (S a)) (eq-ind lzero lzero nat (S (plus a (plus a O))) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (S (plus a (plus a O))) x-1) -> eq lzero nat n (S x-1)) (eq-ind lzero lzero nat (pred n) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (pred n) x-1) -> eq lzero nat n (S x-1)) (sym-eq lzero nat (S (pred n)) n (S-pred n (transitive-le (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) n (lt-O-S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) len))) (S (plus a (plus a O))) Hpredn) (plus a (S (plus a O))) (plus-n-Sm a (plus a O))))))) (pred n) Hpredn) (times (S (S O)) (S a)) (eq-ind lzero lzero nat (S (plus a (plus a O))) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (S (plus a (plus a O))) x-1) -> eq lzero nat n (S x-1)) (eq-ind lzero lzero nat (pred n) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (pred n) x-1) -> eq lzero nat n (S x-1)) (sym-eq lzero nat (S (pred n)) n (S-pred n (transitive-le (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) n (lt-O-S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) len))) (S (plus a (plus a O))) Hpredn) (plus a (S (plus a O))) (plus-n-Sm a (plus a O)))) (prim (times (S (S O)) (S a))) (eq-prim-prim-pred (S a) (lt-times-n-to-lt-r (S (S O)) (S O) (S a) (eq-ind lzero lzero nat n (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat n x-1) -> lt (times (S (S O)) (S O)) x-1) (transitive-le (S (times (S (S O)) (S O))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) n (le-plus-n-r (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))) (S (times (S (S O)) (S O)))) len) (times (S (S O)) (S a)) (eq-ind lzero lzero nat (S (plus a (plus a O))) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (S (plus a (plus a O))) x-1) -> eq lzero nat n (S x-1)) (eq-ind lzero lzero nat (pred n) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (pred n) x-1) -> eq lzero nat n (S x-1)) (sym-eq lzero nat (S (pred n)) n (S-pred n (transitive-le (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) n (lt-O-S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) len))) (S (plus a (plus a O))) Hpredn) (plus a (S (plus a O))) (plus-n-Sm a (plus a O))))))) (monotonic-pred a (div (times (S (S O)) (S a)) (S (S O))) (le-times-to-le-div (times (S (S O)) (S a)) (S (S O)) a (lt-O-S (S O)) (eq-coerc lzero (le (times (S (S O)) a) (plus (S (S O)) (times (S (S O)) a))) (le (times (S (S O)) a) (times (S (S O)) (S a))) (le-plus-n (S (S O)) (times (S (S O)) a)) (rewrite-r lzero (lsuc lzero) nat (times (S (S O)) (S a)) (λ (X-- : nat) -> eq (lsuc lzero) (Set (lzero)) (le (times (S (S O)) a) X--) (le (times (S (S O)) a) (times (S (S O)) (S a)))) (refl (lsuc lzero) (Set (lzero)) (le (times (S (S O)) a) (times (S (S O)) (S a)))) (plus (S (S O)) (times (S (S O)) a)) (times-n-Sm (S (S O)) a)))))) n (eq-ind lzero lzero nat (S (plus a (plus a O))) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (S (plus a (plus a O))) x-1) -> eq lzero nat n (S x-1)) (eq-ind lzero lzero nat (pred n) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (pred n) x-1) -> eq lzero nat n (S x-1)) (sym-eq lzero nat (S (pred n)) n (S-pred n (transitive-le (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) n (lt-O-S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) len))) (S (plus a (plus a O))) Hpredn) (plus a (S (plus a O))) (plus-n-Sm a (plus a O)))) X-clearme) (even-or-odd (pred n))

Psi : (X-- : nat) -> nat
Psi = λ (n : nat) -> bigop (S n) (λ (p : nat) -> primeb p) nat (S O) times (λ (p : nat) -> exp p (log p n))

psi-def : (n : nat) -> eq lzero nat (Psi n) (bigop (S n) (λ (p : nat) -> primeb p) nat (S O) times (λ (p : nat) -> exp p (log p n)))
psi-def = λ (n : nat) -> refl lzero nat (Psi n)

le-Psil1 : (n : nat) -> le (Psi n) (bigop (S n) (λ (p : nat) -> primeb p) nat (S O) times (λ (p : nat) -> n))
le-Psil1 = λ (n : nat) -> match-nat lzero (λ (X-- : nat) -> le (Psi X--) (bigop (S X--) (λ (p : nat) -> primeb p) nat (S O) times (λ (p : nat) -> X--))) (le-n (Psi O)) (λ (m : nat) -> le-pi (S (S m)) primeb (λ (X-- : nat) -> exp X-- (log X-- (S m))) (λ (X-- : nat) -> S m) (λ (i : nat) -> λ (X-- : lt i (S (S m))) -> λ (X-0 : eq lzero bool (primeb i) true) -> le-exp-log i (S m) (lt-O-S m))) n

le-Psil : (n : nat) -> le (Psi n) (exp n (prim n))
le-Psil = λ (n : nat) -> eq-ind lzero lzero nat (bigop (S n) (λ (i : nat) -> primeb i) nat (S O) times (λ (i : nat) -> n)) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (bigop (S n) (λ (i : nat) -> primeb i) nat (S O) times (λ (i : nat) -> n)) x-1) -> le (Psi n) x-1) (le-Psil1 n) (exp n (bigop (S n) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (exp-sigma (S n) n primeb)

lePsi-r2 : (n : nat) -> le (exp n (prim n)) (times (Psi n) (Psi n))
lePsi-r2 = λ (n : nat) -> Or-ind lzero lzero lzero (lt O n) (eq lzero nat O n) (λ (X-x-170 : Or lzero lzero (lt O n) (eq lzero nat O n)) -> le (exp n (prim n)) (times (Psi n) (Psi n))) (λ (Hn : lt O n) -> eq-ind lzero lzero nat (bigop (S n) (λ (i : nat) -> primeb i) nat (S O) times (λ (i : nat) -> n)) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (bigop (S n) (λ (i : nat) -> primeb i) nat (S O) times (λ (i : nat) -> n)) x-1) -> le x-1 (times (Psi n) (Psi n))) (eq-ind lzero lzero nat (bigop (S n) (λ (i : nat) -> primeb i) nat (S O) times (λ (i : nat) -> times (exp i (log i n)) (exp i (log i n)))) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (bigop (S n) (λ (i : nat) -> primeb i) nat (S O) times (λ (i : nat) -> times (exp i (log i n)) (exp i (log i n)))) x-1) -> le (bigop (S n) (λ (i : nat) -> primeb i) nat (S O) times (λ (i : nat) -> n)) x-1) (le-pi (S n) primeb (λ (X-- : nat) -> n) (λ (X-- : nat) -> times (exp X-- (log X-- n)) (exp X-- (log X-- n))) (λ (i : nat) -> λ (lti : lt i (S n)) -> λ (primei : eq lzero bool (primeb i) true) -> eq-ind lzero lzero nat (exp i (plus (log i n) (log i n))) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (exp i (plus (log i n) (log i n))) x-1) -> le n x-1) (transitive-le n (exp i (S (log i n))) (exp i (plus (log i n) (log i n))) (lt-to-le n (exp i (S (log i n))) (lt-exp-log i n (prime-to-lt-SO i (primeb-true-to-prime i (rewrite-r lzero lzero bool true (λ (X-- : bool) -> eq lzero bool X-- true) (refl lzero bool true) (primeb i) primei))))) (le-exp (S (log i n)) (plus (log i n) (log i n)) i (prime-to-lt-O i (primeb-true-to-prime i (rewrite-r lzero lzero bool true (λ (X-- : bool) -> eq lzero bool X-- true) (refl lzero bool true) (primeb i) primei))) (eq-ind-r lzero lzero nat (plus (log i n) O) (λ (x : nat) -> λ (X-- : eq lzero nat x (plus (log i n) O)) -> le (S x) (plus (log i n) (log i n))) (eq-ind-r lzero lzero nat (plus (log i n) (S O)) (λ (x : nat) -> λ (X-- : eq lzero nat x (plus (log i n) (S O))) -> le x (plus (log i n) (log i n))) (monotonic-le-plus-r (log i n) (S O) (log i n) (lt-O-log i n (lt-to-le-to-lt (S O) i n (prime-to-lt-SO i (primeb-true-to-prime i (rewrite-r lzero lzero bool true (λ (X-- : bool) -> eq lzero bool X-- true) (refl lzero bool true) (primeb i) primei))) (le-S-S-to-le i n lti)) (le-S-S-to-le i n lti))) (S (plus (log i n) O)) (plus-n-Sm (log i n) O)) (log i n) (plus-n-O (log i n))))) (times (exp i (log i n)) (exp i (log i n))) (exp-plus-times i (log i n) (log i n)))) (times (bigop (S n) (λ (i : nat) -> primeb i) nat (S O) times (λ (i : nat) -> exp i (log i n))) (bigop (S n) (λ (i : nat) -> primeb i) nat (S O) times (λ (i : nat) -> exp i (log i n)))) (times-pi (S n) primeb (λ (X-- : nat) -> exp X-- (log X-- n)) (λ (X-- : nat) -> exp X-- (log X-- n)))) (exp n (bigop (S n) (λ (i : nat) -> primeb i) nat O plus (λ (i : nat) -> S O))) (exp-sigma (S n) n primeb)) (λ (Hn : eq lzero nat O n) -> eq-ind lzero lzero nat O (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat O x-1) -> le (exp x-1 (prim x-1)) (times (Psi x-1) (Psi x-1))) (le-n (exp O (prim O))) n Hn) (le-to-or-lt-eq O n (le-O-n n))

Psi' : (X-- : nat) -> nat
Psi' = λ (n : nat) -> bigop (S n) (λ (p : nat) -> primeb p) nat (S O) times (λ (p : nat) -> bigop (log p n) (λ (i : nat) -> true) nat (S O) times (λ (i : nat) -> p))

Psidef : (n : nat) -> eq lzero nat (Psi' n) (bigop (S n) (λ (p : nat) -> primeb p) nat (S O) times (λ (p : nat) -> bigop (log p n) (λ (i : nat) -> true) nat (S O) times (λ (i : nat) -> p)))
Psidef = λ (n : nat) -> refl lzero nat (Psi' n)

eq-Psi-Psi' : (n : nat) -> eq lzero nat (Psi n) (Psi' n)
eq-Psi-Psi' = λ (n : nat) -> same-bigop (S n) primeb primeb nat (S O) times (λ (X-- : nat) -> exp X-- (log X-- n)) (λ (X-- : nat) -> bigop (log X-- n) (λ (i : nat) -> true) nat (S O) times (λ (i : nat) -> X--)) (λ (i : nat) -> λ (auto : lt i (S n)) -> refl lzero bool (primeb i)) (λ (i : nat) -> λ (lti : lt i (S n)) -> λ (primebi : eq lzero bool (primeb i) true) -> trans-eq lzero nat (exp i (log i n)) (exp i (bigop (log i n) (λ (x : nat) -> true) nat O plus (λ (x : nat) -> S O))) (bigop (log i n) (λ (i0 : nat) -> true) nat (S O) times (λ (i0 : nat) -> i)) (eq-f lzero lzero nat nat (exp i) (log i n) (bigop (log i n) (λ (x : nat) -> true) nat O plus (λ (x : nat) -> S O)) (sym-eq lzero nat (bigop (log i n) (λ (x : nat) -> true) nat O plus (λ (x : nat) -> S O)) (log i n) (sigma-const (log i n)))) (sym-eq lzero nat (bigop (log i n) (λ (i0 : nat) -> true) nat (S O) times (λ (i0 : nat) -> i)) (exp i (bigop (log i n) (λ (x : nat) -> true) nat O plus (λ (x : nat) -> S O))) (exp-sigma (log i n) i (λ (X-- : nat) -> true))))

