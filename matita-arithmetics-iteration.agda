open import Agda.Primitive
open import matita-basics-logic
open import matita-basics-relations
open import matita-arithmetics-nat


iter : (l4-v : Level) -> (H-v : Set l4-v) -> (X---v : (X---v : H-v) -> H-v) -> (X--1-v : nat) -> (X--2-v : H-v) -> H-v
iter l5-v H-v X---v O a-v = a-v
iter l5-v H-v X---v (S m-v) a-v = X---v (iter l5-v H-v X---v m-v a-v)

le-iter : (g : (X-- : nat) -> nat) -> (a : nat) -> (X-- : (x : nat) -> le x (g x)) -> (i : nat) -> le a (iter lzero nat g i a)
le-iter = λ (g : (X-- : nat) -> nat) -> λ (a : nat) -> λ (leg : (x : nat) -> le x (g x)) -> λ (i : nat) -> nat-ind lzero (λ (X-x-365 : nat) -> le a (iter lzero nat g X-x-365 a)) (le-n a) (λ (n : nat) -> λ (Hind : le a (iter lzero nat g n a)) -> transitive-le a (iter lzero nat g n a) (iter lzero nat g (S n) a) Hind (leg (iter lzero nat g n a))) i

iter-iter : (l42 : Level) -> (A : Set l42) -> (g : (X-- : A) -> A) -> (a : A) -> (b : nat) -> (c : nat) -> eq l42 A (iter l42 A g c (iter l42 A g b a)) (iter l42 A g (plus b c) a)
iter-iter = λ (l42 : Level) -> λ (A : Set l42) -> λ (g : (X-- : A) -> A) -> λ (a : A) -> λ (b : nat) -> λ (c : nat) -> nat-ind l42 (λ (X-x-365 : nat) -> eq l42 A (iter l42 A g X-x-365 (iter l42 A g b a)) (iter l42 A g (plus b X-x-365) a)) (eq-ind lzero l42 nat b (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat b x-1) -> eq l42 A (iter l42 A g O (iter l42 A g b a)) (iter l42 A g x-1 a)) (refl l42 A (iter l42 A g b a)) (plus b O) (plus-n-O b)) (λ (m : nat) -> λ (Hind : eq l42 A (iter l42 A g m (iter l42 A g b a)) (iter l42 A g (plus b m) a)) -> eq-ind lzero l42 nat (S (plus b m)) (λ (x-1 : nat) -> λ (X-x-2 : eq lzero nat (S (plus b m)) x-1) -> eq l42 A (iter l42 A g (S m) (iter l42 A g b a)) (iter l42 A g x-1 a)) (eq-f l42 l42 A A g (iter l42 A g m (iter l42 A g b a)) (iter l42 A g (plus b m) a) Hind) (plus b (S m)) (plus-n-Sm b m)) c

monotonic-iter : (g : (X-- : nat) -> nat) -> (a : nat) -> (b : nat) -> (i : nat) -> (X-- : monotonic lzero lzero nat le g) -> (X--1 : le a b) -> le (iter lzero nat g i a) (iter lzero nat g i b)
monotonic-iter = λ (g : (X-- : nat) -> nat) -> λ (a : nat) -> λ (b : nat) -> λ (i : nat) -> λ (Hmono : monotonic lzero lzero nat le g) -> λ (leab : le a b) -> nat-ind lzero (λ (X-x-365 : nat) -> le (iter lzero nat g X-x-365 a) (iter lzero nat g X-x-365 b)) leab (λ (m : nat) -> λ (Hind : le (iter lzero nat g m a) (iter lzero nat g m b)) -> Hmono (iter lzero nat g m a) (iter lzero nat g m b) Hind) i

monotonic-iter2 : (g : (X-- : nat) -> nat) -> (a : nat) -> (i : nat) -> (j : nat) -> (X-- : (x : nat) -> le x (g x)) -> (X--1 : le i j) -> le (iter lzero nat g i a) (iter lzero nat g j a)
monotonic-iter2 = λ (g : (X-- : nat) -> nat) -> λ (a : nat) -> λ (i : nat) -> λ (j : nat) -> λ (leg : (x : nat) -> le x (g x)) -> λ (leij : le i j) -> le-ind lzero i (λ (x-417 : nat) -> λ (X-x-418 : le i x-417) -> le (iter lzero nat g i a) (iter lzero nat g x-417 a)) (le-n (iter lzero nat g i a)) (λ (m : nat) -> λ (leim : le i m) -> λ (Hind : le (iter lzero nat g i a) (iter lzero nat g m a)) -> transitive-le (iter lzero nat g i a) (iter lzero nat g m a) (g (iter lzero nat g m a)) Hind (leg (iter lzero nat g m a))) j leij

