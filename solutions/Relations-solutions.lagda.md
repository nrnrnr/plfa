---
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

```
module Relations-solutions where
```

This file gives solutions to exercises in plfa.part1.Relations

## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm)
open import plfa.part1.Relations using (_≤_; s≤s; z≤n; +-mono-≤; _<_; z<s; s<s)
open import Data.Empty using ( ⊥ )
```

#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

```
*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q z≤n       _   = z≤n
*-mono-≤ m n p q (s≤s m≤n) u≤v = +-mono-≤ _ _ _ _ u≤v (*-mono-≤ _ _ _ _ m≤n u≤v)
```

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

```
<-trans : ∀ {m n p : ℕ}
   → m < n
   → n < p
     -----
   → m < p
<-trans z<s     (s<s n) = z<s
<-trans (s<s m) (s<s n) = s<s (<-trans m n)
```

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}/Negation/).)

```
_>_ : ℕ → ℕ → Set
a > b = b < a

data _⊎1_⊎2_ (A B C : Set) : Set where
  inj1 : A → A ⊎1 B ⊎2 C
  inj2 : B → A ⊎1 B ⊎2 C
  inj3 : C → A ⊎1 B ⊎2 C

trich : ∀ (m n : ℕ) → ((m < n) ⊎1 (m ≡ n) ⊎2 (m > n))
trich zero    zero    = inj2 refl
trich zero    (suc n) = inj1 z<s
trich (suc m) zero    = inj3 z<s
trich (suc m) (suc n) = f x
    where
      x = trich m n
      f :  ((m < n) ⊎1 (m ≡ n) ⊎2 (m > n))
         → ((suc m < suc n) ⊎1 (suc m ≡ suc n) ⊎2 (suc m > suc n))
      f (inj1 x) = inj1 (s<s x)
      f (inj2 x) = inj2 (cong suc x)
      f (inj3 x) = inj3 (s<s x)
```

#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

```
+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → n + p < n + q
+-monoʳ-< zero    p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite -- m + p < n + p
    +-comm m p              -- p + m < n + p
  | +-comm n p              -- p + m < p + n
  = +-monoʳ-< p m n m<n
 
+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q  = <-trans (+-monoˡ-< m n p m<n)
                                    (+-monoʳ-< n p q p<q)
```

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

``` 
succ-≤→< : ∀ {m n : ℕ} → suc m ≤ n → m < n
succ-≤→< (s≤s z≤n)     = z<s
succ-≤→< (s≤s (s≤s x)) = s<s (succ-≤→< (s≤s x))

<→succ-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<→succ-≤ z<s       = s≤s z≤n
<→succ-≤ (s<s m<n) = s≤s (<→succ-≤ m<n)
```

## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:

```
data even : ℕ → Set where
 e-zero :
     ---------
     even zero

 e-next  : ∀ {n : ℕ}
   → even n
     ------------
   → even (suc (suc n))

data odd : ℕ → Set where
 o-one  : odd 1

 o-next   : ∀ {n : ℕ}
   → odd n
     -----------
   → odd (suc (suc n))
```
A number is even if it is zero or 2 plus another even number,
and odd if it is one or 2 plus another odd number.

We show that the sum of two even numbers is even:
```
e+e≡e : ∀ {m n : ℕ}
 → even m
 → even n
   ------------
 → even (m + n)
e+e≡e e-zero     b = b
e+e≡e (e-next a) b = e-next (e+e≡e a b)

o+e≡o : ∀ {m n : ℕ}
 → odd m
 → even n
   -----------
 → odd (m + n)
o+e≡o o-one      e-zero     = o-one
o+e≡o o-one      (e-next b) = o-next (o+e≡o o-one b)
o+e≡o (o-next a) b          = o-next (o+e≡o a b)

e+o≡o : ∀ {m n : ℕ}
 → even m
 → odd n
   ------------
 → odd (n + m)
e+o≡o a b = o+e≡o b a
```

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it a next even number, then the result is even
because it is the next even number after the sum of two even numbers,
which is even.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is one,
then if the second argument is zero, then it is odd. If the
second argument is a next even number, then the sum is the next odd
number of the sum of one and the even number. If the first argument
is the next odd number, then the result is an odd number because it
is the next odd number of the sum of an odd and an even.

To show that the sum of an even number and and odd number is odd,
just call o+e≡o with the arguments swapped.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

```
o+o≡e : ∀ {m n : ℕ}
 → odd m
 → odd n
   ------------
 → even (m + n)
o+o≡e o-one      o-one      = e-next e-zero
o+o≡e o-one      (o-next b) = e-next (o+o≡e o-one b)
o+o≡e (o-next a) b          = e-next (o+o≡e a b)
```

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can b
    ---------------
    to (from b) ≡ b

(Hint: For each of these, you may first need to prove related
properties of `One`. Also, you may need to prove that
if `One b` then `1` is less or equal to the result of `from b`.)

```
open import Naturals-solutions using (Bin; ⟨⟩; _O; _I; inc; to; from)

data One : Bin → Set where
  one-⟨⟩ : One (⟨⟩ I)
  one-O  : ∀ {b : Bin} → One b → One (b O)
  one-I  : ∀ {b : Bin} → One b → One (b I)

one-inc : ∀ (b : Bin) → One (b O) → One (b I)
one-inc ⟨⟩ obO = one-⟨⟩
one-inc (b O) obO with obO
...                 | one-O ob' = one-I ob'
one-inc (b I) obO with obO
...                 | one-O ob' = one-I ob' 

one-incI : ∀ (b : Bin) → One b → One (inc b I)
one-incO : ∀ (b : Bin) → One b → One (inc b O)

one-incI ⟨⟩ obO = one-I one-⟨⟩
one-incI (b O) obO with obO
...                 | one-O ob' = one-I (one-I ob')
one-incI (b I) obO with obO
...                 | one-⟨⟩ = one-I (one-O obO)
...                 | one-I  ob = one-I (one-incO b ob)

one-incO ⟨⟩ obI = one-O one-⟨⟩
one-incO (b O) obI with obI
...                 |   one-O  ob = one-O (one-I ob)
one-incO (b I) obI with obI
...                 |   one-⟨⟩ = one-O (one-O obI)
...                 |   one-I  ob = one-O (one-incO b ob)

_ : One (⟨⟩ I O O)
_ = one-O (one-O (one-⟨⟩))

data Can : Bin -> Set where
  can0 : Can (⟨⟩ O)
  canb : ∀ { b : Bin} → One b → Can b

_ : Can (⟨⟩ O)
_ = can0

_ :  Can (⟨⟩ I)
_ = canb (one-⟨⟩)

_ : Can (⟨⟩ I O O)
_ = canb (one-O (one-O (one-⟨⟩))) 

canon-inc : ∀ (b : Bin)
  → Can b
    ------------
  → Can (inc b)
canon-inc ⟨⟩    cb  = canb one-⟨⟩
canon-inc (b O) cb with cb
...                | can0      = canb (one-⟨⟩)         -- Can (⟨⟩ I)
...                | canb oneb = canb (one-inc b oneb) -- Can (b I)
canon-inc (b I) cb with cb
...                | canb oneb with oneb
...                               | one-⟨⟩      = canb (one-O oneb)
...                               | one-I oneb' = canb (one-incO b oneb')

canon-to : ∀ (n : ℕ) → Can (to n)
canon-to zero = can0
canon-to (suc n) = canon-inc (to n) (canon-to n)

to*2≡to-O : ∀ (n : ℕ) → 1 Data.Nat.≤ n → to (2 * n) ≡ (to n) O
to*2≡to-O (suc zero) 1≤n = refl
to*2≡to-O (suc (suc n)) (Data.Nat.s≤s 1≤n)
    with to*2≡to-O (suc n) (Data.Nat.s≤s Data.Nat.z≤n)
... | IH
    rewrite +-comm n 0 | +-comm n (suc n) | +-comm n (suc (suc n)) | IH = refl

open import Data.Nat.Properties using (≤-stepsʳ)

one-1≤from : ∀ (b : Bin) → One b → 1 Data.Nat.≤ from b
one-1≤from .(⟨⟩ I) one-⟨⟩ = Data.Nat.s≤s Data.Nat.z≤n
one-1≤from (b O) (one-O one-b) rewrite +-comm (from b) zero =
  let IH = one-1≤from b one-b in
  ≤-stepsʳ {1} {from b} (from b) IH
one-1≤from (b I) (one-I one-b) = Data.Nat.s≤s Data.Nat.z≤n

open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

one-to-from : ∀ (b : Bin) → One b → to (from b) ≡ b
one-to-from .(⟨⟩ I) one-⟨⟩ = refl
one-to-from (b O) (one-O one-b) =
  begin
  to (2 * from b)        ≡⟨ to*2≡to-O (from b) (one-1≤from b one-b) ⟩
  (to (from b)) O        ≡⟨ cong _O (one-to-from b one-b) ⟩
  (b O)
  ∎
one-to-from (b I) (one-I one-b) =
  begin
  to (from (b I))           ≡⟨ refl ⟩
  to (suc (2 * from b))     ≡⟨ refl ⟩
  inc (to (2 * from b))     ≡⟨ cong inc (to*2≡to-O (from b) (one-1≤from b one-b)) ⟩
  inc ((to (from b)) O)     ≡⟨ cong inc (cong _O (one-to-from b one-b)) ⟩
  inc (b O)                 ≡⟨ refl ⟩
  (b I)
  ∎

canon-to-from : ∀ (b : Bin) → Can b → to (from b) ≡ b
canon-to-from .(⟨⟩ O) can0 = refl
canon-to-from b (canb one-b) = one-to-from b one-b
```
