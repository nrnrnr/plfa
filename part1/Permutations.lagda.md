---
title     : "Permutations":
permalink : /Permutations/
---

```agda
module cs.plfa.part1.Permutations where
```

A sorting algorithm is correct only if its output is a 
permutation of its input.
This page presents multiple ways to formalize permutations.

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Product using (Σ-syntax)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)

open import Data.List using (List; _++_; length; map; foldr; downFrom; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
  renaming (mapIsFold to map-is-foldr)
open import Algebra.Structures using (IsMonoid)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (Decidable)

open import Data.List.Properties
  using (++-assoc; ++-identityˡ; ++-identityʳ; length-++)

```

## List syntax

We can write lists more conveniently by introducing the following definitions:
```agda
ns : List ℕ
ns = 1 ∷ []

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
```


## Reverse

```agda
reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]
```

## Faster reverse

The definition above, while easy to reason about, is less efficient than
one might expect since it takes time quadratic in the length of the list.
The idea is that we generalise reverse to take an additional argument:
```agda
shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)
```
The definition is by recursion on the first argument. The second argument
actually becomes _larger_, but this is not a problem because the argument
on which we recurse becomes _smaller_.

Shunt is related to reverse as follows:
```agda
shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎
```
The proof is by induction on the first argument.
The base case instantiates to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs` and follows by the inductive
hypothesis and associativity of append.  When we invoke the inductive hypothesis,
the second argument actually becomes *larger*, but this is not a problem because
the argument on which we induct becomes *smaller*.

Generalising on an auxiliary argument, which becomes larger as the argument on
which we recurse or induct becomes smaller, is a common trick. It belongs in
your quiver of arrows, ready to slay the right problem.

## Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.

```agda
open import Data.Sum using (_⊎_; inj₁; inj₂)

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
   record { to = to xs ys; from = from xs ys }
 where 
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    Any P xs ⊎ Any P ys → Any P (xs ++ ys)

  extra : ∀ { A : Set} {P : A → Set} (xs ys : List A) → Any P xs -> Any P (xs ++ ys)
  extra (x ∷ xs) ys (here x₁) = here x₁
  extra (x ∷ xs) ys (there pf) = there (extra xs ys pf)

  to [] ys pf = inj₂ pf
  to (x ∷ xs) ys (here x₁) = inj₁ (here x₁)
  to (x ∷ xs) ys (there pf) with to xs ys pf
  ... | inj₁ x₁ = inj₁ (there x₁)
  ... | inj₂ y = inj₂ y
  from xs ys (inj₁ x) = extra xs ys x
  from [] ys (inj₂ y) = y
  from (x ∷ xs) ys (inj₂ y) = there (from xs ys (inj₂ y))



```

## Permutations

The relation that concerns us is "list `xs` is a permutation of list `ys`."

### Growth with zipper

The permtuation relation can be specified inductively by growing `xs` and `ys` simultaneously.
In this formulation, `xs` is always grown by adding a new element at the head, where `ys` 
can be grown by adding a new element anywhere.
List `ys` is represented by an instance of Huet's zipper: `ys = reverse ysˡ ++ ysʳ`.
The representation has three species of constructors:

  - Start with an empty list.

  - Grow the lists, growing `ys` at the "write head" of the zipper.

  - Move the "write head."


```agda
data Permutation++ {A : Set} : (xs ysˡ ysʳ : List A) -> Set where
  -- xs is a permutation of reverse ysˡ ++ ysʳ
  []   :  Permutation++ [] [] []
  there-left : {xs ysˡ ysʳ : List A} -> {y : A}
       -> Permutation++ xs (y ∷ ysˡ) ysʳ
       -> Permutation++ xs ysˡ (y ∷ ysʳ)
  there-right : {xs ysˡ ysʳ : List A} -> {z : A}
       -> Permutation++ xs ysˡ (z ∷ ysʳ)
       -> Permutation++ xs (z ∷ ysˡ) ysʳ
  here : {xs ysˡ ysʳ : List A} -> {x : A} -> Permutation++ xs ysˡ ysʳ
       -> Permutation++ (x ∷ xs) ysˡ (x ∷ ysʳ)
```

To relate two lists, I use a canonical form:

```agda
infix 4 _⋈-Z_
data _⋈-Z_ {A : Set} : (xs ys : List A) -> Set where
  permutation : ∀ {xs zs : List A} -> Permutation++ xs [] zs -> xs ⋈-Z zs
```

### Growth with insertion

The second representation is almost the same as the first,
but instead of using the zipper, it uses a separate judgement that says "a new element is inserted somewhere into `ys`.

```agda
data _⊳_≡_ {A : Set} : (x : A) (xs ys : List A) -> Set where
  -- x ⊳ xs ≡ ys when ys is formed by inserting x somewhere into xs
  here  : ∀ {x   : A} {xs    : List A} -> x ⊳ xs ≡ (x ∷ xs)
  there : ∀ {x y : A} {ys zs : List A} -> y ⊳ ys ≡ zs -> y ⊳ (x ∷ ys) ≡ (x ∷ zs)
```

A permutation is grown by starting with empty lists and inserting elements.

```agda
infix 4 _⋈_
data _⋈_ {A : Set} : (xs ys : List A) -> Set where
  [] : [] ⋈ []
  insert : ∀ {x : A} {xs ys zs : List A} -> x ⊳ ys ≡ zs -> xs ⋈ ys -> x ∷ xs ⋈ zs
```

#### Properties of insertions

The order of two insertions can be swapped.
This property is a key lemma that will be used to help prove transitivity.

```agda
insert-swap : ∀ {A : Set} {x y : A} {as bs cs : List A}
            -> x ⊳ as ≡ bs
            -> y ⊳ bs ≡ cs
            -> ∃[ es ] y ⊳ as ≡ es × x ⊳ es ≡ cs
insert-swap {as = as} {bs = bs} {cs = cs} (here {x = a}) (here {x = b}) =
   ⟨ (b ∷ as) , ⟨ here , there here ⟩ ⟩
insert-swap (here) (there {zs = zs} p2) = ⟨ zs , ⟨ p2 , here ⟩ ⟩
insert-swap (there {x = w} {ys = ys} p1) (here {x = y}) =
      ⟨ y ∷ w ∷ ys , ⟨ here , there (there p1) ⟩ ⟩
insert-swap (there { x = head } { y = inserted }p1) (there p2) with insert-swap p1 p2
... | ⟨ es , ⟨ y-into-as , x-into-es ⟩ ⟩ = ⟨ head ∷ es , ⟨ (there y-into-as) , (there x-into-es) ⟩ ⟩
```


#### Equivalence properties

Permutation is an equivalence relation.

```agda
refl-⋈ : ∀ {A : Set} {xs : List A} -> xs ⋈ xs
refl-⋈ {xs = xs} = self' xs
  where self' : ∀ {A : Set} (xs : List A) -> xs ⋈ xs
        self' [] = []
        self' (x ∷ xs) = insert here (self' xs)
```

For transitivity, the key property is that when `ys` is a permutation of `zs`,
and we know a smaller list `xs` that is used to form `ys`,
we can also find a smaller list `as` that is used to form `zs`,
such that `as` is a permutation of `xs`.

```agda
pullout-x : ∀ {A : Set} {x : A} {xs ys zs : List A}
      -> x ⊳ xs ≡ ys
      -> ys ⋈ zs
      -> ∃[ as ] x ⊳ as ≡ zs × xs ⋈ as
pullout-x here (insert {ys = ys} {zs = zs} a>as==bs perm) = ⟨ ys , ⟨ a>as==bs , perm ⟩ ⟩
pullout-x {xs = y' ∷ _} (there insertion) (insert here ys'⋈as) 
    with pullout-x insertion ys'⋈as
... | ⟨ bs , ⟨ z>bs=ys , ys⋈bs ⟩ ⟩ = ⟨ y' ∷ bs , ⟨ there z>bs=ys ,  insert here ys⋈bs   ⟩ ⟩
pullout-x {zs = z' ∷ zs'} (there insertion) (insert (there y'>cs==zs') ys'⋈z'::cs) 
   with pullout-x insertion ys'⋈z'::cs
... | ⟨ cs , ⟨ here , xs'⋈cs ⟩ ⟩ = ⟨ zs' , ⟨ here , (insert y'>cs==zs' xs'⋈cs) ⟩ ⟩
... | ⟨ (z' ∷ ds) , ⟨ there x>ds=cs , xs'⋈z'∷ds ⟩ ⟩
        with insert-swap x>ds=cs y'>cs==zs'
...                | ⟨ es , ⟨ y'>ds=es , x>es=zs' ⟩ ⟩ = 
                         ⟨ (z' ∷ es) , ⟨ (there x>es=zs') , (insert (there y'>ds=es) xs'⋈z'∷ds) ⟩ ⟩
```

Once we can pull out an `x`, we prove transitivity by pulling it out and reinserting it.

```agda
trans-⋈ : ∀ {A : Set} {xs ys zs : List A} -> xs ⋈ ys -> ys ⋈ zs -> xs ⋈ zs
trans-⋈ [] [] = []
trans-⋈ {A} (insert x⊳as≡ys xs⋈as) ys⋈zs with pullout-x x⊳as≡ys ys⋈zs
... | ⟨ cs , ⟨ x⊳cs≡zs , as⋈cs ⟩ ⟩ = insert x⊳cs≡zs (trans-⋈ xs⋈as as⋈cs)
```

asdf

```agda
find-⋈ : ∀ {A : Set} {x : A} {xs ys zs : List A}
       -> (x ∷ xs) ⋈ ys
       -> ∃[ zs ] x ⊳ zs ≡ ys
find-⋈ (insert {ys = ys} pf _) = ⟨ ys , pf ⟩
 
data same-length {A B : Set} : (xs : List A) (ys : List B) -> Set where
  [] : same-length [] []
  same-∷ : ∀ {x : A} {y : B} {xs : List A} {ys : List B}
         -> same-length xs ys -> same-length (x ∷ xs) (y ∷ ys)

refl-same : ∀ {A : Set} {xs : List A} -> same-length xs xs
refl-same {A} {[]} = []
refl-same {A} {x ∷ xs} = same-∷ refl-same

trans-same : ∀ {A : Set} {xs ys zs : List A} -> same-length xs ys -> same-length ys zs -> same-length xs zs
trans-same [] [] = []
trans-same (same-∷ p1) (same-∷ p2) = same-∷ (trans-same p1 p2)

insert-same : ∀ {A : Set} {xs ys : List A} {x : A}
            -> x ⊳ xs ≡ ys -> same-length (x ∷ xs) ys
insert-same here = refl-same
insert-same (there pf) with insert-same pf
... | (same-∷ pf) =  (same-∷ (same-∷ pf))

⋈-same : ∀ {A : Set} {xs ys : List A} -> (xs ⋈ ys) -> same-length xs ys
⋈-same [] = []
⋈-same (insert x pf) with insert-same x | ⋈-same pf
... | same-∷ pf' | pf'' = same-∷ (trans-same pf'' pf')


reverse-insert : ∀ {A : Set} {x : A} {xs : List A}
               -> (x ∈ xs) -> ∃[ ys ] x ⊳ ys ≡ xs
reverse-insert (here {xs = ys} refl) = ⟨ ys , here ⟩
reverse-insert (there {x = y} x∈xs) with reverse-insert x∈xs
... | ⟨ ys , x>xs=ys ⟩ = ⟨ y ∷ ys , there x>xs=ys ⟩

⋈-head-swap : ∀ {A : Set} {x₁ x₂ : A} {xs ys : List A}
               -> xs ⋈ ys
               -> (x₁ ∷ x₂ ∷ xs) ⋈ (x₂ ∷ x₁ ∷ ys)
⋈-head-swap xs⋈ys = insert (there here) (insert here xs⋈ys)

⋈-Z-head-swap : ∀ {A : Set} {x₁ x₂ : A} {xs ys : List A}
               -> xs ⋈-Z ys
               -> (x₁ ∷ x₂ ∷ xs) ⋈-Z (x₂ ∷ x₁ ∷ ys)
⋈-Z-head-swap (permutation xs⋈ys) = permutation (there-left (here (there-right (here xs⋈ys))))



lemma-ins : ∀ {A : Set} {x : A} {xs ys ys' zs : List A}
          -> x ⊳ ys ≡ ys'
          -> Permutation++ zs xs ys
          -> Permutation++ (x ∷ zs) xs ys'
lemma-ins here perm = here perm
lemma-ins (there ins) perm with lemma-ins ins (there-right perm)
... | perm' = there-left perm'

legacy-insert : ∀ {A : Set} {x : A} {xs ys zs : List A}
              -> x ⊳ ys ≡ zs -> xs ⋈-Z ys -> x ∷ xs ⋈-Z zs
legacy-insert ins (permutation p) = permutation (lemma-ins ins p)

⋈→⋈-Z : ∀ {A : Set} {xs ys : List A} -> xs ⋈ ys -> xs ⋈-Z ys
⋈→⋈-Z [] = permutation []
⋈→⋈-Z (insert ins xs⋈ys) = legacy-insert ins (⋈→⋈-Z xs⋈ys)

shunt-⊳ : ∀ {A : Set} {x : A} {ys zs : List A} (xs : List A)
        -> x ⊳ ys ≡ zs
        -> x ⊳ shunt xs ys ≡ shunt xs zs
shunt-⊳ [] pf = pf
shunt-⊳ (y ∷ ys) pf = shunt-⊳ ys (there pf)

reverse-lemma : ∀ {A : Set} {xs ys zs : List A}
              -> Permutation++ zs xs ys -> zs ⋈ shunt xs ys
reverse-lemma [] = []
reverse-lemma {xs = []} (here p) with reverse-lemma p
... | p' = insert here p'
reverse-lemma {xs = x ∷ xs} (here p) = insert (shunt-⊳ xs (there here)) (reverse-lemma p)
reverse-lemma (there-left p) = reverse-lemma p
reverse-lemma (there-right p) = reverse-lemma p

⋈-Z→⋈ : ∀ {A : Set} {xs ys : List A} -> xs ⋈-Z ys -> xs ⋈ ys
⋈-Z→⋈ (permutation p) = reverse-lemma p

infix 4 _swapped-is_
data _swapped-is_ {A : Set} : List A -> List A -> Set where
  here : ∀ {x y : A} {zs : List A} -> x ∷ y ∷ zs swapped-is y ∷ x ∷ zs
  there : ∀ {z : A} {xs ys : List A} -> xs swapped-is ys -> z ∷ xs swapped-is z ∷ ys

infix 4 _swapped*-is_
data _swapped*-is_ {A : Set} : List A -> List A -> Set where
  refl : ∀ {xs : List A} -> xs swapped*-is xs
  swap : ∀ {xs ys zs : List A} -> (xs swapped-is ys) -> ys swapped*-is zs -> xs swapped*-is zs

swapped→⋈ : ∀ {A : Set} {xs ys : List A} (pf : xs swapped-is ys) -> xs ⋈ ys
swapped→⋈ here = insert (there here) refl-⋈
swapped→⋈ (there pf) = insert here (swapped→⋈ pf)

swapped*→⋈ : ∀ {A : Set} {xs ys : List A} (pf : xs swapped*-is ys) -> xs ⋈ ys
swapped*→⋈ refl = refl-⋈
swapped*→⋈ (swap one many) = trans-⋈ (swapped→⋈ one) (swapped*→⋈ many)

grow-swap* : ∀ {A : Set} {z : A} {xs ys : List A} -> xs swapped*-is ys -> z ∷ xs swapped*-is z ∷ ys
grow-swap* refl = refl
grow-swap* (swap pf* pf) = swap (there pf*) (grow-swap* pf)

⊳-swapped* : ∀ {A : Set} {x : A} {ys zs : List A} -> x ⊳ ys ≡ zs -> x ∷ ys swapped*-is zs
⊳-swapped* here = refl
⊳-swapped* (there pf) = swap here (grow-swap* (⊳-swapped* pf))

trans-swapped* :  ∀ {A : Set} {xs ys zs : List A} -> xs swapped*-is ys -> ys swapped*-is zs -> xs swapped*-is zs
trans-swapped* refl pf = pf
trans-swapped* (swap one many) rest = swap one (trans-swapped* many rest)

insert-swapped* : ∀ {A : Set} {x : A} {xs ys zs : List A} -> x ⊳ ys ≡ zs -> xs swapped*-is ys -> x ∷ xs swapped*-is zs
insert-swapped* here perm = grow-swap* perm
insert-swapped* {A} {x = x} {xs = as} {ys = b ∷ bs} {zs = c ∷ cs} 
           (there ins) many = trans-swapped*  (grow-swap* many)
                              (trans-swapped* (swap here (grow-swap* (⊳-swapped* ins)))
                                              refl)
  where l1 : x ∷ bs swapped*-is cs
        l2 : as swapped*-is b ∷ bs
        l3 : x ∷ as swapped*-is x ∷ b ∷ bs 
        l4 : x ∷ b ∷ bs swapped-is b ∷ x ∷ bs 
        l1 = ⊳-swapped* ins
        l2 = many
        l3 = grow-swap* many
        l4 = here

⋈→swapped* : ∀ {A : Set} {xs ys : List A} -> (xs ⋈ ys) -> (xs swapped*-is ys)
⋈→swapped* [] = refl
⋈→swapped* (insert ins pf) = insert-swapped* ins (⋈→swapped* pf)


insert-∈-left : ∀ {A : Set} {xs ys : List A} {x : A} -> x ⊳ xs ≡ ys -> x ∈ ys
insert-∈-left here = here refl
insert-∈-left (there pf) = there (insert-∈-left pf)

insert-∈-right : ∀ {A : Set} {xs ys : List A} {x y : A} -> x ⊳ xs ≡ ys -> y ∈ xs -> y ∈ ys
insert-∈-right here y∈xs = there y∈xs
insert-∈-right (there pf) (here refl) = here refl
insert-∈-right (there pf) (there y∈xs) = there (insert-∈-right pf y∈xs)

insert-breakdown : ∀ {A : Set} {xs ys : List A} {x y : A}
                 -> x ⊳ xs ≡ ys
                 -> y ∈ ys
                 -> y ≡ x ⊎ y ∈ xs
insert-breakdown here (here y≡x) = inj₁ y≡x
insert-breakdown (there ins) (here y≡x) = inj₂ (here y≡x)
insert-breakdown here (there y∈xs) = inj₂ y∈xs
insert-breakdown (there y⊳zs≡xs) (there y∈xs) with insert-breakdown y⊳zs≡xs y∈xs
... | inj₁ y≡x = inj₁ y≡x
... | inj₂ y∈xs = inj₂ (there y∈xs)

⋈-∈ : ∀ {A : Set} {xs ys : List A} -> (xs ⋈ ys) -> ∀ {x : A} -> (x ∈ xs) ⇔ (x ∈ ys)
⋈-∈ {xs = xs} {ys = ys} xs⋈ys! {x} = record { to = to xs⋈ys! ; from = from xs⋈ys! }
  where to : ∀ {A : Set} {xs ys : List A} -> (xs ⋈ ys) -> ∀ {x : A} -> (x ∈ xs) -> (x ∈ ys)
        to (insert x⊳ys≡zs _) (here refl) = insert-∈-left x⊳ys≡zs
        to (insert x⊳ys≡zs pf) (there x∈xs) = insert-∈-right x⊳ys≡zs (to pf x∈xs)

        from : ∀ {A : Set} {xs ys : List A} -> (xs ⋈ ys) -> ∀ {x : A} -> (x ∈ ys) -> (x ∈ xs)
        from (insert here pf) (here refl) = here refl
        from (insert (there x⊳ys≡zs) pf) (here refl) = there (from pf (here refl))
        from (insert x⊳bs≡y∷ys xs⋈bs) z∈ys with insert-breakdown x⊳bs≡y∷ys z∈ys
        ... | inj₁ x≡y = here x≡y
        ... | inj₂ x∈ys = there (from xs⋈bs x∈ys)


cong-⋈ : ∀ {A : Set} {xs ys zs : List A}
        -> ys ≡ zs -> xs ⋈ ys -> xs ⋈ zs
cong-⋈ refl pf = pf


sym-⋈  : ∀ {A : Set} {xs ys : List A} -> xs ⋈ ys -> ys ⋈ xs
sym-⋈ [] = []
sym-⋈ (insert here pf) = insert here (sym-⋈ pf)
sym-⋈ (insert {ys = y ∷ ys} (there {y = x} x⊳ys≡zs) pf) with sym-⋈ pf
... | thing = {!!}



module ⋈-Reasoning {A : Set} where

  infix  1 begin⋈_
  infixr 2 _⋈⟨⟩_ step-⋈ step-≡-⋈
  infix  3 _∎⋈

  begin⋈_ : ∀ {x y : List A}
    → x ⋈ y
      -----
    → x ⋈ y
  begin⋈ x⋈y  =  x⋈y

  _⋈⟨⟩_ : ∀ (x : List A) {y : List A}
    → x ⋈ y
      -----
    → x ⋈ y
  x ⋈⟨⟩ x⋈y  =  x⋈y

  step-⋈ : ∀ (x {y z} : List A) → y ⋈ z → x ⋈ y → x ⋈ z
  step-⋈ x y⋈z x⋈y  =  trans-⋈ x⋈y y⋈z

  step-≡-⋈ : ∀ (xs : List A)  {ys zs : List A} → ys ⋈ zs -> xs ≡ ys -> xs ⋈ zs
  step-≡-⋈ xs xs⋈ys refl = xs⋈ys

  syntax step-⋈ x y⋈z x⋈y  =  x ⋈⟨  x⋈y ⟩ y⋈z
  syntax step-≡-⋈ xs xs⋈ys zs≡xs  =  xs ⋈≡⟨ zs≡xs ⟩ xs⋈ys

  _∎⋈ : ∀ (x : List A)
      -----
    → x ⋈ x
  x ∎⋈  =  refl-⋈

open ⋈-Reasoning


data Order (m n : ℕ) : Set where
  less : m ≤ n -> Order  m n
  greater : n ≤ m -> Order  m n

compare : (m n : ℕ) -> Order m n
compare zero n = less z≤n
compare (suc m) zero = greater z≤n
compare (suc m) (suc n) with compare m n
... | less x = less (s≤s x)
... | greater x = greater (s≤s x)


data Maybe (A : Set) : Set where
  Just : A -> Maybe A
  Nothing : Maybe A

data Heap : List ℕ -> Set where
  [] : Heap []
  root : ∀ {xs ys ns : List ℕ} 
       -> (n : ℕ)
       -> Heap xs
       -> Heap ys
       -> (∀ {m : ℕ} -> (m ∈ ns) -> n ≤ m)
       -> ns ⋈ n ∷ (xs ++ ys)
       -> Heap ns

open import Data.Nat.Properties using (≤-trans; ≤-refl)



--min : ∀ {ns : List ℕ} (h : Heap ns)
--    -> ∃[ n ] n ∈ ns
--    -> ∃[ n ] n ∈ ns × (∀ {m : ℕ} -> m ∈ ns -> n ≤ m)
--min {ns} (root {xs = xs} {ys = ys} n left right small-l small-r perm) _ = ⟨ n , ⟨ n∈ns , smallest ⟩ ⟩
--  where n∈ns : n ∈ ns
--        open _⇔_
--        n∈ns = from (⋈-∈ perm) (here refl)
--        smallest : ∀ {m : ℕ} → m ∈ ns → n ≤ m
--        smallest {m} m∈ns with to (⋈-∈ perm) m∈ns
--        ... | here refl = ≤-refl
--        ... | there m∈xs++ys with to (Any-++-⇔ xs ys) m∈xs++ys
--        ... | inj₁ m∈xs = small-l m∈xs
--        ... | inj₂ m∈ys = small-r m∈ys



insert-snoc :  ∀ {A : Set} {xs ys : List A} {x z : A}
            -> x ⊳ xs ≡ ys
            -> x ⊳ (xs ++ [ z ]) ≡ (ys ++ [ z ])
insert-snoc here = here
insert-snoc (there pf) = there (insert-snoc pf)

cong-⋈-snoc : ∀ {A : Set} {xs ys : List A} {z : A}
           -> xs ⋈ ys
           -> xs ++ [ z ] ⋈ ys ++ [ z ]
cong-⋈-snoc [] = refl-⋈
cong-⋈-snoc (insert x pf) = insert (insert-snoc x) (cong-⋈-snoc pf)

cong-⋈-++ : ∀ {A : Set} {xs ys zs : List A}
           -> xs ⋈ ys
           -> xs ++ zs ⋈ ys ++ zs
cong-⋈-++ {xs = xs} {ys = ys} {zs = []} xs⋈ys rewrite ++-identityʳ xs | ++-identityʳ ys = xs⋈ys
cong-⋈-++ {xs = xs} {ys = ys} {zs = z ∷ zs} pf = 
  begin⋈
    xs ++ z ∷ zs
  ⋈≡⟨ sym (++-assoc xs [ z ] zs) ⟩
    (xs ++ [ z ]) ++ zs
  ⋈⟨ cong-⋈-++ (cong-⋈-snoc pf) ⟩
    (ys ++ [ z ]) ++ zs
  ⋈≡⟨ ++-assoc ys [ z ] zs ⟩
    ys ++ z ∷ zs
  ∎⋈

merge-heaps : ∀ {ns ms : List ℕ} -> Heap ns -> Heap ms -> Heap (ns ++ ms)
merge-heaps [] h = h
merge-heaps {ns = ns} h [] rewrite ++-identityʳ ns = h
merge-heaps {ns = ns} {ms = ms}
            h₁@(root {xs = xs} {ys = ys} {ns = ns₁} n₁ l₁ r₁ small₁ perm1)
            h₂@(root {ns = ns₂} n₂ l₂ r₂ small₂ perm2) 
  with compare n₁ n₂
... | less n₁≤n₂ = root n₁ l₁ (merge-heaps r₁ h₂) lemma2 lemma1
        where lemma1 : ns ++ ms ⋈ n₁ ∷ xs ++ ys ++ ms
              lemma2 : ∀ {m : ℕ} → m ∈ ns ++ ms → n₁ ≤ m
              lemma1 = begin⋈
                         ns ++ ms
                       ⋈⟨ cong-⋈-++ perm1 ⟩
                         (n₁ ∷ xs ++ ys) ++ ms
                       ⋈≡⟨ refl ⟩
                         n₁ ∷ (xs ++ ys) ++ ms
                       ⋈≡⟨ cong (_∷_ n₁) (++-assoc xs ys ms) ⟩
                         n₁ ∷ xs ++ ys ++ ms
                       ∎⋈

              open _⇔_

              lemma2 {m} m∈list with to (Any-++-⇔ ns ms) m∈list
              ... | inj₁ m∈ns = small₁ m∈ns
              ... | inj₂ m∈ms = ≤-trans n₁≤n₂ (small₂ m∈ms)
... | greater n₂≤n₂ = {!!}

heap-elements : ∀ {ns : List ℕ} -> Heap ns -> ∃[ ms ] ms ≡ ns
heap-elements [] = ⟨ [] , refl ⟩
heap-elements (root {ns = ns} n h h₁ x x₁) = ⟨ ns , refl ⟩

data length_is_ {A : Set} : List A -> ℕ -> Set where
  [] : length [] is zero
  there : ∀ {a : A} {as : List A} {k : ℕ} -> length as is k -> length (a ∷ as) is (suc k)


insert-length : ∀ {A : Set} {x : A} {xs ys : List A} {k : ℕ}
              -> x ⊳ xs ≡ ys -> length xs is k -> length ys is (suc k)
insert-length here len = there len
insert-length (there ins) (there len) = there (insert-length ins len)

insert-length' : ∀ {A : Set} {x : A} {xs ys : List A} {k : ℕ}
              -> x ⊳ xs ≡ ys -> length ys is suc k -> length xs is k
insert-length' here (there len) = len
insert-length' (there ins) (there (there len)) = there (insert-length' ins (there len))




length-pred :  ∀ {A : Set} {x : A} {xs : List A} {k : ℕ}
            -> length (x ∷ xs) is (suc k) -> length xs is k
length-pred (there pf) = pf

length-perm : ∀ {A : Set} {xs ys : List A} {k : ℕ} -> length xs is k -> xs ⋈ ys -> length ys is k
length-perm [] [] = []
length-perm (there pf) (insert here perm) = there (length-perm pf perm)
length-perm (there (there as-l-k)) (insert (there a⊳ys≡zs) (insert x⊳xs≡ys perm))
   = there (insert-length a⊳ys≡zs (length-pred (insert-length x⊳xs≡ys (length-perm as-l-k perm))))

delete-min : ∀ {ns : List ℕ} {k : ℕ}
           -> length ns is suc k
           -> (h : Heap ns)
           -> ∃[ m ] ∃[ ms ] Heap ms × length ms is k × (ns ⋈ m ∷ ms) × (∀ {z : ℕ} -> (z ∈ ns) -> m ≤ z)
delete-min (len) (root n left right small perm) with heap-elements (merge-heaps left right)
... | ⟨ elements , refl ⟩ =
        ⟨ n , ⟨ elements , ⟨ newheap , ⟨ length-pred (length-perm len perm) , ⟨ perm , small ⟩ ⟩ ⟩ ⟩ ⟩
  where newheap = merge-heaps left right

singleton-heap : ∀ (n : ℕ) -> Heap [ n ]
singleton-heap n = root n [] [] (λ { (here refl) → ≤-refl}) refl-⋈

insert-in-heap : ∀ {ns : List ℕ} -> (n : ℕ) -> Heap ns -> Heap (n ∷ ns)
insert-in-heap n h = merge-heaps (singleton-heap n) h


build-heap : (ns : List ℕ) -> Heap ns
build-heap [] = []
build-heap (n ∷ ns) = insert-in-heap n (build-heap ns)

----------------------------------------------------------------

data Ordered : (List ℕ -> Set) where
  ordered-[] : Ordered []
  ordered-[x] : ∀ {n : ℕ} -> Ordered [ n ]
  ordered-∷ : ∀ {n₁ n₂ : ℕ} {ns : List ℕ} -> n₁ ≤ n₂ -> Ordered (n₂ ∷ ns) 
            -> Ordered (n₁ ∷ n₂ ∷ ns)


≤-congruence : ∀ {x y z : ℕ} -> (x ≤ y) -> (y ≡ z) -> (x ≤ z)
≤-congruence pf refl = pf

Ordered-≤ : ∀ (n : ℕ) (ns : List ℕ) -> Ordered (n ∷ ns) ⇔ (Ordered ns × (∀ (y : ℕ) -> (y ∈ ns) -> n ≤ y))
Ordered-≤ n ns = record { to = to n ns ; from = from n ns }
  where to : ∀ (n : ℕ) (ns : List ℕ) -> Ordered (n ∷ ns) -> (Ordered ns × (∀ (y : ℕ) ->  (y ∈ ns) -> n ≤ y))
        from : ∀ (n : ℕ) (ns : List ℕ) -> (Ordered ns × (∀ (y : ℕ) -> (y ∈ ns) -> n ≤ y)) -> Ordered (n ∷ ns)

        to n [] ordered-[x] = ⟨ ordered-[] , (λ y ()) ⟩
        to n (m ∷ ms) (ordered-∷ n≤m pf) with to m ms pf
        ... | ⟨ _ , m≤ms ⟩ = ⟨ pf , (λ y → λ{ (here x) → ≤-congruence n≤m (sym x)
                                            ; (there x) → ≤-trans n≤m (m≤ms y x)}) ⟩
        from n [] ⟨ O-ns , n≤ns ⟩ = ordered-[x]
        from n (x ∷ xs) ⟨ ordered-x∷xs , n≤x∷xs ⟩ =
          ordered-∷ (n≤x∷xs x (here refl)) ordered-x∷xs

open _⇔_



drain-heap : ∀ {ns : List ℕ} {n : ℕ} -> (length ns is n) -> Heap ns -> ∃[ ms ] ns ⋈ ms × Ordered ms
drain-heap {[]} {zero} pf [] = ⟨ [] , ⟨ [] , ordered-[] ⟩ ⟩
drain-heap {z ∷ zs} {suc k} (length) h@(root n _ _ orig-order perm)
  with delete-min length h -- ⟨ n , from (⋈-∈ perm) (here refl) ⟩
... | ⟨ min , ⟨ ms , ⟨ newheap , ⟨ len , ⟨ perm1 , small ⟩ ⟩ ⟩ ⟩ ⟩ with drain-heap len newheap
... | ⟨ rest , ⟨ ms⋈rest , ordered ⟩ ⟩ = ⟨ min ∷ rest , ⟨ fullperm , fullorder ⟩ ⟩
  where smallest = λ y y∈rest → small (from (⋈-∈ perm1) (there (from (⋈-∈ ms⋈rest) y∈rest)))
        fullorder = from (Ordered-≤ min rest) ⟨ ordered , smallest ⟩
        fullperm : z ∷ zs ⋈ min ∷ rest
        fullperm = 
           begin⋈
             z ∷ zs
           ⋈⟨ perm1 ⟩ 
             min ∷ ms
           ⋈⟨ insert here ms⋈rest ⟩ 
             min ∷ rest
           ∎⋈

             
length-++-is : ∀ {A : Set} {xs ys : List A} {k1 k2 : ℕ}
          -> length xs is k1
          -> length ys is k2
          -> length (xs ++ ys) is (k1 + k2)
length-++-is [] l2 = l2
length-++-is (there l1) l2 = there (length-++-is l1 l2)

heap-size : ∀ {ns : List ℕ} -> Heap ns -> ∃[ k ] length ns is k
heap-size [] = ⟨ zero , [] ⟩
heap-size (root _ left right _ perm) with heap-size left | heap-size right 
... | ⟨ kₗ , lenₗ ⟩ | ⟨ kᵣ , lenᵣ ⟩ =
   ⟨ 1 + kₗ + kᵣ , length-perm (there (length-++-is lenₗ lenᵣ)) (sym-⋈ perm) ⟩

           -- 
heapsort : (ns : List ℕ) -> ∃[ ms ] ns ⋈ ms × Ordered ms
heapsort ns with heap-size (build-heap ns)
... | ⟨ _ , len ⟩ = drain-heap len (build-heap ns)


            
--    -> ∃[ n ] n ∈ ns
--    -> ∃[ n ] n ∈ ns × (∀ {m : ℕ} -> m ∈ ns -> n ≤ m)
--min {ns} (root {xs = xs} {ys = ys} n left right small-l small-r perm) _ = ⟨ n , ⟨ n∈ns , smallest

----data STree {A : Set} : (zs : List A) -> Set where
----  [] : STree []
----  [x] : ∀ (x : A) -> STree ([ x ])
----  fork : ∀ {xs ys ns : List A} -> STree xs -> STree ys -> Permutation++ ns xs ys -> STree ns
----
----
----pswap : ∀ {A : Set} {xs ys zs : List A} -> Permutation++ xs ys zs -> Permutation++ xs zs ys
----pswap [] = []
----pswap (here p) = there-right (here (pswap p))
----pswap (there-left p) = there-right (pswap p)
----pswap (there-right p) = there-left (pswap p)
----
----perm-symmetric : ∀ {A : Set} {zs zs' : List A} -> Permutation++ zs [] zs' -> Permutation++ zs' [] zs
----perm-symmetric [] = []
----perm-symmetric (here p) = here (perm-symmetric p)
----perm-symmetric (there-left p) = {!!}
----
----
----tree-∷ : ∀ {A : Set} -> (x : A) -> {ns : List A} -> (STree ns) -> STree (x ∷ ns)
----tree-∷ x [] = [x] x
----tree-∷ x ([x] y) = fork ([x] x) ([x] y) (there-right (here (here [])))
----tree-∷ x (fork xs ys p) = fork (tree-∷ x ys) xs (pswap (here p))
----
----tree-of-list : ∀ {A : Set} -> (xs : List A) -> STree xs
----tree-of-list [] = []
----tree-of-list (x ∷ xs) = tree-∷ x (tree-of-list xs)
----
----empty-perm-left' : ∀ {A : Set} (y : A) (ys zs : List A) -> ¬ (Permutation++ [] (y ∷ ys) zs)
----empty-perm-right' : ∀ {A : Set} (y : A) (ys zs : List A) -> ¬ (Permutation++ [] zs (y ∷ ys))
----
----empty-perm-left' y ys (z ∷ zs) (there-left pf) = empty-perm-left' z (y ∷ ys) zs pf
----empty-perm-left' y ys (zs) (there-right pf) = empty-perm-right' y zs ys pf
----empty-perm-right' y ys zs (there-left pf) = empty-perm-left' y zs ys pf
----empty-perm-right' y ys (z ∷ zs) (there-right pf) = empty-perm-right' z (y ∷ ys) zs pf
----
----empty-perm-left : ∀ {A : Set} {y : A} {ys zs : List A} -> ¬ (Permutation++ [] (y ∷ ys) zs)
----empty-perm-left {A} {y} {ys} {zs} = empty-perm-left' y ys zs
----
----
------perm-lemma-5 : ∀ {A : Set} {xs ys zs xs' : List A}
------             -> Permutation++ xs ⋈ xs'
------             -> zs ⋈ (shunt xs ys)
------             -> zs ⋈ (shunt xs' ys)
----
----perm-find-z : ∀ {A : Set} {xs ys zs : List A} (z : A)
----          -> Permutation++ (z ∷ zs) xs ys
----          -> ∃[ xs' ] ∃[ ys' ] Permutation++ zs xs' ys'
----perm-find-z _ (here {zs} {xs} {ys} {x} pf) = ⟨ xs , ⟨ ys , pf ⟩ ⟩
----perm-find-z z (there-left pf) = perm-find-z z pf
----perm-find-z z (there-right pf) = perm-find-z z pf
----
----
----perm-cons : ∀ {A : Set} {z : A} {xs ys : List A}
----          -> xs ⋈ ys -> (z ∷ xs) ⋈ (z ∷ ys)
----perm-cons (permutation x) = permutation (here x)
----
----perm-swap++ : ∀ {A : Set} {y1 y2 : A} {xs ys zs : List A}
----          -> Permutation++ zs xs (y1 ∷ y2 ∷ ys)
----          -> Permutation++ zs xs (y2 ∷ y1 ∷ ys)
----perm-swap++ (here pf) = there-left (here (there-right pf))
----perm-swap++ (there-left (here pf)) = here (there-left pf)
----perm-swap++ (there-left (there-left pf)) = {!!}
----perm-swap++ (there-left (there-right pf)) = perm-swap++ pf
----perm-swap++ (there-right pf) = {!!}
----
------canonical-perm : ∀ {A : Set} {xs xs' : List A}
------               -> xs ⋈ xs'
------               -> Permutation++ xs [] xs'
------canonical-perm (permutation []) = {!!}
------canonical-perm (permutation (here pf)) = {!!}
------canonical-perm (permutation (there-left pf)) = {!!}
----
----find-element-perm : ∀ {A : Set} {x : A} (xs : List A) -> (x ∈ xs)
----                  -> ∃[ zs ] xs ⋈ (x ∷ zs)
----find-element-perm (x ∷ xs) (here refl) = ⟨ xs , self-permutation (x ∷ xs) ⟩
----find-element-perm { x = y } (x ∷ xs) (there y∈xs) with find-element-perm xs y∈xs
----... | ⟨ xs' , perm' ⟩ = ⟨ x ∷ xs' , {!!} ⟩
----
----
----
----perm-find-x : ∀ {A : Set} {xs ys zs : List A} (x : A)
----          -> Permutation++ zs (x ∷ xs) ys
----          -> ∃[ zs' ] Permutation++ zs' xs ys
----perm-find-x {zs = zs} x perm 
----        with (_⇔_.from (perm-membership (there-left perm)) (inj₂ (here refl)))
----... | x∈zs with find-element-perm zs x∈zs
----... | ⟨ zs' , permutation perm' ⟩ = ⟨ zs' , {!!} ⟩
------perm-find-x x (there-left pf) = {!!}
------perm-find-x x (there-right pf) = {!!}
----
----
----
----perm-swap : ∀ {A : Set} {y1 y2 : A} {xs ys : List A}
----          -> xs ⋈ (y1 ∷ y2 ∷ ys)
----          -> xs ⋈ (y2 ∷ y1 ∷ ys)
----perm-swap (permutation (here pf)) = permutation (there-left (here (there-right pf)))
----perm-swap {ys = []} (permutation (there-left (here pf))) = permutation (here (there-left pf))
----perm-swap {ys = []} (permutation (there-left (there-left (there-right pf)))) =
----  perm-swap (permutation (there-left pf))
----perm-swap {ys = []} (permutation (there-left (there-right pf))) = perm-swap (permutation pf)
----perm-swap {ys = z ∷ zs} (permutation (there-left {xs} {[]} {(z1 ∷ z2 ∷ zs)} {y} pf)) =
----   permutation {!!}
------... | thing = permutation {!!}
----
----perm-find : ∀ {A : Set} {as : List A}
----          -> ∀ {a : A} -> a ∈ as -> ∃[ as' ] as ⋈ (a ∷ as')
----perm-find (here {x} {xs} refl) = ⟨ xs , self-permutation (x ∷ xs)  ⟩
----perm-find {A} {as} {a} (there {x} {xs} pf) with perm-find pf
----... | ⟨ ys , pys ⟩ = ⟨ (x ∷ ys) , perm-swap (perm-cons pys) ⟩
----
----open import Data.Empty using (⊥-elim)
----
----perm-lemma-4 : ∀ {A : Set} {xs ys zs xs' : List A}
----             -> xs ⋈ xs'
----             -> zs ⋈ (shunt xs ys)
----             -> zs ⋈ (shunt xs' ys)
------perm-lemma-4 xs⋈xs' zs⋈Rxs++ys = {!!}
----perm-lemma-4 (permutation xs⋈xs') (permutation zs⋈Rxs++ys) = permutation {!!}
----
----perm-lemma-3 : ∀ {A : Set} {xs ys zs xs' : List A}
----             -> xs ⋈ xs'
----             -> Permutation++ zs xs ys
----             -> Permutation++ zs xs' ys
----perm-lemma-3 (permutation []) [] = []
----perm-lemma-3 (permutation (there-left pf)) [] = ⊥-elim (empty-perm-left pf)
----perm-lemma-3 xs⋈xs' (here zxy) = here (perm-lemma-3 xs⋈xs' zxy)
----perm-lemma-3 xs⋈xs' (there-left {xs = yyy} {y = y} zxy) 
----  = there-left {!!}
----perm-lemma-3 (permutation x) (there-right zxy) = {!!}
----
----perm-lemma-2 : ∀ {xs ys zs xs' ys' zs' : List ℕ}
----             -> xs ⋈ xs'
----             -> ys ⋈ ys'
----             -> Permutation++ zs' xs' ys'
----             -> Permutation++ zs xs ys
----             -> zs ⋈ zs'
------perm-lemma-2 xs⋈xs' ys⋈ys' zxy' zxy = {!!}
----perm-lemma-2 xs⋈xs' ys⋈ys' zxy' zxy = {!!}             
----
----
----perm-lemma-1 : ∀ {xs ys zs xs' ys' zs' : List ℕ}
----             -> xs ⋈ xs'
----             -> ys ⋈ ys'
----             -> Permutation++ zs' xs' ys'
----             -> zs ⋈ zs'
----perm-lemma-1  = {!!}
----
----
----


```

## Orphans

```agda
insertion : ∀ {A : Set} {x : A} {xs zs : List A} -> x ⊳ xs ≡ zs -> (x ∷ xs) ⋈ zs
insertion here = insert here refl-⋈
insertion (there pf) = insert (there pf) refl-⋈
```

## Unicode

This chapter uses the following unicode:

    ∷  U+2237  PROPORTION  (\::)
    ⊗  U+2297  CIRCLED TIMES  (\otimes, \ox)
    ∈  U+2208  ELEMENT OF  (\in)
    ∉  U+2209  NOT AN ELEMENT OF  (\inn, \notin)
