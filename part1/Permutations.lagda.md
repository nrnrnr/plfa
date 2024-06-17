---
title     : "Permutations: A precursor to proving sorting algorithms correct"
permalink : /Permutations/
---

```agda
module cs.plfa.part1.Permutations where
```

A sorting algorithm is correct only if its output is a 
permutation of its input.
This page presents multiple ways to formalize permutations.
The formalizations are presented in the order in which I explored
them:

  - A representation based on Huet's zipper

  - A representation based on a separate insertion judgment, inspired
    by Andras Kovacs

  - The reflexive, transitive closure of single swaps of adjacent elements

  - The representation in the standard library, which is a better
    representation of the reflexive, transitive closure of single
    swaps

All the formalizations are equivalent, but 
the library representation is likely the best.
The end of the document includes some useful lemmas involving
permutations of lists formed with `++`.

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
open import cs.plfa.part1.Isomorphism using (_≃_; _⇔_)

open import Data.List using (List; _++_; length; map; foldr; downFrom; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
  renaming (mapIsFold to map-is-foldr)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

## Zipping up the zipper

A zipper represents a "list with pointer" 
as the reverse of the head, followed by the tail.
The abstraction function is the `shunt` function from the Lists chapter.

```agda
shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)
```

## Permutations

The relation that concerns us is "list `xs` is a permutation of list `ys`."

### Permutations via growth with zipper

The permtuation relation can be specified inductively by growing `xs` and `ys` simultaneously.
In this formulation, `xs` is always grown by adding a new element at the head, where `ys` 
can be grown by adding a new element anywhere.
List `ys` is represented by an instance of Huet's zipper: `ys = reverse ysˡ ++ ysʳ`.
The representation has three species of constructors:

  - Start with an empty list.

  - Grow the lists, growing `ys` at the "write head" of the zipper.

  - Move the "write head."


```agda
data Permutation-Zipper {A : Set} : (xs ysˡ ysʳ : List A) -> Set where
  -- `xs` is a permutation of `reverse ysˡ ++ ysʳ`
  []   :  Permutation-Zipper [] [] []
  there-left : {xs ysˡ ysʳ : List A} -> {y : A}
       -> Permutation-Zipper xs (y ∷ ysˡ) ysʳ
       -> Permutation-Zipper xs ysˡ (y ∷ ysʳ)
  there-right : {xs ysˡ ysʳ : List A} -> {z : A}
       -> Permutation-Zipper xs ysˡ (z ∷ ysʳ)
       -> Permutation-Zipper xs (z ∷ ysˡ) ysʳ
  here : {xs ysˡ ysʳ : List A} -> {x : A} -> Permutation-Zipper xs ysˡ ysʳ
       -> Permutation-Zipper (x ∷ xs) ysˡ (x ∷ ysʳ)
```

To relate two lists, I use a canonical form:

```agda
infix 4 _Zip⋈_
data _Zip⋈_ {A : Set} : (xs ys : List A) -> Set where
  permutation : ∀ {xs zs : List A} -> Permutation-Zipper xs [] zs -> xs Zip⋈ zs
```

### Permutations via growth with insertion

The second representation is almost the same as the first,
but instead of using the zipper, it uses a separate judgement that
says "a new element is inserted somewhere into `ys`.


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

This representation is a simplified version of [one 
implemented by Andras
Kovacs](https://gist.github.com/AndrasKovacs/0d7bcc3aba513c29ef73/);
Kovacs's representation uses insertion on *both* sides, not just one.
Using insertion on both sides seems to complicate the proof of
transitivity.

A super-common idiom is to add an element to the front of both
sides of a permutation:

```agda
--⋈-∷ : ∀ {A : Set} {z : A} {xs ys : List A}
--    -> xs ⋈ ys
--    -> z ∷ xs ⋈ z ∷ ys
pattern ⋈-∷ perm = insert here perm
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

Find an insertion that places any element in its list.
That is,
given `x` and `xs`, compute `ys` such that `x ⊳ ys ≡ xs`.

```agda
reverse-insert : ∀ {A : Set} {x : A} {xs : List A}
               -> (x ∈ xs) -> ∃[ ys ] x ⊳ ys ≡ xs
reverse-insert (here {xs = ys} refl) = ⟨ ys , here ⟩
reverse-insert (there {x = y} x∈xs) with reverse-insert x∈xs
... | ⟨ ys , x>xs=ys ⟩ = ⟨ y ∷ ys , there x>xs=ys ⟩
```

#### Insertions and list membership

When `x ⊳ xs ≡ ys`, the elements of `ys` are exactly `x` plus the elements of `xs`.

```
inserted-∈-result      : ∀ {A : Set} {xs ys : List A} {x : A}
                       -> x ⊳ xs ≡ ys
                       -> x ∈ ys
inserted-into-⊆-result : ∀ {A : Set} {xs ys : List A} {x y : A} 
                       -> x ⊳ xs ≡ ys
                       -> y ∈ xs
                       -> y ∈ ys
result-⊆-inserted-⊎-inserted-into 
                       : ∀ {A : Set} {xs ys : List A} {x y : A}
                       -> x ⊳ xs ≡ ys
                       -> y ∈ ys
                       -> y ≡ x ⊎ y ∈ xs

inserted-∈-result here = here refl
inserted-∈-result (there pf) = there (inserted-∈-result pf)

inserted-into-⊆-result here y∈xs = there y∈xs
inserted-into-⊆-result (there pf) (here refl) = here refl
inserted-into-⊆-result (there pf) (there y∈xs) = there (inserted-into-⊆-result pf y∈xs)

result-⊆-inserted-⊎-inserted-into here (here y≡x) = inj₁ y≡x
result-⊆-inserted-⊎-inserted-into (there ins) (here y≡x) = inj₂ (here y≡x)
result-⊆-inserted-⊎-inserted-into here (there y∈xs) = inj₂ y∈xs
result-⊆-inserted-⊎-inserted-into (there y⊳zs≡xs) (there y∈xs) 
  with result-⊆-inserted-⊎-inserted-into y⊳zs≡xs y∈xs
... | inj₁ y≡x = inj₁ y≡x
... | inj₂ y∈xs = inj₂ (there y∈xs)
```


#### Equivalence properties of the permutation relation

Permutation is an equivalence relation.

```agda
refl-⋈ : ∀ {A : Set} {xs : List A} -> xs ⋈ xs
refl-⋈ {xs = xs} = self' xs
  where self' : ∀ {A : Set} (xs : List A) -> xs ⋈ xs
        self' [] = []
        self' (x ∷ xs) = ⋈-∷ (self' xs)
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
... | ⟨ bs , ⟨ z>bs=ys , ys⋈bs ⟩ ⟩ = ⟨ y' ∷ bs , ⟨ there z>bs=ys ,  ⋈-∷ ys⋈bs   ⟩ ⟩
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

To prove symmetry, I use a lemma that says I can pull the right-hand side's head
out of a left-hand side/

```agda
pullout-rhs : ∀ {A : Set} {y : A} {xs ys : List A}
           -> xs ⋈ (y ∷ ys)
           -> ∃[ ws ] y ⊳ ws ≡ xs × ws ⋈ ys
pullout-rhs {xs = y ∷ ws}
            (insert here ws⋈ys) = ⟨ ws , ⟨ here , ws⋈ys ⟩ ⟩
pullout-rhs {xs = w ∷ ws}
            (insert (there w⊳zs≡ys) ws⋈y∷zs) with pullout-rhs ws⋈y∷zs
... | ⟨ vs , ⟨ y⊳vs≡ws , vs⋈zs ⟩ ⟩ = ⟨ w ∷ vs , ⟨ there y⊳vs≡ws , insert w⊳zs≡ys vs⋈zs ⟩ ⟩

sym-⋈  : ∀ {A : Set} {xs ys : List A} -> xs ⋈ ys -> ys ⋈ xs
sym-⋈ [] = []
sym-⋈ {ys = y ∷ ys} pf@(insert _ _) with pullout-rhs pf
... | ⟨ ws , ⟨ y⊳ws≡xs , ws⋈ys ⟩ ⟩ = insert y⊳ws≡xs (sym-⋈ ws⋈ys)
```



### Permutation by repeated swapping

List `ys` is a permutation of `xs` if `ys` can be obtained from `xs` by 
swapping adjacent elements.
A single swap is represented by relation `_swapped-is_`.

```agda
infix 4 _swapped-is_
data _swapped-is_ {A : Set} : List A -> List A -> Set where
  here : ∀ {x y : A} {zs : List A} -> x ∷ y ∷ zs swapped-is y ∷ x ∷ zs
  there : ∀ {z : A} {xs ys : List A} -> xs swapped-is ys -> z ∷ xs swapped-is z ∷ ys
```

Permutation is the transitive, reflexive closure of `_swapped-is_`.

```agda
infix 4 _swapped*-is_
data _swapped*-is_ {A : Set} : List A -> List A -> Set where
  refl : ∀ {xs : List A} -> xs swapped*-is xs
  swap : ∀ {xs ys zs : List A} -> (xs swapped-is ys) -> ys swapped*-is zs -> xs swapped*-is zs
```

The transitive, reflexive closure is in fact transitive.

```agda
trans-swapped* :  ∀ {A : Set} {xs ys zs : List A}
               -> xs swapped*-is ys
               -> ys swapped*-is zs
               -> xs swapped*-is zs
trans-swapped* refl pf = pf
trans-swapped* (swap one many) rest = swap one (trans-swapped* many rest)
```

```agda
sym-swapped :  ∀ {A : Set} {xs ys : List A}
               -> xs swapped-is ys
               -> ys swapped-is xs
sym-swapped here = here
sym-swapped (there pf) = there (sym-swapped pf)

sym-swapped* :  ∀ {A : Set} {xs ys : List A}
               -> xs swapped*-is ys
               -> ys swapped*-is xs
sym-swapped* refl = refl
sym-swapped* (swap one many) with sym-swapped* many
... | thing = trans-swapped* thing (swap (sym-swapped one) refl) 
```


### Standard-library permutations

The standard library defines permutations as follows:

    infix 3 _↭_

    data _↭_ : Rel (List A) a where
      refl  : ∀ {xs}        → xs ↭ xs
      prep  : ∀ {xs ys} x   → xs ↭ ys → x ∷ xs ↭ x ∷ ys
      swap  : ∀ {xs ys} x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
      trans : ∀ {xs ys zs}  → xs ↭ ys → ys ↭ zs → xs ↭ zs

This definition is very similar to the swapping definition,
except the reflexive transitive closure is expressed directly 
as axioms of the datatype.


## All formulations are equivalent

### Insertion growth implies zipper growth

The key idea is to implement `insert` using the zipper.

```agda
insert-in-zipper : ∀ {A : Set} {x : A} {xs ys ys' zs : List A}
          -> x ⊳ ys ≡ ys'
          -> Permutation-Zipper zs xs ys
          -> Permutation-Zipper (x ∷ zs) xs ys'
insert-in-zipper here perm = here perm
insert-in-zipper (there ins) perm with insert-in-zipper ins (there-right perm)
... | perm' = there-left perm'

insert-in-Zip⋈ : ∀ {A : Set} {x : A} {xs ys zs : List A}
              -> x ⊳ ys ≡ zs -> xs Zip⋈ ys -> x ∷ xs Zip⋈ zs
insert-in-Zip⋈ ins (permutation p) = permutation (insert-in-zipper ins p)

⋈→Zip⋈ : ∀ {A : Set} {xs ys : List A} -> xs ⋈ ys -> xs Zip⋈ ys
⋈→Zip⋈ [] = permutation []
⋈→Zip⋈ (insert ins xs⋈ys) = insert-in-Zip⋈ ins (⋈→Zip⋈ xs⋈ys)
```

### Zipper growth implies insertion growth

The main problem with the zipper is the redundancy in the representation:
the position of the write head doesn't affect the permutation that is represented.
The right-hand list is always `shunt ysₗ ysᵣ`, and insertion always takes place at `ysᵣ`.
The `shunt-⊳` lemma shows we can ignore `ysₗ` when inserting into `ysᵣ`.

```agda
shunt-⊳ : ∀ {A : Set} {x : A} {ys ysᵣ : List A} (ysₗ : List A)
        -> x ⊳ ys ≡ ysᵣ
        -> x ⊳ shunt ysₗ ys ≡ shunt ysₗ ysᵣ
shunt-⊳ [] pf = pf
shunt-⊳ (y ∷ ys) pf = shunt-⊳ ys (there pf)
```

Proof of implication just has insert each element where it goes,
following movement of the write head as needed.

```agda
zipper→⋈ : ∀ {A : Set} {ysₗ ys ysᵣ : List A}
              -> Permutation-Zipper ysᵣ ysₗ ys -> ysᵣ ⋈ shunt ysₗ ys
zipper→⋈ [] = []
zipper→⋈ {ysₗ = []} (here p) with zipper→⋈ p
... | p' = ⋈-∷ p'
zipper→⋈ {ysₗ = x ∷ xs} (here p) = insert (shunt-⊳ xs (there here)) (zipper→⋈ p)
zipper→⋈ (there-left p) = zipper→⋈ p
zipper→⋈ (there-right p) = zipper→⋈ p

Zip⋈→⋈ : ∀ {A : Set} {xs ys : List A} -> xs Zip⋈ ys -> xs ⋈ ys
Zip⋈→⋈ (permutation p) = zipper→⋈ p
```

### Swapping implies insertion growth

A single swap creates a permutation.

```agda
swapped→⋈ : ∀ {A : Set} {xs ys : List A} (pf : xs swapped-is ys) -> xs ⋈ ys
swapped→⋈ here = insert (there here) refl-⋈
swapped→⋈ (there pf) = ⋈-∷ (swapped→⋈ pf)
```

The reflexive, transitive closure relies on the `refl-⋈` and `trans-⋈` properties proved above.

```agda
swapped*→⋈ : ∀ {A : Set} {xs ys : List A} (pf : xs swapped*-is ys) -> xs ⋈ ys
swapped*→⋈ refl = refl-⋈
swapped*→⋈ (swap one many) = trans-⋈ (swapped→⋈ one) (swapped*→⋈ many)
```

### Insertion growth implies swapping

First,  we can grow a permutation expressed by swapping.

```agda
grow-swap* : ∀ {A : Set} {z : A} {xs ys : List A}
           -> xs swapped*-is ys -> z ∷ xs swapped*-is z ∷ ys
grow-swap* refl = refl
grow-swap* (swap pf* pf) = swap (there pf*) (grow-swap* pf)
```

Next, the insertion relation implies a (swapped) permutation.

```agda
⊳-swapped* : ∀ {A : Set} {x : A} {ys zs : List A} -> x ⊳ ys ≡ zs -> x ∷ ys swapped*-is zs
⊳-swapped* here = refl
⊳-swapped* (there pf) = swap here (grow-swap* (⊳-swapped* pf))
```

And finally, as with the zipper implication, we reproduce `insert` using the
swapped representation.

```agda
insert-swapped* : ∀ {A : Set} {x : A} {xs ys zs : List A}
                -> x ⊳ ys ≡ zs
                -> xs swapped*-is ys
                -> x ∷ xs swapped*-is zs
insert-swapped* here perm = grow-swap* perm
insert-swapped* {A} {x = x} {xs = as} {ys = b ∷ bs} {zs = c ∷ cs} 
           (there ins) many = trans-swapped*  (grow-swap* many)
                              (trans-swapped* (swap here (grow-swap* (⊳-swapped* ins)))
                                              refl)
    -- lemmas below might give some insert into the proof
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
```

### Swapping is equivalent to the standard library

The standard library lacks the "single swap" predicate,
but both predicates map nicely onto the standard library.
Each library constructor is used exactly once.

```agda
open import Data.List.Relation.Binary.Permutation.Propositional 
  using (_↭_; refl; prep; swap) renaming (trans to trans-↭)

swapped→↭ : ∀ {A : Set} {xs ys : List A} -> xs swapped-is ys -> xs ↭ ys
swapped*→↭ : ∀ {A : Set} {xs ys : List A} -> xs swapped*-is ys -> xs ↭ ys

swapped*→↭ refl = refl
swapped*→↭ (swap one many) = trans-↭ (swapped→↭ one) (swapped*→↭ many) 

swapped→↭ here = swap _ _ refl
swapped→↭ (there pf) = prep _ (swapped→↭ pf)
```

The opposite direction relies on my `grow-swap*` lemma,
which is of course exactly the `prep` axiom built into the standard library.

```agda
↭→swapped* : ∀ {A : Set} {xs ys : List A} -> xs ↭ ys -> xs swapped*-is ys
↭→swapped* refl = refl
↭→swapped* (prep x pf) = grow-swap* (↭→swapped* pf)
↭→swapped* (swap x y pf) = 
   trans-swapped* (grow-swap* (grow-swap* (↭→swapped* pf))) (swap here refl)
↭→swapped* (trans-↭ left right) = trans-swapped* (↭→swapped* left) (↭→swapped* right)

```



## Reasoning about insertion permutations

Permuted lists have the same elements.

```agda
⋈-∈ : ∀ {A : Set} {xs ys : List A}
    -> (xs ⋈ ys)
    -> (∀ {x : A} -> (x ∈ xs) ⇔ (x ∈ ys))
⋈-∈ {xs = xs} {ys = ys} xs⋈ys! {x} = record { to = to xs⋈ys! ; from = from xs⋈ys! }
  where to : ∀ {A : Set} {xs ys : List A} -> (xs ⋈ ys) -> ∀ {x : A} -> (x ∈ xs) -> (x ∈ ys)
        to (insert x⊳ys≡zs _) (here refl) = inserted-∈-result x⊳ys≡zs
        to (insert x⊳ys≡zs pf) (there x∈xs) = inserted-into-⊆-result x⊳ys≡zs (to pf x∈xs)

        from : ∀ {A : Set} {xs ys : List A} -> (xs ⋈ ys) -> ∀ {x : A} -> (x ∈ ys) -> (x ∈ xs)
        from (insert here pf) (here refl) = here refl
        from (insert (there x⊳ys≡zs) pf) (here refl) = there (from pf (here refl))
        from (insert x⊳bs≡y∷ys xs⋈bs) z∈ys with result-⊆-inserted-⊎-inserted-into x⊳bs≡y∷ys z∈ys
        ... | inj₁ x≡y = here x≡y
        ... | inj₂ x∈ys = there (from xs⋈bs x∈ys)
```

Equivalence preserves permutation.

```agda
cong-⋈ : ∀ {A : Set} {xs ys zs : List A}
        -> ys ≡ zs -> xs ⋈ ys -> xs ⋈ zs
cong-⋈ refl pf = pf
```

## Equational proofs about insertion permutations

This module apes the standard `≡-Reasoning` module.

```agda
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
```

## Permutations and append

When you have permutations, there are at least three ways to use `++` to make 
more permutations:

    xs ++ ys ⋈ ys ++ xs
    xs ⋈ ys -> zs ++ xs ⋈ zs ++ ys
    xs ⋈ ys -> xs ++ zs ⋈ ys ++ zs



```agda
find-insertion : ∀ {A : Set} (x : A) (xs ys : List A)
              -> x ⊳ (xs ++ ys) ≡ (xs ++ x ∷ ys)
find-insertion x [] ys = here
find-insertion x (x₁ ∷ xs) ys = there (find-insertion x xs ys)

swap-++ : ∀ {A : Set} (xs ys : List A)
        -> xs ++ ys ⋈ ys ++ xs
swap-++ [] ys rewrite ++-identityʳ ys = refl-⋈
swap-++ (x ∷ xs) ys = insert (find-insertion x ys xs) (swap-++ xs ys)
```

An element inserted between two lists can be pulled out.

```agda
open ⋈-Reasoning

⋈-head-swap : ∀ {A : Set} {x₁ x₂ : A} {xs ys : List A}
               -> xs ⋈ ys
               -> (x₁ ∷ x₂ ∷ xs) ⋈ (x₂ ∷ x₁ ∷ ys)
⋈-head-swap xs⋈ys = insert (there here) (⋈-∷ xs⋈ys)

swap-cons : ∀ {A : Set} (xs : List A) (x : A) (ys : List A)
          -> xs ++ x ∷ ys ⋈ x ∷ xs ++ ys
swap-cons [] x ys = refl-⋈
swap-cons (x₁ ∷ xs) x ys =
   begin⋈
     (x₁ ∷ xs) ++ x ∷ ys
   ⋈≡⟨ refl ⟩
     x₁ ∷ (xs ++ x ∷ ys)
   ⋈⟨ ⋈-∷ (swap-cons xs x ys) ⟩
     x₁ ∷ (x ∷ xs ++ ys)
   ⋈⟨ ⋈-head-swap refl-⋈ ⟩
     x ∷ (x₁ ∷ xs) ++ ys
   ∎⋈
```


We can add elements on the left or on the right.

```agda
++-⋈ˡ : ∀ {A : Set} {xs ys zs : List A}
      → xs ⋈ ys -> zs ++ xs ⋈ zs ++ ys
++-⋈ʳ : ∀ {A : Set} {xs ys zs : List A}
      → xs ⋈ ys -> xs ++ zs ⋈ ys ++ zs
++-⋈ˡ {zs = []} xs⋈ys = xs⋈ys
++-⋈ˡ {zs = x ∷ zs} xs⋈ys = ⋈-∷ (++-⋈ˡ xs⋈ys)
++-⋈ʳ {xs = xs} {ys = ys} {zs = []}
      xs⋈ys rewrite ++-identityʳ xs | ++-identityʳ ys = xs⋈ys
++-⋈ʳ {xs = xs} {ys = ys} {zs = z ∷ zs} xs⋈ys = 
  begin⋈
    xs ++ z ∷ zs
  ⋈⟨ swap-cons xs z zs ⟩
    z ∷ xs ++ zs
  ⋈⟨ ⋈-∷ (++-⋈ʳ xs⋈ys) ⟩
    z ∷ ys ++ zs
  ⋈⟨ sym-⋈ (swap-cons ys z zs) ⟩
    ys ++ z ∷ zs
  ∎⋈

```

## Sanity checks


```agda
Zip⋈-head-swap : ∀ {A : Set} {x₁ x₂ : A} {xs ys : List A}
               -> xs Zip⋈ ys
               -> (x₁ ∷ x₂ ∷ xs) Zip⋈ (x₂ ∷ x₁ ∷ ys)
Zip⋈-head-swap (permutation xs⋈ys) = permutation (there-left (here (there-right (here xs⋈ys))))
```


```agda
open ⋈-Reasoning

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

```

## Length properties

Confirming that permutations have equal lengths.

```agda
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
```

