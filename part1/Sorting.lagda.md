---
title     : "Sorting: correctness of heapsort and merge sort"
permalink : /Sorting/
---

```agda
module cs.plfa.part1.Sorting where
```

This chapter discusses the list data type.  It gives further examples
of many of the techniques we have developed so far, and provides
examples of polymorphic types and higher-order functions.

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
open import Algebra.Structures using (IsMonoid)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (Decidable)

open import Data.List.Properties
  using (++-assoc; ++-identityˡ; ++-identityʳ; length-++)

open import cs.plfa.part1.Permutations

```

## Comparison

I could import `_≤?_` from the standard library, but
I don't want to get into the details of `Total`, which I haven't actually studied.
Instead, `compare` gives me `≤` one way or another.

```agda
data Order (m n : ℕ) : Set where
  less : m ≤ n -> Order  m n
  greater : n ≤ m -> Order  m n

compare : (m n : ℕ) -> Order m n
compare zero n = less z≤n
compare (suc m) zero = greater z≤n
compare (suc m) (suc n) with compare m n
... | less x = less (s≤s x)
... | greater x = greater (s≤s x)
```

## Heaps

The parameter to a heap lists the elements it contains.


```agda
data Heap : List ℕ -> Set where
  [] : Heap []
  root : ∀ {xs ys ns : List ℕ} 
       -> (n : ℕ)
       -> Heap xs
       -> Heap ys
       -> (∀ {m : ℕ} -> (m ∈ ns) -> n ≤ m)
       -> ns ⋈ n ∷ (xs ++ ys)
       -> Heap ns
```

Heap merge is the best.

```agda
open import Data.Nat.Properties using (≤-trans; ≤-refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open ⋈-Reasoning

cong-⋈-++ʳ : ∀ {A : Set} {xs ys zs : List A}
           -> xs ⋈ ys
           -> zs ++ xs ⋈ zs ++ ys
cong-⋈-++ʳ {zs = []} pf = pf
cong-⋈-++ʳ {zs = z ∷ zs} pf = insert here (cong-⋈-++ʳ pf)

merge-heaps : ∀ {ns ms : List ℕ} -> Heap ns -> Heap ms -> Heap (ns ++ ms)
merge-heaps [] [] = []
merge-heaps [] h@(root _ _ _ _ _) = h
merge-heaps {ns = ns} h@(root _ _ _ _ _) [] rewrite ++-identityʳ ns = h
merge-heaps {ns = ns} {ms = ms}
            h₁@(root {xs = xs₁} {ys = ys₁} {ns = ns₁} n₁ l₁ r₁ small₁ perm1)
            h₂@(root {xs = xs₂} {ys = ys₂} {ns = ns₂} n₂ l₂ r₂ small₂ perm2) 
  with compare n₁ n₂ | merge-heaps r₁ h₂ | merge-heaps h₁ r₂
... | less n₁≤n₂ | h | _ = root n₁ l₁ h lemma2 lemma1
        where lemma1 : ns ++ ms ⋈ n₁ ∷ xs₁ ++ ys₁ ++ ms
              lemma2 : ∀ {m : ℕ} → m ∈ ns ++ ms → n₁ ≤ m
              lemma1 = begin⋈
                         ns ++ ms
                       ⋈⟨ cong-⋈-++ˡ perm1 ⟩
                         (n₁ ∷ xs₁ ++ ys₁) ++ ms
                       ⋈≡⟨ refl ⟩
                         n₁ ∷ (xs₁ ++ ys₁) ++ ms
                       ⋈≡⟨ cong (_∷_ n₁) (++-assoc xs₁ ys₁ ms) ⟩
                         n₁ ∷ xs₁ ++ ys₁ ++ ms
                       ∎⋈

              open _⇔_

              lemma2 {m} m∈list with to (Any-++-⇔ ns ms) m∈list
              ... | inj₁ m∈ns = small₁ m∈ns
              ... | inj₂ m∈ms = ≤-trans n₁≤n₂ (small₂ m∈ms)
... | greater n₂≤n₁ | _ | h = root n₂ h l₂ lemma2 lemma1
        where lemma1 : ns ++ ms ⋈ n₂ ∷ (ns ++ ys₂) ++ xs₂
              lemma2 : ∀ {m : ℕ} → m ∈ ns ++ ms → n₂ ≤ m
              lemma1 = begin⋈
                         ns ++ ms
                       ⋈⟨ cong-⋈-++ʳ perm2 ⟩
                         ns ++ n₂ ∷ xs₂ ++ ys₂
                       ⋈⟨ swap-cons ns n₂ (xs₂ ++ ys₂)  ⟩
                         n₂ ∷ ns ++ xs₂ ++ ys₂
                       ⋈⟨ insert here (swap-++-++ ns xs₂ ys₂) ⟩
                         n₂ ∷ (ns ++ ys₂) ++ xs₂
                       ∎⋈
                  where swap-++-++ : ∀ {A : Set} (xs ys zs : List A)
                                  -> xs ++ ys ++ zs ⋈ (xs ++ zs) ++ ys
                        swap-++-++ [] ys zs = swap-++ ys zs
                        swap-++-++ (x ∷ xs) ys zs = insert here (swap-++-++ xs ys zs)
              open _⇔_

              lemma2 {m} m∈list with to (Any-++-⇔ ns ms) m∈list
              ... | inj₁ m∈ms = ≤-trans n₂≤n₁ (small₁ m∈ms)
              ... | inj₂ m∈ns = small₂ m∈ns

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

data Ascending : (List ℕ -> Set) where

  ascending-[]  : Ascending []

  ascending-[x] : ∀ {n : ℕ}
                → Ascending [ n ]

  ascending-∷  : ∀ {n₁ n₂ : ℕ} {ns : List ℕ}
               → n₁ ≤ n₂
               → Ascending (n₂ ∷ ns) 
               -------------------------------
               → Ascending (n₁ ∷ n₂ ∷ ns)


≤-congruence : ∀ {x y z : ℕ} -> (x ≤ y) -> (y ≡ z) -> (x ≤ z)
≤-congruence pf refl = pf

Ascending-≤ : ∀ (n : ℕ) (ns : List ℕ)
            -> Ascending (n ∷ ns) ⇔ (Ascending ns × (∀ (y : ℕ) -> (y ∈ ns) -> n ≤ y))
Ascending-≤ n ns = record { to = to n ns ; from = from n ns }
  where to : ∀ (n : ℕ) (ns : List ℕ) -> Ascending (n ∷ ns) -> (Ascending ns × (∀ (y : ℕ) ->  (y ∈ ns) -> n ≤ y))
        from : ∀ (n : ℕ) (ns : List ℕ) -> (Ascending ns × (∀ (y : ℕ) -> (y ∈ ns) -> n ≤ y)) -> Ascending (n ∷ ns)

        to n [] ascending-[x] = ⟨ ascending-[] , (λ y ()) ⟩
        to n (m ∷ ms) (ascending-∷ n≤m pf) with to m ms pf
        ... | ⟨ _ , m≤ms ⟩ = ⟨ pf , (λ y → λ{ (here x) → ≤-congruence n≤m (sym x)
                                            ; (there x) → ≤-trans n≤m (m≤ms y x)}) ⟩
        from n [] ⟨ O-ns , n≤ns ⟩ = ascending-[x]
        from n (x ∷ xs) ⟨ ascending-x∷xs , n≤x∷xs ⟩ =
          ascending-∷ (n≤x∷xs x (here refl)) ascending-x∷xs

open _⇔_



drain-heap : ∀ {ns : List ℕ} {n : ℕ} -> (length ns is n) -> Heap ns -> ∃[ ms ] ns ⋈ ms × Ascending ms
drain-heap {[]} {zero} pf [] = ⟨ [] , ⟨ [] , ascending-[] ⟩ ⟩
drain-heap {z ∷ zs} {suc k} (length) h@(root n _ _ orig-order perm)
  with delete-min length h -- ⟨ n , from (⋈-∈ perm) (here refl) ⟩
... | ⟨ min , ⟨ ms , ⟨ newheap , ⟨ len , ⟨ perm1 , small ⟩ ⟩ ⟩ ⟩ ⟩ with drain-heap len newheap
... | ⟨ rest , ⟨ ms⋈rest , ordered ⟩ ⟩ = ⟨ min ∷ rest , ⟨ fullperm , fullorder ⟩ ⟩
  where smallest = λ y y∈rest → small (from (⋈-∈ perm1) (there (from (⋈-∈ ms⋈rest) y∈rest)))
        fullorder = from (Ascending-≤ min rest) ⟨ ordered , smallest ⟩
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
heapsort : (ns : List ℕ) -> ∃[ ms ] (ns ⋈ ms) × (Ascending ms)
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

## Standard Library

Definitions similar to those in this chapter can be found in the standard library:
```agda
import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional using (_∈_)
import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
  renaming (mapIsFold to map-is-foldr)
import Algebra.Structures using (IsMonoid)
import Relation.Unary using (Decidable)
import Relation.Binary using (Decidable)
```
The standard library version of `IsMonoid` differs from the
one given here, in that it is also parameterised on an equivalence relation.

Both `Relation.Unary` and `Relation.Binary` define a version of `Decidable`,
one for unary relations (as used in this chapter where `P` ranges over
unary predicates) and one for binary relations (as used earlier, where `_≤_`
ranges over a binary relation).

## Unicode

This chapter uses the following unicode:

    ∷  U+2237  PROPORTION  (\::)
    ⊗  U+2297  CIRCLED TIMES  (\otimes, \ox)
    ∈  U+2208  ELEMENT OF  (\in)
    ∉  U+2209  NOT AN ELEMENT OF  (\inn, \notin)
