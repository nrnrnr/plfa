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
open import Data.Nat.Properties using (≤-trans; ≤-refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Product using (Σ-syntax)
open import Function using (_∘_)
open import Level using (Level)
open import cs.plfa.part1.Isomorphism using (_≃_; _⇔_)
open import Data.Empty using (⊥; ⊥-elim)

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

## Sorting and ordering

Definition of a sorted list of natural numbers:

```agda
data Ascending : (List ℕ -> Set) where
  []  : Ascending []

  [x] : ∀ {n : ℕ}
                → Ascending [ n ]

  ascending-∷  : ∀ {n₁ n₂ : ℕ} {ns : List ℕ}
               → n₁ ≤ n₂
               → Ascending (n₂ ∷ ns) 
               -------------------------------
               → Ascending (n₁ ∷ n₂ ∷ ns)
```

A nonempty list is sorted if an only if its first element is 
the smallest and the tail is sorted.

```agda
Ascending-≤ : ∀ (n : ℕ) (ns : List ℕ)
            -> Ascending (n ∷ ns) ⇔ (Ascending ns × (∀ (y : ℕ) -> (y ∈ ns) -> n ≤ y))
Ascending-≤ n ns = record { to = to n ns ; from = from n ns }
  where to   : ∀ (n : ℕ) (ns : List ℕ)
             → Ascending (n ∷ ns)
             → (Ascending ns × (∀ (y : ℕ) → (y ∈ ns) → n ≤ y))
        from : ∀ (n : ℕ) (ns : List ℕ)
             → (Ascending ns × (∀ (y : ℕ) → (y ∈ ns) → n ≤ y))
             → Ascending (n ∷ ns)

        to n [] [x] = ⟨ [] , (λ y ()) ⟩
        to n (m ∷ ms) (ascending-∷ n≤m pf) with to m ms pf
        ... | ⟨ _ , m≤ms ⟩ = ⟨ pf , (λ y → λ{ (here refl) → n≤m
                                            ; (there x) → ≤-trans n≤m (m≤ms y x)}) ⟩
        from n [] ⟨ O-ns , n≤ns ⟩ = [x]
        from n (x ∷ xs) ⟨ ascending-x∷xs , n≤x∷xs ⟩ =
          ascending-∷ (n≤x∷xs x (here refl)) ascending-x∷xs
```

The tail of a sorted list is sorted.

```agda
ascending-tail : ∀ {x : ℕ} {xs : List ℕ} -> Ascending (x ∷ xs) -> Ascending xs
ascending-tail [x] = []
ascending-tail (ascending-∷ x [x]) = [x]
ascending-tail (ascending-∷ x (ascending-∷ x₁ pf)) = ascending-∷ x₁ pf
```


A sort function is given a list `ns` and computes a list `zs`
such that `zs` is `ns` sorted.

```agda
data _Sorted : List ℕ -> Set where
  sorted-as : ∀ {ns : List ℕ} -> ∀ (zs : List ℕ) -> Ascending zs -> zs ⋈ ns -> ns Sorted
```


## Exercise `Any-++-⇔` (finding elements in appended lists)

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

Of the two recursive calls to `merge-heaps`, only 
one will ever be used, but placing them in the `with` clause
somehow enables Agda's termination checker to figure out
that the calls are OK.
If the calls are split up, one under each outcome of `compare`,
the termination checker throws up its hands.
See <https://stackoverflow.com/questions/17910737/termination-check-on-list-merge>.

```agda
open import Data.Sum using (_⊎_; inj₁; inj₂)

open ⋈-Reasoning

merge-heaps : ∀ {ns ms : List ℕ} -> Heap ns -> Heap ms -> Heap (ns ++ ms)
merge-heaps [] [] = []
merge-heaps [] h@(root _ _ _ _ _) = h
merge-heaps {ns = ns} h@(root _ _ _ _ _) [] rewrite ++-identityʳ ns = h
merge-heaps {ns = ns} {ms = ms}
            h₁@(root {xs = xs₁} {ys = ys₁} {ns = ns₁} n₁ l₁ r₁ small₁ ns⋈n₁∷xs₁++ys₁)
            h₂@(root {xs = xs₂} {ys = ys₂} {ns = ns₂} n₂ l₂ r₂ small₂ ms⋈n₂∷xs₂++ys₂) 
  with compare n₁ n₂ | merge-heaps r₁ h₂ | merge-heaps h₁ r₂
... | less n₁≤n₂ | h | _ = root n₁ l₁ h lemma2 lemma1
        where lemma1 : ns ++ ms ⋈ n₁ ∷ xs₁ ++ ys₁ ++ ms
              lemma2 : ∀ {m : ℕ} → m ∈ ns ++ ms → n₁ ≤ m
              lemma1 = begin⋈
                         ns ++ ms
                       ⋈⟨ ++-⋈ʳ ns⋈n₁∷xs₁++ys₁ ⟩
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
                       ⋈⟨ ++-⋈ˡ ms⋈n₂∷xs₂++ys₂ ⟩
                         ns ++ n₂ ∷ xs₂ ++ ys₂
                       ⋈⟨ swap-cons ns n₂ (xs₂ ++ ys₂)  ⟩
                         n₂ ∷ ns ++ xs₂ ++ ys₂
                       ⋈⟨ ⋈-∷ (swap-++-++ ns xs₂ ys₂) ⟩
                         n₂ ∷ (ns ++ ys₂) ++ xs₂
                       ∎⋈
                  where swap-++-++ : ∀ {A : Set} (xs ys zs : List A)
                                  -> xs ++ ys ++ zs ⋈ (xs ++ zs) ++ ys
                        swap-++-++ [] ys zs = swap-++ ys zs
                        swap-++-++ (x ∷ xs) ys zs = ⋈-∷ (swap-++-++ xs ys zs)
              open _⇔_

              lemma2 {m} m∈list with to (Any-++-⇔ ns ms) m∈list
              ... | inj₁ m∈ms = ≤-trans n₂≤n₁ (small₁ m∈ms)
              ... | inj₂ m∈ns = small₂ m∈ns
```

To turn a heap into a sorted list, we have to know that the recursive call terminates.
That means that `delete-min` has to return a proof that the returned
heap is smaller than the argument heap.
The size of a heap is the length of its list of elements.
To make the structural recursion obvious, I define length as a relation.

```agda
data length_is_ {A : Set} : List A -> ℕ -> Set where
  [] : length [] is zero
  there : ∀ {a : A} {as : List A} {k : ℕ} -> length as is k -> length (a ∷ as) is (suc k)
```

Insertion grows a list by one, which I show in both directions.

```agda
insert-length : ∀ {A : Set} {x : A} {xs ys : List A} {k : ℕ}
              -> x ⊳ xs ≡ ys -> length xs is k -> length ys is (suc k)
insert-length here len = there len
insert-length (there ins) (there len) = there (insert-length ins len)

insert-length' : ∀ {A : Set} {x : A} {xs ys : List A} {k : ℕ}
              -> x ⊳ xs ≡ ys -> length ys is suc k -> length xs is k
insert-length' here (there len) = len
insert-length' (there ins) (there (there len)) = there (insert-length' ins (there len))
```

The length of `xs ++ ys` is the sum of the lengths.

```agda
length-++-is : ∀ {A : Set} {xs ys : List A} {k1 k2 : ℕ}
          -> length xs is k1
          -> length ys is k2
          -> length (xs ++ ys) is (k1 + k2)
length-++-is [] l2 = l2
length-++-is (there l1) l2 = there (length-++-is l1 l2)
```



And a list's tail is one shorter than the list.

```agda
length-pred :  ∀ {A : Set} {x : A} {xs : List A} {k : ℕ}
            -> length (x ∷ xs) is (suc k) -> length xs is k
length-pred (there pf) = pf
```

Permuting a list doesn't change its length.

```agda
length-perm : ∀ {A : Set} {xs ys : List A} {k : ℕ} -> length xs is k -> xs ⋈ ys -> length ys is k
length-perm [] [] = []
length-perm (there pf) (insert here perm) = there (length-perm pf perm)
length-perm (there (there as-l-k)) (insert (there a⊳ys≡zs) (insert x⊳xs≡ys perm))
   = there (insert-length a⊳ys≡zs (length-pred (insert-length x⊳xs≡ys (length-perm as-l-k perm))))
```

I'm not quite sure why I need this function, 
because a list should be manifestly equal to itself.
But extracting the elements is necessary for `delete-min`

```agda
heap-elements : ∀ {ns : List ℕ} -> Heap ns -> ∃[ ms ] ms ≡ ns
heap-elements [] = ⟨ [] , refl ⟩
heap-elements (root {ns = ns} n h h₁ x x₁) = ⟨ ns , refl ⟩
```

Given a heap `h` of type `Heap ns`, `delete-min` finds `m`, the smallest element of `ns`,
and `ms`, a list of all the remaining elements.
And it produces a new heap containing `ms`, plus proofs of my claims about `m` and `ms`,
plus a proof that the heap has shrunk.

```agda
delete-min : ∀ {ns : List ℕ} {k : ℕ}
           -> length ns is suc k
           -> (h : Heap ns)
           -> ∃[ m ] ∃[ ms ] Heap ms
                           × length ms is k
                           × (ns ⋈ m ∷ ms)
                           × (∀ {z : ℕ} -> (z ∈ ns) -> m ≤ z)

delete-min |ns|≡suc-k (root m left right n≤xs++ys ns⋈n∷xs++ys)
  with heap-elements (merge-heaps left right)
... | ⟨ ms , refl ⟩ =
        ⟨ m , ⟨ ms , ⟨ newheap , ⟨ good-length , ⟨ ns⋈n∷xs++ys , n≤xs++ys ⟩ ⟩ ⟩ ⟩ ⟩
  where newheap = merge-heaps left right
        good-length = length-pred (length-perm |ns|≡suc-k ns⋈n∷xs++ys)
```

To sort a list, first build a heap containing the elements of the list.

```agda
singleton-heap : ∀ (n : ℕ) -> Heap [ n ]
singleton-heap n = root n [] [] (λ { (here refl) → ≤-refl}) refl-⋈

insert-in-heap : ∀ {ns : List ℕ} -> (n : ℕ) -> Heap ns -> Heap (n ∷ ns)
insert-in-heap n h = merge-heaps (singleton-heap n) h

build-heap : (ns : List ℕ) -> Heap ns
build-heap [] = []
build-heap (n ∷ ns) = insert-in-heap n (build-heap ns)
```


Draining a heap produces a sorted permutation of the heap's elements.

```agda
open _⇔_

drain-heap : ∀ {ns : List ℕ} {n : ℕ} -> (length ns is n) -> Heap ns -> ∃[ ms ] ns ⋈ ms × Ascending ms
drain-heap {[]} {zero} pf [] = ⟨ [] , ⟨ [] , [] ⟩ ⟩
drain-heap {z ∷ zs} {suc k} length h@(root n _ _ orig-order perm)
  with delete-min length h
... | ⟨ min , ⟨ ms , ⟨ newheap , ⟨ shorter , ⟨ z∷zs⋈min∷ms , small ⟩ ⟩ ⟩ ⟩ ⟩
         with drain-heap shorter newheap
...         | ⟨ rest , ⟨ ms⋈rest , ordered ⟩ ⟩ = ⟨ min ∷ rest , ⟨ fullperm , fullorder ⟩ ⟩
  where smallest = λ y y∈rest → small (from (⋈-∈ z∷zs⋈min∷ms) (there (from (⋈-∈ ms⋈rest) y∈rest)))
        fullorder = from (Ascending-≤ min rest) ⟨ ordered , smallest ⟩
        fullperm : z ∷ zs ⋈ min ∷ rest
        fullperm = 
           begin⋈
             z ∷ zs
           ⋈⟨ z∷zs⋈min∷ms ⟩ 
             min ∷ ms
           ⋈⟨ ⋈-∷ ms⋈rest ⟩ 
             min ∷ rest
           ∎⋈
```

To implement heapsort, I have to compute the size of a heap.
             
```agda
heap-size : ∀ {ns : List ℕ} -> Heap ns -> ∃[ k ] length ns is k
heap-size [] = ⟨ zero , [] ⟩
heap-size (root _ left right _ perm) with heap-size left | heap-size right 
... | ⟨ kₗ , lenₗ ⟩ | ⟨ kᵣ , lenᵣ ⟩ =
   ⟨ 1 + kₗ + kᵣ , length-perm (there (length-++-is lenₗ lenᵣ)) (sym-⋈ perm) ⟩

           -- 
heapsort : (ns : List ℕ) -> ∃[ ms ] ns ⋈ ms × Ascending ms
heapsort ns with heap-size (build-heap ns)
... | ⟨ _ , len ⟩ = drain-heap len (build-heap ns)
```

## Mergesort

Mergesort leaves bread crumbs showing that
the merge always takes the smaller element.

```agda
data merged (A : Set) (_le_ : A -> A -> Set) : (xs ys zs : List A) → Set where
  -- the merge of xs and ys is zs

  [] :
      --------------
      merged A _le_ [] [] []

  left-∷-[] : ∀ {x xs zs}
    → merged A _le_ xs [] zs
      --------------------------
    → merged A _le_ (x ∷ xs) [] (x ∷ zs)

  left-∷-∷ : ∀ {x y xs ys zs}
    → x le y
    → merged A _le_ xs (y ∷ ys) zs
      --------------------------
    → merged A _le_ (x ∷ xs) (y ∷ ys) (x ∷ zs)

  right-[]-∷ : ∀ {y ys zs}
    → merged A _le_ [] ys zs
      --------------------------
    → merged A _le_ [] (y ∷ ys) (y ∷ zs)

  right-∷-∷ : ∀ {x y xs ys zs}
    → y le x
    → merged A _le_ (x ∷ xs) ys zs
      --------------------------
    → merged A _le_ (x ∷ xs) (y ∷ ys) (y ∷ zs)

merged≤ : ∀ (xs ys zs : List ℕ) -> Set
merged≤ = merged (ℕ) (_≤_)

```

The merge itself is straightforward.

```agda
merge≤ : ∀ (xs ys : List ℕ) -> ∃[ zs ] (merged≤ xs ys zs)
merge≤ [] [] = ⟨ [] , [] ⟩
merge≤ (x ∷ xs) [] with merge≤ xs [] 
... | ⟨ zs , merge ⟩ = ⟨ (x ∷ zs) , (left-∷-[] merge) ⟩
merge≤ [] (y ∷ ys) with merge≤ [] ys
... | ⟨ zs , merge ⟩ = ⟨ (y ∷ zs) , (right-[]-∷ merge) ⟩
merge≤ (x ∷ xs) (y ∷ ys) with compare x y | merge≤ xs (y ∷ ys) | merge≤ (x ∷ xs) ys
... | less x≤y | ⟨ zs , m ⟩ | _ = ⟨ x ∷ zs , left-∷-∷ x≤y m ⟩
... | greater y≤x | _ | ⟨ zs , m ⟩ = ⟨ (y ∷ zs) , right-∷-∷ y≤x m ⟩
```

And merging creates a permutation.
```agda
merge-permutes : ∀ {A : Set} {le : A -> A -> Set} {xs ys zs : List A}
               -> merged A le xs ys zs
               -> xs ++ ys ⋈ zs
merge-permutes [] = []
merge-permutes (left-∷-[] pf)   = ⋈-∷ (merge-permutes pf)
merge-permutes (left-∷-∷ x pf)  = ⋈-∷ (merge-permutes pf)
merge-permutes (right-[]-∷ pf)  = ⋈-∷ (merge-permutes pf)
merge-permutes {xs = xs} {ys = y ∷ ys} (right-∷-∷ _ pf)
   = trans-⋈ (swap-cons xs y ys) (⋈-∷ (merge-permutes pf))

cong-Ascending : ∀ {xs ys : List ℕ} -> (xs ≡ ys) -> (Ascending xs) -> Ascending ys
cong-Ascending refl pf = pf

cong-∈ : ∀ {A : Set} {xs ys : List A} {z : A} -> xs ≡ ys -> z ∈ xs -> z ∈ ys
cong-∈ refl pf = pf

merged≤-left-≡ : {xs zs : List ℕ} -> merged≤ xs [] zs -> xs ≡ zs
merged≤-left-≡ [] = refl
merged≤-left-≡ (left-∷-[] pf) rewrite (merged≤-left-≡ pf) = refl

merged-only-xs-ys : ∀ {xs ys zs : List ℕ} -> merged≤ xs ys zs ->
                    ∀ (z : ℕ) -> z ∈ zs -> z ∈ xs ⊎ z ∈ ys
merged-only-xs-ys [] z = λ ()
merged-only-xs-ys (left-∷-[] pf) z (here x) = inj₁ (here x)
merged-only-xs-ys (left-∷-[] pf) z (there z∈zs) with merged-only-xs-ys pf z z∈zs 
... | inj₁ z∈xs = inj₁ (there z∈xs)
merged-only-xs-ys (right-[]-∷ pf) z (here x) = inj₂ (here x)
merged-only-xs-ys (right-[]-∷ pf) z (there z∈zs) with merged-only-xs-ys pf z z∈zs 
... | inj₂ z∈xs = inj₂ (there z∈xs)

merged-only-xs-ys (left-∷-∷ _ pf) z (here h) = inj₁ (here h)
merged-only-xs-ys (left-∷-∷ _ pf) z (there z∈zs) with merged-only-xs-ys pf z z∈zs 
... | inj₁ z∈xs = inj₁ (there z∈xs)
... | inj₂ z∈ys = inj₂ z∈ys

merged-only-xs-ys (right-∷-∷ _ pf) z (here h) = inj₂ (here h)
merged-only-xs-ys (right-∷-∷ _ pf) z (there z∈zs) with merged-only-xs-ys pf z z∈zs 
... | inj₁ z∈xs = inj₁ z∈xs
... | inj₂ z∈ys = inj₂ (there z∈ys)



lemma9 : ∀ {ys zs : List ℕ}
       -> merged≤ [] ys zs
       -> ys ≡ zs
lemma9 [] = refl
lemma9 (right-[]-∷ pf) = cong (_∷_ _) (lemma9 pf)

lemma8 : ∀ {xs zs : List ℕ}
       -> merged≤ xs [] zs
       -> xs ≡ zs
lemma8 [] = refl
lemma8 (left-∷-[] pf) = cong (_∷_ _) (lemma8 pf)


merge-ordered : ∀ {xs ys zs : List ℕ} -> Ascending xs -> Ascending ys -> merged≤ xs ys zs
              -> Ascending zs
merge-ordered [] [] [] = []
merge-ordered xs≤ [] pf with lemma8 pf
... | refl = xs≤
merge-ordered [] ys≤ pf with lemma9 pf
... | refl = ys≤

merge-ordered oxs oys (left-∷-∷ {x} {y} {xs} {ys} {zs} x≤y m) = 
                                        from (Ascending-≤ x zs) ⟨ ozs , x≤zs ⟩
  where ozs : Ascending zs
        x≤zs : ∀ (y : ℕ) -> y ∈ zs -> x ≤ y
        x≤xs : ∀ (y : ℕ) -> y ∈ xs -> x ≤ y
        ozs = merge-ordered (ascending-tail oxs) oys m
        x≤xs = Data.Product.Σ.proj₂ (_⇔_.to (Ascending-≤ x xs) oxs)
        y≤ys = Data.Product.Σ.proj₂ (_⇔_.to (Ascending-≤ y ys) oys)
        x≤zs v v∈zs with merged-only-xs-ys m v v∈zs 
        ... | inj₁ v∈xs = x≤xs v v∈xs
        ... | inj₂ (here refl) = x≤y
        ... | inj₂ (there v∈ys) = ≤-trans x≤y (y≤ys v v∈ys)

merge-ordered xs≤ ys≤ (right-∷-∷ {y = y} {zs = zs} y≤x m) 
  with to (Ascending-≤ _ _) xs≤ | to (Ascending-≤ _ _) ys≤
... | ⟨ _ , big-xs ⟩ | ⟨ _ , big-ys ⟩ = 
         from (Ascending-≤ y zs) ⟨ merge-ordered xs≤ (ascending-tail ys≤) m , big-zs ⟩
      where big-zs : ∀ (z : ℕ) → z ∈ zs → y ≤ z
            big-zs z z∈zs with merged-only-xs-ys m z z∈zs
            ... | inj₁ (here refl) = y≤x
            ... | inj₁ (there z∈xs) = ≤-trans y≤x (big-xs _ z∈xs)
            ... | inj₂ z∈ys = big-ys _ z∈ys
```

Splitting a list

The recursion in merge sort is subtle, and it is easy to get wrong when coding.
Merge sort splits a list into two smaller lists, and if the code
is botched, the lists might *not* be smaller, in which case the recursion goes
on forever.
I address this problem with a new proposition `Split zs`, which
is satisfied either if `zs` is split into two smaller pieces
or if it is too short to need splitting (and therefore already 
totally ordered).

```agda
data Split {A : Set} : (zs : List A) -> Set where
  [] : Split []
  [x] : ∀ (x : A) -> Split ([ x ])
  fork : ∀ {xs ys zs : List A} -> Split xs -> Split ys -> xs ++ ys ⋈ zs -> Split zs
```

Once the splitting process is known terminate, merge sort is
relatively straightforward.

```agda
sort-tree : ∀ {ns : List ℕ} -> Split ns -> ns Sorted
sort-tree [] = sorted-as [] [] []
sort-tree ([x] x) = sorted-as [ x ] [x] (⋈-∷ [])
sort-tree {ns} (fork {xs = vs} {ys = ws} left right vs++ws⋈ns)
  with sort-tree left | sort-tree right
...  | sorted-as xs xs≤ xs⋈vs | sorted-as ys ys≤ ys⋈ws with merge≤ xs ys
...       | ⟨ zs , merged ⟩ with merge-permutes merged 
...            | xs++ys⋈zs = 
     sorted-as zs (merge-ordered xs≤ ys≤ merged) zs⋈ns
   where zs⋈ns : zs ⋈ ns
         zs⋈ns =
           begin⋈
             zs
           ⋈⟨ sym-⋈ xs++ys⋈zs ⟩
             xs ++ ys
           ⋈⟨ ++-⋈ʳ xs⋈vs ⟩
             vs ++ ys
           ⋈⟨ ++-⋈ˡ ys⋈ws ⟩
             vs ++ ws
           ⋈⟨ vs++ws⋈ns ⟩
             ns
           ∎⋈

```

And the final mergesort just builds the tree and sorts it.

```agda
tree-∷ : ∀ {A : Set} -> (x : A) -> {ns : List A} -> Split ns -> Split (x ∷ ns)
tree-∷ x [] = [x] x
tree-∷ x ([x] y) = fork ([x] x) ([x] y) refl-⋈
tree-∷ x (fork {xs = xs} {ys = ys} xtree ytree xs++ys⋈ns) =
  fork (tree-∷ x ytree) xtree (⋈-∷ (trans-⋈ (swap-++ ys xs) xs++ys⋈ns))

tree-of-list : ∀ {A : Set} -> (xs : List A) -> Split xs
tree-of-list [] = []
tree-of-list (x ∷ xs) = tree-∷ x (tree-of-list xs)

mergesort : ∀ (ns : List ℕ) -> ns Sorted
mergesort ns = sort-tree (tree-of-list ns)
```


## Insertion sort

```
insert≤ : ∀ (n : ℕ) (ns : List ℕ)
       -> Ascending ns
       -> (n ∷ ns) Sorted
insert≤ n [] pf = sorted-as [ n ] [x] refl-⋈
insert≤ n (m ∷ ms) m∷ms≤ with compare n m
... | less n≤m = sorted-as (n ∷ m ∷ ms) (ascending-∷ n≤m m∷ms≤) refl-⋈
... | greater m≤n with insert≤ n ms (ascending-tail m∷ms≤)
...       | sorted-as zs zs≤ zs⋈n∷ms = sorted-as (m ∷ zs) all≤ (insert (there here) zs⋈n∷ms)
  where big-n∷ms : ∀ (y : ℕ) -> y ∈ n ∷ ms -> m ≤ y
        big-n∷ms y (here refl) = m≤n -- y ≡ n
        big-n∷ms y (there y∈ms) with to (Ascending-≤ m ms) m∷ms≤
        ... | ⟨ _ , big-ms ⟩ = big-ms y y∈ms

        big-zs : ∀ (y : ℕ) -> y ∈ zs -> m ≤ y
        big-zs y y∈zs = big-n∷ms y (to (⋈-∈ zs⋈n∷ms) y∈zs)

        all≤ : Ascending (m ∷ zs)
        all≤ = from (Ascending-≤ m zs) ⟨ zs≤ , big-zs ⟩
```
