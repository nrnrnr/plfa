---
title     : "More: Additional constructs of simply-typed lambda calculus"
permalink : /More/
---

```agda
module cs.plfa.part2.More where
```

So far, we have focussed on a relatively minimal language, based on
Plotkin's PCF, which supports functions, naturals, and fixpoints.  In
this chapter we extend our calculus to support the following:

  * primitive numbers
  * _let_ bindings
  * products
  * an alternative formulation of products
  * sums
  * unit type
  * an alternative formulation of unit type
  * empty type
  * lists

All of the data types should be familiar from Part I of this textbook.
For _let_ and the alternative formulations we show how they translate
to other constructs in the calculus.  Most of the description will be
informal. We show how to formalise the first four constructs and leave
the rest as an exercise for the reader.

Our informal descriptions will be in the style of
Chapter [Lambda](/Lambda/),
using extrinsically-typed terms,
while our formalisation will be in the style of
Chapter [DeBruijn](/DeBruijn/),
using intrinsically-typed terms.

By now, explaining with symbols should be more concise, more precise,
and easier to follow than explaining in prose.
For each construct, we give syntax, typing, reductions, and an example.
We also give translations where relevant; formally establishing the
correctness of translations will be the subject of the next chapter.

## Primitive numbers

We define a `Nat` type equivalent to the built-in natural number type
with multiplication as a primitive operation on numbers:

### Syntax

    A, B, C ::= ...                     Types
      Nat                                 primitive natural numbers

    L, M, N ::= ...                     Terms
      con c                               constant
      L `* M                              multiplication

    V, W ::= ...                        Values
      con c                               constant

### Typing

The hypothesis of the `con` rule is unusual, in that
it refers to a typing judgment of Agda rather than a
typing judgment of the defined calculus:

    c : ℕ
    --------------- con
    Γ ⊢ con c : Nat

    Γ ⊢ L : Nat
    Γ ⊢ M : Nat
    ---------------- _`*_
    Γ ⊢ L `* M : Nat

### Reduction

A rule that defines a primitive directly, such as the last rule below,
is called a δ rule.  Here the δ rule defines multiplication of
primitive numbers in terms of multiplication of naturals as given
by the Agda standard prelude:

    L —→ L′
    ----------------- ξ-*₁
    L `* M —→ L′ `* M

    M —→ M′
    ----------------- ξ-*₂
    V `* M —→ V `* M′

    ----------------------------- δ-*
    con c `* con d —→ con (c * d)

### Example

Here is a function to cube a primitive number:

    cube : ∅ ⊢ Nat ⇒ Nat
    cube = ƛ x ⇒ x `* x `* x


## Let bindings

Let bindings affect only the syntax of terms; they introduce no new
types or values:

### Syntax

    L, M, N ::= ...                     Terms
      `let x `= M `in N                   let

### Typing

    Γ ⊢ M ⦂ A
    Γ , x ⦂ A ⊢ N ⦂ B
    ------------------------- `let
    Γ ⊢ `let x `= M `in N ⦂ B

### Reduction

    M —→ M′
    --------------------------------------- ξ-let
    `let x `= M `in N —→ `let x `= M′ `in N

    --------------------------------- β-let
    `let x `= V `in N —→ N [ x := V ]

### Example

Here is a function to raise a primitive number to the tenth power:

    exp10 : ∅ ⊢ Nat ⇒ Nat
    exp10 = ƛ x ⇒ `let x2  `= x  `* x  `in
                  `let x4  `= x2 `* x2 `in
                  `let x5  `= x4 `* x  `in
                  x5 `* x5

### Translation

We can translate each _let_ term into an application of an abstraction:

    (`let x `= M `in N) †  =  (ƛ x ⇒ (N †)) · (M †)

Here `M †` is the translation of term `M` from a calculus with the
construct to a calculus without the construct.


## Products {#products}

### Syntax

    A, B, C ::= ...                     Types
      A `× B                              product type

    L, M, N ::= ...                     Terms
      `⟨ M , N ⟩                          pair
      `proj₁ L                            project first component
      `proj₂ L                            project second component

    V, W ::= ...                        Values
      `⟨ V , W ⟩                          pair

### Typing

    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ B
    ----------------------- `⟨_,_⟩ or `×-I
    Γ ⊢ `⟨ M , N ⟩ ⦂ A `× B

    Γ ⊢ L ⦂ A `× B
    ---------------- `proj₁ or `×-E₁
    Γ ⊢ `proj₁ L ⦂ A

    Γ ⊢ L ⦂ A `× B
    ---------------- `proj₂ or `×-E₂
    Γ ⊢ `proj₂ L ⦂ B

### Reduction

    M —→ M′
    ------------------------- ξ-⟨,⟩₁
    `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

    N —→ N′
    ------------------------- ξ-⟨,⟩₂
    `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

    L —→ L′
    --------------------- ξ-proj₁
    `proj₁ L —→ `proj₁ L′

    L —→ L′
    --------------------- ξ-proj₂
    `proj₂ L —→ `proj₂ L′

    ---------------------- β-proj₁
    `proj₁ `⟨ V , W ⟩ —→ V

    ---------------------- β-proj₂
    `proj₂ `⟨ V , W ⟩ —→ W

### Example

Here is a function to swap the components of a pair:

    swap× : ∅ ⊢ A `× B ⇒ B `× A
    swap× = ƛ z ⇒ `⟨ `proj₂ z , `proj₁ z ⟩


## Alternative formulation of products

There is an alternative formulation of products, where in place of two
ways to eliminate the type we have a case term that binds two
variables.  We repeat the syntax in full, but only give the new type
and reduction rules:

### Syntax

    A, B, C ::= ...                     Types
      A `× B                              product type

    L, M, N ::= ...                     Terms
      `⟨ M , N ⟩                          pair
      case× L [⟨ x , y ⟩⇒ M ]             case

    V, W ::=                            Values
      `⟨ V , W ⟩                          pair

### Typing

    Γ ⊢ L ⦂ A `× B
    Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C
    ------------------------------- case× or ×-E
    Γ ⊢ case× L [⟨ x , y ⟩⇒ N ] ⦂ C

### Reduction

    L —→ L′
    --------------------------------------------------- ξ-case×
    case× L [⟨ x , y ⟩⇒ N ] —→ case× L′ [⟨ x , y ⟩⇒ N ]

    --------------------------------------------------------- β-case×
    case× `⟨ V , W ⟩ [⟨ x , y ⟩⇒ N ] —→ N [ x := V ][ y := W ]

### Example

Here is a function to swap the components of a pair rewritten in the new notation:

    swap×-case : ∅ ⊢ A `× B ⇒ B `× A
    swap×-case = ƛ z ⇒ case× z
                         [⟨ x , y ⟩⇒ `⟨ y , x ⟩ ]

### Translation

We can translate the alternative formulation into the one with projections:

      (case× L [⟨ x , y ⟩⇒ N ]) †
    =
      `let z `= (L †) `in
      `let x `= `proj₁ z `in
      `let y `= `proj₂ z `in
      (N †)

Here `z` is a variable that does not appear free in `N`.  We refer
to such a variable as _fresh_.

One might think that we could instead use a more compact translation:

    -- WRONG
      (case× L [⟨ x , y ⟩⇒ N ]) †
    =
      (N †) [ x := `proj₁ (L †) ] [ y := `proj₂ (L †) ]

But this behaves differently.  The first term always reduces `L`
before `N`, and it computes `` `proj₁ `` and `` `proj₂ `` exactly once.  The
second term does not reduce `L` to a value before reducing `N`, and
depending on how many times and where `x` and `y` appear in `N`, it
may reduce `L` many times or not at all, and it may compute `` `proj₁ ``
and `` `proj₂ `` many times or not at all.

We can also translate back the other way:

    (`proj₁ L) ‡  =  case× (L ‡) [⟨ x , y ⟩⇒ x ]
    (`proj₂ L) ‡  =  case× (L ‡) [⟨ x , y ⟩⇒ y ]

## Sums {#sums}

### Syntax

    A, B, C ::= ...                     Types
      A `⊎ B                              sum type

    L, M, N ::= ...                     Terms
      `inj₁ M                             inject first component
      `inj₂ N                             inject second component
      case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ]    case

    V, W ::= ...                        Values
      `inj₁ V                             inject first component
      `inj₂ W                             inject second component

### Typing

    Γ ⊢ M ⦂ A
    -------------------- `inj₁ or ⊎-I₁
    Γ ⊢ `inj₁ M ⦂ A `⊎ B

    Γ ⊢ N ⦂ B
    -------------------- `inj₂ or ⊎-I₂
    Γ ⊢ `inj₂ N ⦂ A `⊎ B

    Γ ⊢ L ⦂ A `⊎ B
    Γ , x ⦂ A ⊢ M ⦂ C
    Γ , y ⦂ B ⊢ N ⦂ C
    ----------------------------------------- case⊎ or ⊎-E
    Γ ⊢ case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] ⦂ C

### Reduction

    M —→ M′
    ------------------- ξ-inj₁
    `inj₁ M —→ `inj₁ M′

    N —→ N′
    ------------------- ξ-inj₂
    `inj₂ N —→ `inj₂ N′

    L —→ L′
    ---------------------------------------------------------------------- ξ-case⊎
    case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ case⊎ L′ [inj₁ x ⇒ M |inj₂ y ⇒ N ]

    --------------------------------------------------------- β-inj₁
    case⊎ (`inj₁ V) [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ M [ x := V ]

    --------------------------------------------------------- β-inj₂
    case⊎ (`inj₂ W) [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ N [ y := W ]

### Example

Here is a function to swap the components of a sum:

    swap⊎ : ∅ ⊢ A `⊎ B ⇒ B `⊎ A
    swap⊎ = ƛ z ⇒ case⊎ z
                    [inj₁ x ⇒ `inj₂ x
                    |inj₂ y ⇒ `inj₁ y ]


## Unit type

For the unit type, there is a way to introduce
values of the type but no way to eliminate values of the type.
There are no reduction rules.

### Syntax

    A, B, C ::= ...                     Types
      `⊤                                  unit type

    L, M, N ::= ...                     Terms
      `tt                                 unit value

    V, W ::= ...                        Values
      `tt                                 unit value

### Typing

    ------------ `tt or ⊤-I
    Γ ⊢ `tt ⦂ `⊤

### Reduction

(none)

### Example

Here is the isomorphism between `A` and ``A `× `⊤``:

    to×⊤ : ∅ ⊢ A ⇒ A `× `⊤
    to×⊤ = ƛ x ⇒ `⟨ x , `tt ⟩

    from×⊤ : ∅ ⊢ A `× `⊤ ⇒ A
    from×⊤ = ƛ z ⇒ `proj₁ z


## Alternative formulation of unit type

There is an alternative formulation of the unit type, where in place of
no way to eliminate the type we have a case term that binds zero variables.
We repeat the syntax in full, but only give the new type and reduction rules:

### Syntax

    A, B, C ::= ...                     Types
      `⊤                                  unit type

    L, M, N ::= ...                     Terms
      `tt                                 unit value
      `case⊤ L [tt⇒ N ]                   case

    V, W ::= ...                        Values
      `tt                                 unit value

### Typing

    Γ ⊢ L ⦂ `⊤
    Γ ⊢ M ⦂ A
    ------------------------ case⊤ or ⊤-E
    Γ ⊢ case⊤ L [tt⇒ M ] ⦂ A

### Reduction

    L —→ L′
    ------------------------------------- ξ-case⊤
    case⊤ L [tt⇒ M ] —→ case⊤ L′ [tt⇒ M ]

    ----------------------- β-case⊤
    case⊤ `tt [tt⇒ M ] —→ M

### Example

Here is half the isomorphism between `A` and ``A `× `⊤`` rewritten in the new notation:

    from×⊤-case : ∅ ⊢ A `× `⊤ ⇒ A
    from×⊤-case = ƛ z ⇒ case× z
                          [⟨ x , y ⟩⇒ case⊤ y
                                        [tt⇒ x ] ]


### Translation

We can translate the alternative formulation into one without case:

    (case⊤ L [tt⇒ M ]) †  =  `let z `= (L †) `in (M †)

Here `z` is a variable that does not appear free in `M`.


## Empty type

For the empty type, there is a way to eliminate values of
the type but no way to introduce values of the type.  There are no
values of the type and no β rule, but there is a ξ rule.  The `case⊥`
construct plays a role similar to `⊥-elim` in Agda:

### Syntax

    A, B, C ::= ...                     Types
      `⊥                                  empty type

    L, M, N ::= ...                     Terms
      case⊥ L []                          case

### Typing

    Γ ⊢ L ⦂ `⊥
    ------------------ case⊥ or ⊥-E
    Γ ⊢ case⊥ L [] ⦂ A

### Reduction

    L —→ L′
    ------------------------- ξ-case⊥
    case⊥ L [] —→ case⊥ L′ []

### Example

Here is the isomorphism between `A` and ``A `⊎ `⊥``:

    to⊎⊥ : ∅ ⊢ A ⇒ A `⊎ `⊥
    to⊎⊥ = ƛ x ⇒ `inj₁ x

    from⊎⊥ : ∅ ⊢ A `⊎ `⊥ ⇒ A
    from⊎⊥ = ƛ z ⇒ case⊎ z
                     [inj₁ x ⇒ x
                     |inj₂ y ⇒ case⊥ y
                                 [] ]

## Lists

### Syntax

    A, B, C ::= ...                     Types
      `List A                             list type

    L, M, N ::= ...                     Terms
      `[]                                 nil
      M `∷ N                              cons
      caseL L [[]⇒ M | x ∷ y ⇒ N ]        case

    V, W ::= ...                        Values
      `[]                                 nil
      V `∷ W                              cons

### Typing

    ----------------- `[] or List-I₁
    Γ ⊢ `[] ⦂ `List A

    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ `List A
    -------------------- _`∷_ or List-I₂
    Γ ⊢ M `∷ N ⦂ `List A

    Γ ⊢ L ⦂ `List A
    Γ ⊢ M ⦂ B
    Γ , x ⦂ A , xs ⦂ `List A ⊢ N ⦂ B
    -------------------------------------- caseL or List-E
    Γ ⊢ caseL L [[]⇒ M | x ∷ xs ⇒ N ] ⦂ B

### Reduction

    M —→ M′
    ----------------- ξ-∷₁
    M `∷ N —→ M′ `∷ N

    N —→ N′
    ----------------- ξ-∷₂
    V `∷ N —→ V `∷ N′

    L —→ L′
    --------------------------------------------------------------- ξ-caseL
    caseL L [[]⇒ M | x ∷ xs ⇒ N ] —→ caseL L′ [[]⇒ M | x ∷ xs ⇒ N ]

    ------------------------------------ β-[]
    caseL `[] [[]⇒ M | x ∷ xs ⇒ N ] —→ M

    --------------------------------------------------------------- β-∷
    caseL (V `∷ W) [[]⇒ M | x ∷ xs ⇒ N ] —→ N [ x := V ][ xs := W ]

### Example

Here is the map function for lists:

    mapL : ∅ ⊢ (A ⇒ B) ⇒ `List A ⇒ `List B
    mapL = μ mL ⇒ ƛ f ⇒ ƛ xs ⇒
             caseL xs
               [[]⇒ `[]
               | x ∷ xs ⇒ f · x `∷ mL · f · xs ]


## Formalisation

We now show how to formalise

  * primitive numbers
  * _let_ bindings
  * products
  * an alternative formulation of products

and leave formalisation of the remaining constructs as an exercise.


### Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; sym)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```


### Syntax

```agda
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_
infixr 8 _`⊎_
infixr 9 _`×_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infixl 8 _`*_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_
```

### Types

```agda
data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Nat   : Type
  _`×_  : Type → Type → Type
  _`⊎_  : Type → Type → Type
  𝟙 : Type
  𝟘 : Type
```

### Contexts

```agda
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

### Variables and the lookup judgment

```agda
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B
```

### Terms and the typing judgment

```agda
data _⊢_ : Context → Type → Set where

  -- variables

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- functions

  ƛ_  :  ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  -- naturals

  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      -----
    → Γ ⊢ A

-- begin
  `left_or_ : ∀ {Γ A}
    → Γ ⊢ A
    → (B : Type)
    → Γ ⊢ A `⊎ B

  `right_or_ : ∀ {Γ B}
    → Γ ⊢ B
    → (A : Type)
    → Γ ⊢ A `⊎ B

  ⊎-elim : ∀ {Γ A B C}
    -> Γ ⊢ A `⊎ B
    -> Γ , A ⊢ C
    -> Γ , B ⊢ C
    -> Γ ⊢ C
-- end

  -- fixpoint

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ----------
    → Γ ⊢ A

  -- primitive numbers

  con : ∀ {Γ}
    → ℕ
      -------
    → Γ ⊢ Nat

  _`*_ : ∀ {Γ}
    → Γ ⊢ Nat
    → Γ ⊢ Nat
      -------
    → Γ ⊢ Nat

  -- let

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ B

  -- products

  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `× B

  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ A

  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ B

  -- alternative formulation of products

  case× : ∀ {Γ A B C}
    → Γ ⊢ A `× B
    → Γ , A , B ⊢ C
      --------------
    → Γ ⊢ C

-- begin
  [] : ∀ {Γ}
     → Γ ⊢ 𝟙

--  𝟘-elim : ∀ {A Γ}
--     → Γ , 𝟘 ⊢ A

  𝟘-elim : ∀ {A Γ} 
     → Γ ∋ 𝟘
     → Γ ⊢ A

-- end

```

### Abbreviating de Bruijn indices

```agda
length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
```

## Renaming

```agda
ext : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

𝟘-to-any : ∀ {Γ A} → Γ ⊢ 𝟘 → Γ ⊢ A
𝟘-to-any M = (ƛ 𝟘-elim Z) · M

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (`left M or B) =  `left (rename ρ M) or B
rename ρ (`right M or B)=  `right (rename ρ M) or B
rename ρ (⊎-elim L M N) =   ⊎-elim (rename ρ L) (rename (ext ρ) M) (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
rename ρ (con n)        =  con n
rename ρ (M `* N)       =  rename ρ M `* rename ρ N
rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)
rename ρ `⟨ M , N ⟩     =  `⟨ rename ρ M , rename ρ N ⟩
rename ρ (`proj₁ L)     =  `proj₁ (rename ρ L)
rename ρ (`proj₂ L)     =  `proj₂ (rename ρ L)
rename ρ (case× L M)    =  case× (rename ρ L) (rename (ext (ext ρ)) M)
rename ρ [] = []
rename ρ (𝟘-elim x) = 𝟘-elim (ρ x)
```

## Simultaneous Substitution

```agda
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (`left M or B)      =  `left (subst σ M) or B
subst σ (`right M or B)      =  `right (subst σ M) or B
subst σ (⊎-elim L M N) =   ⊎-elim (subst σ L) (subst (exts σ) M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)
subst σ (con n)        =  con n
subst σ (M `* N)       =  subst σ M `* subst σ N
subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)
subst σ `⟨ M , N ⟩     =  `⟨ subst σ M , subst σ N ⟩
subst σ (`proj₁ L)     =  `proj₁ (subst σ L)
subst σ (`proj₂ L)     =  `proj₂ (subst σ L)
subst σ (case× L M)    =  case× (subst σ L) (subst (exts (exts σ)) M)
subst σ [] = []
subst σ (𝟘-elim x) = 𝟘-to-any (σ x)

--infix 5 _>>>_
--_>>>_ : ∀ {Γ Δ}
--      → (∀ {C} → Γ ∋ C -> Δ ⊢ C)
--      → (∀ {C} → Γ ∋ C -> Δ ⊢ C)
--      → (∀ {C} → Γ ∋ C -> Δ ⊢ C)
--(now >>> later) x with now x
--... | ` y = later {!!}
--... | M = {!!}


```

## Single and double substitution

```agda
_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A

lemma-sigma : ∀ {Γ A}
  → Γ ⊢ A
  → (∀ {C} → Γ , A ∋ C → Γ ⊢ C)
lemma-sigma M Z = M
lemma-sigma _ (S x) = ` x

_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (lemma-sigma M) {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x

_[_][_] : ∀ {Γ A B C}
  → Γ , A , B ⊢ C
  → Γ ⊢ A
  → Γ ⊢ B
    -------------
  → Γ ⊢ C

lemma-sigma-2 : ∀ {Γ A B}
  → Γ ⊢ A
  → Γ ⊢ B
  → (∀ {C} → Γ , A , B ∋ C → Γ ⊢ C)
lemma-sigma-2 V W Z = W
lemma-sigma-2 V W (S Z) = V
lemma-sigma-2 V W (S (S x)) = ` x


_[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} (lemma-sigma-2 V W) N
  where
  σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
  σ Z          =  W
  σ (S Z)      =  V
  σ (S (S x))  =  ` x
```

## Values

```agda
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  -- naturals

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)

  V-left : ∀ {Γ A B} {V : Γ ⊢ A}
    → Value V
      --------------
    → Value (`left V or B)

  V-right : ∀ {Γ A B} {V : Γ ⊢ A}
    → Value V
      --------------
    → Value (`right V or B)

  -- primitives

  V-con : ∀ {Γ n}
      -----------------
    → Value (con {Γ} n)

  -- products

  V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------
    → Value `⟨ V , W ⟩

  V-[] : ∀ {Γ}
    → Value ([] {Γ})

```

Implicit arguments need to be supplied when they are
not fixed by the given arguments.

## Reduction

```agda
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  -- naturals

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]


  ξ-left : ∀ {Γ A B} {M M′ : Γ ⊢ A}
    → M —→ M′
      -----------------
    → `left M or B —→ `left M′ or B

  ξ-right : ∀ {Γ A B} {M M′ : Γ ⊢ A}
    → M —→ M′
      -----------------
    → `right M or B —→ `right M′ or B

  ξ-⊎-elim : ∀ {Γ A B C} {L L′ : Γ ⊢ A `⊎ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → L —→ L′
      -------------------------
    → ⊎-elim L M N —→ ⊎-elim L′ M N

  β-left : ∀ {Γ A B C} {V : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value V
      ----------------------------
    → ⊎-elim (`left V or B) M N —→ M [ V ]

  β-right : ∀ {Γ A B C} {V : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value V
      ----------------------------
    → ⊎-elim (`right V or A) M N —→ N [ V ]


  -- fixpoint

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]

  -- primitive numbers

  ξ-*₁ : ∀ {Γ} {L L′ M : Γ ⊢ Nat}
    → L —→ L′
      -----------------
    → L `* M —→ L′ `* M

  ξ-*₂ : ∀ {Γ} {V M M′ : Γ ⊢ Nat}
    → Value V
    → M —→ M′
      -----------------
    → V `* M —→ V `* M′

  δ-* : ∀ {Γ c d}
      ---------------------------------
    → con {Γ} c `* con d —→ con (c * d)

  -- let

  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M —→ M′
      ---------------------
    → `let M N —→ `let M′ N

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
      -------------------
    → `let V N —→ N [ V ]

  -- products

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
    → M —→ M′
      -------------------------
    → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
    → Value V
    → N —→ N′
      -------------------------
    → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

  ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₁ L —→ `proj₁ L′

  ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₂ L —→ `proj₂ L′

  β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₁ `⟨ V , W ⟩ —→ V

  β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₂ `⟨ V , W ⟩ —→ W

  -- alternative formulation of products

  ξ-case× : ∀ {Γ A B C} {L L′ : Γ ⊢ A `× B} {M : Γ , A , B ⊢ C}
    → L —→ L′
      -----------------------
    → case× L M —→ case× L′ M

  β-case× : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {M : Γ , A , B ⊢ C}
    → Value V
    → Value W
      ----------------------------------
    → case× `⟨ V , W ⟩ M —→ M [ V ][ W ]

```

## Reflexive and transitive closure

```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  step—→ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M —↠ N
    → L —→ M
      ------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```


## Values do not reduce

```agda
V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ          ()
V¬—→ V-zero       ()
V¬—→ (V-suc VM)   (ξ-suc M—→M′)     =  V¬—→ VM M—→M′
V¬—→ (V-left VM)  (ξ-left M—→M′)    =  V¬—→ VM M—→M′
V¬—→ (V-right VM)  (ξ-right M—→M′)    =  V¬—→ VM M—→M′
V¬—→ V-con        ()
V¬—→ V-⟨ VM , _ ⟩ (ξ-⟨,⟩₁ M—→M′)    =  V¬—→ VM M—→M′
V¬—→ V-⟨ _ , VN ⟩ (ξ-⟨,⟩₂ _ N—→N′)  =  V¬—→ VN N—→N′
V¬—→ V-[]         ()
```


## Progress

```agda
data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A}
  → (M : ∅ ⊢ A)
    -----------
  → Progress M
progress (` ())
progress (ƛ N)                              =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                        =  step (β-ƛ VM)
progress (`zero)                            =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                         =  step (ξ-suc M—→M′)
...    | done VM                            =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                         =  step (ξ-case L—→L′)
...    | done V-zero                        =  step β-zero
...    | done (V-suc VL)                    =  step (β-suc VL)
progress (`left M or B) with progress M
...    | step M—→M′                         =  step (ξ-left M—→M′)
...    | done VM                            =  done (V-left VM)
progress (`right M or B) with progress M
...    | step M—→M′                         =  step (ξ-right M—→M′)
...    | done VM                            =  done (V-right VM)
progress (⊎-elim L M N) with progress L
...    | step L—→L′                         =  step (ξ-⊎-elim L—→L′)
...    | done (V-left VM)                   =  step (β-left VM)
...    | done (V-right VM)                  =  step (β-right VM)
progress (μ N)                              =  step β-μ
progress (con n)                            =  done V-con
progress (L `* M) with progress L
...    | step L—→L′                         =  step (ξ-*₁ L—→L′)
...    | done V-con with progress M
...        | step M—→M′                     =  step (ξ-*₂ V-con M—→M′)
...        | done V-con                     =  step δ-*
progress (`let M N) with progress M
...    | step M—→M′                         =  step (ξ-let M—→M′)
...    | done VM                            =  step (β-let VM)
progress `⟨ M , N ⟩ with progress M
...    | step M—→M′                         =  step (ξ-⟨,⟩₁ M—→M′)
...    | done VM with progress N
...        | step N—→N′                     =  step (ξ-⟨,⟩₂ VM N—→N′)
...        | done VN                        =  done (V-⟨ VM , VN ⟩)
progress (`proj₁ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₁ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₁ VM VN)
progress (`proj₂ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₂ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₂ VM VN)
progress (case× L M) with progress L
...    | step L—→L′                         =  step (ξ-case× L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-case× VM VN)
progress []                                =  done V-[]
progress (𝟘-elim ())
```


## Evaluation

```agda
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N

data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```


## Examples

```agda
cube : ∅ ⊢ Nat ⇒ Nat
cube = ƛ (# 0 `* # 0 `* # 0)

_ : cube · con 2 —↠ con 8
_ =
  begin
    cube · con 2
  —→⟨ β-ƛ V-con ⟩
    con 2 `* con 2 `* con 2
  —→⟨ ξ-*₁ δ-* ⟩
    con 4 `* con 2
  —→⟨ δ-* ⟩
    con 8
  ∎

exp10 : ∅ ⊢ Nat ⇒ Nat
exp10 = ƛ (`let (# 0 `* # 0)
            (`let (# 0 `* # 0)
              (`let (# 0 `* # 2)
                (# 0 `* # 0))))

_ : exp10 · con 2 —↠ con 1024
_ =
  begin
    exp10 · con 2
  —→⟨ β-ƛ V-con ⟩
    `let (con 2 `* con 2) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ ξ-let δ-* ⟩
    `let (con 4) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ β-let V-con ⟩
    `let (con 4 `* con 4) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ ξ-let δ-* ⟩
    `let (con 16) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ β-let V-con ⟩
    `let (con 16 `* con 2) (# 0 `* # 0)
  —→⟨ ξ-let δ-* ⟩
    `let (con 32) (# 0 `* # 0)
  —→⟨ β-let V-con ⟩
    con 32 `* con 32
  —→⟨ δ-* ⟩
    con 1024
  ∎

swap× : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap× = ƛ `⟨ `proj₂ (# 0) , `proj₁ (# 0) ⟩

_ : swap× · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
    swap× · `⟨ con 42 , `zero ⟩
  —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
    `⟨ `proj₂ `⟨ con 42 , `zero ⟩ , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₁ (β-proj₂ V-con V-zero) ⟩
    `⟨ `zero , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₂ V-zero (β-proj₁ V-con V-zero) ⟩
    `⟨ `zero , con 42 ⟩
  ∎

swap×-case : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap×-case = ƛ case× (# 0) `⟨ # 0 , # 1 ⟩

_ : swap×-case · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
     swap×-case · `⟨ con 42 , `zero ⟩
   —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
     case× `⟨ con 42 , `zero ⟩ `⟨ # 0 , # 1 ⟩
   —→⟨ β-case× V-con V-zero ⟩
     `⟨ `zero , con 42 ⟩
   ∎

pred : ∅ ⊢ `ℕ ⇒ `ℕ `⊎ 𝟙
pred = ƛ case (# 0) (`right [] or `ℕ) (`left (# 0) or 𝟙)

_ : eval (gas 100) (pred · (`suc (`suc (`suc `zero)))) ≡
  steps
  ((ƛ case (` Z) (`right [] or `ℕ) (`left ` Z or 𝟙)) ·
   `suc (`suc (`suc `zero))
   —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   case (`suc (`suc (`suc `zero))) (`right [] or `ℕ) (`left ` Z or 𝟙)
   —→⟨ β-suc (V-suc (V-suc V-zero)) ⟩
   (`left `suc (`suc `zero) or 𝟙) ∎)
  (done (V-left (V-suc (V-suc V-zero))))
_ = refl

```

#### Exercise `More` (recommended and practice)

Formalise the remaining constructs defined in this chapter.
Make your changes in this file.
Evaluate each example, applied to data as needed,
to confirm it returns the expected answer:

  * sums (recommended)
  * unit type (practice)
  * an alternative formulation of unit type (practice)
  * empty type (recommended)
  * lists (practice)

Please delimit any code you add as follows:

    -- begin
    -- end


#### Exercise `double-subst` (stretch)

Show that a double substitution is equivalent to two single
substitutions.
```agda
ignore-var : ∀ {Γ A C}
           -> Γ ⊢ C
           -> Γ , A ⊢ C
--ignore-var W = subst (λ x → ` (S x)) W
ignore-var W = rename S_ W

-- relate ext and exts


ext-theorem : ∀ {Γ Δ A B}
            → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
            → (x : Γ , B ∋ A)
            → ` (ext ρ x) ≡ exts (λ y -> ` (ρ y)) x
ext-theorem ρ Z = refl
ext-theorem ρ (S x) = refl

--impl : ∀ {Γ C}
--     -> (x : Γ ∋ C)
--     -> rename S_ (` x) ≡ subst (λ x -> ` (S x)) (` x)
--impl x = refl

impl' : ∀ {Γ Δ C}
     → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
     -> (x : Γ ∋ C)
     -> rename ρ (` x) ≡ subst (λ x -> ` (ρ x)) (` x)
impl' ρ x = refl

-- if σ is ` ∘ ρ, then exts σ is ` ∘ ext ρ

--σ-ρ : ∀ {Γ Δ}
--   → (σ : ∀ {A} → Γ ∋ A → Δ ⊢ A)
--   → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
--   → (∀ {B} (M : Γ ⊢ B) → rename ρ M ≡ subst σ M)
--   → (∀ {B C} (M : Γ , C ⊢ B) → rename (ext ρ) M ≡ subst (exts σ) M)
--σ-ρ σ ρ Ms-eq (` Z) = refl
--σ-ρ σ ρ Ms-eq (` (S x)) with Ms-eq (` x)
--... | thing = sym (
--  begin+
--    rename S_ (σ x)
--  ≡⟨ cong (rename S_) (sym thing) ⟩     
--    rename S_ (` ρ x)
--  ≡⟨ refl ⟩
--    ` (S ρ x)
--  ∎+)
--  where open Eq.≡-Reasoning using (_≡⟨⟩_; step-≡) renaming (begin_ to begin+_; _∎ to _∎+)
--        open Eq using (sym)
--
--σ-ρ σ ρ Ms-eq (ƛ M) with σ-ρ (exts σ) (ext ρ) {!!} {!M!}
--... | thing = {!!}
--σ-ρ σ ρ Ms-eq (M · M₁) = {!!}
--σ-ρ σ ρ Ms-eq `zero = {!!}
--σ-ρ σ ρ Ms-eq (`suc M) = {!!}
--σ-ρ σ ρ Ms-eq (case M M₁ M₂) = {!!}
--σ-ρ σ ρ Ms-eq (`left M or B) = {!!}
--σ-ρ σ ρ Ms-eq (`right M or A) = {!!}
--σ-ρ σ ρ Ms-eq (⊎-elim M M₁ M₂) = {!!}
--σ-ρ σ ρ Ms-eq (μ M) = {!!}
--σ-ρ σ ρ Ms-eq (con x) = {!!}
--σ-ρ σ ρ Ms-eq (M `* M₁) = {!!}
--σ-ρ σ ρ Ms-eq (`let M M₁) = {!!}
--σ-ρ σ ρ Ms-eq `⟨ M , M₁ ⟩ = {!!}
--σ-ρ σ ρ Ms-eq (`proj₁ M) = {!!}
--σ-ρ σ ρ Ms-eq (`proj₂ M) = {!!}
--σ-ρ σ ρ Ms-eq (case× M M₁) = {!!}
--σ-ρ σ ρ Ms-eq [] = {!!}
--σ-ρ σ ρ Ms-eq (𝟘-elim x) = {!!}

Rename : Context → Context → Set
Rename Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A

Subst : Context → Context → Set
Subst Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A

open import Function using (_∘_)

σ-of-ρ : ∀{Γ Δ} → Rename Γ Δ → Subst Γ Δ
σ-of-ρ ρ = (λ x -> ` x) ∘ ρ

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

ren-ext : ∀ {Γ Δ}{B C : Type} {ρ : Rename Γ Δ}
        → σ-of-ρ (ext ρ) ≡ exts (σ-of-ρ ρ)
ren-ext {Γ}{Δ}{B}{C}{ρ} = extensionality lemma
  where lemma : ∀ (x : Γ , B ∋ C) -> σ-of-ρ (ext ρ) x ≡ exts (σ-of-ρ ρ) x
        lemma Z = refl
        lemma (S x) = refl

data Core : ∀  {Γ : Context} {A :  Type} -> Γ ⊢ A -> Set where
  c-` : ∀ {Γ A} {x : Γ ∋ A} -> Core (` x)
  c-· : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {M' : Γ ⊢ A} -> Core M -> Core M' -> Core (M · M')
  c-ƛ :  ∀ {Γ A B} {N : Γ , A ⊢ B} -> Core N -> Core (ƛ N)
  c-let : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ , A ⊢ B} -> Core M -> Core N -> Core (`let M N)


cong-exts-applied :  ∀ {Γ Δ A B} {σ σ' : ∀ {A} -> Γ ∋ A -> Δ ⊢ A}
          -> σ ≡ σ'
          -> (x : Γ , A ∋ B)
          -> exts σ x ≡ exts σ' x
cong-exts-applied {Γ} {σ = σ} {σ' = σ'} σ≡σ' Z = refl
cong-exts-applied {Γ} {σ = σ} {σ' = σ'} σ≡σ' (S x) = cong (rename S_) (cong-app σ≡σ' x)

cong-exts :  ∀ {Γ Δ} {σ σ' : ∀ {A} -> Γ ∋ A -> Δ ⊢ A} {B}
          -> (∀ {A} → σ ≡ σ' {A})
          -> (∀ {A} → exts σ {B = B} ≡ exts σ' {A})
cong-exts {Γ} {σ = σ} {σ' = σ'} σ≡σ' = extensionality (cong-exts-applied σ≡σ')

cong-subst : ∀ {Γ Δ A} {σ σ' : ∀ {A} -> Γ ∋ A -> Δ ⊢ A}
           -> (M : Γ ⊢ A)
           -> Core M
           -> (∀ {A} → σ ≡ σ' {A})
           -> subst σ M ≡ subst σ' M
cong-subst (` x) core σ≡σ' = cong-app σ≡σ' x 
cong-subst {Γ} {Δ} {_} {σ} {σ'} (ƛ M) (c-ƛ core) σ≡σ' =
   cong ƛ_ (cong-subst M core (cong-exts σ≡σ'))
cong-subst (M · M₁) (c-· core core₁) σ≡σ' =
   cong₂ _·_ (cong-subst M core σ≡σ') (cong-subst M₁ core₁ σ≡σ')
cong-subst (`let M N) (c-let core-M core-N) σ≡σ' =
   cong₂ `let (cong-subst M core-M σ≡σ') ((cong-subst N core-N (cong-exts σ≡σ')))

rename-subst-ren :  ∀ {Γ Δ A}
   → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
   → (M : Γ ⊢ A)
   → (core : Core M)
   → rename ρ M ≡ subst (σ-of-ρ ρ) M
rename-subst-ren ρ (` x) c-` = refl
rename-subst-ren ρ (M · N) (c-· core core₁) =
   cong₂ _·_ (rename-subst-ren ρ M core) (rename-subst-ren ρ N core₁)
rename-subst-ren ρ (ƛ M) (c-ƛ core) =
  begin+
    ƛ rename (ext ρ) M
  ≡⟨ cong ƛ_ (rename-subst-ren (ext ρ) M core) ⟩
    ƛ subst (σ-of-ρ (ext ρ)) M
  ≡⟨ cong ƛ_ (cong-subst M core (ren-ext {ρ = ρ})) ⟩
    ƛ subst (exts (σ-of-ρ ρ)) M
  ∎+

 where open Eq.≡-Reasoning using (_≡⟨⟩_; step-≡) renaming (begin_ to begin+_; _∎ to _∎+)

rename-subst-ren ρ (`let M N) (c-let cM cN) =
  cong₂ `let (rename-subst-ren ρ M cM) lemma
 where lemma : rename (ext ρ) N ≡ subst (exts (σ-of-ρ ρ)) N
       open Eq.≡-Reasoning using (_≡⟨⟩_; step-≡) renaming (begin_ to begin+_; _∎ to _∎+)
       lemma =
         begin+
           rename (ext ρ) N
         ≡⟨ rename-subst-ren (ext ρ) N cN ⟩
            subst (σ-of-ρ (ext ρ)) N
         ≡⟨ cong-subst N cN ren-ext ⟩
            subst (exts (σ-of-ρ ρ)) N
         ∎+





----    ignore-theorem : ∀ {Γ A C}
----                   -> (W : Γ ⊢ C)
----                   -> rename S_ W ≡ subst (λ x -> ` (S x)) W
----    ignore-theorem (` x) = refl
----    ignore-theorem (ƛ W) = cong ƛ_ {!!}
----    ignore-theorem (W · W₁) = cong₂ _·_ (ignore-theorem W) (ignore-theorem W₁)
----    ignore-theorem `zero = refl
----    ignore-theorem (`suc W) = cong `suc_ (ignore-theorem W)
----    ignore-theorem (case W W₁ W₂) = {!!}
----    ignore-theorem (`left W or B) = {!!}
----    ignore-theorem (`right W or A) = {!!}
----    ignore-theorem (⊎-elim W W₁ W₂) = {!!}
----    ignore-theorem (μ W) = {!!}
----    ignore-theorem (con x) = {!!}
----    ignore-theorem (W `* W₁) = {!!}
----    ignore-theorem (`let W W₁) = {!!}
----    ignore-theorem `⟨ W , W₁ ⟩ = {!!}
----    ignore-theorem (`proj₁ W) = {!!}
----    ignore-theorem (`proj₂ W) = {!!}
----    ignore-theorem (case× W W₁) = {!!}
----    ignore-theorem [] = {!!}
----    ignore-theorem (𝟘-elim x) = {!!}
----    
----    partial : ∀ {Γ A B C}
----          -> (Γ , A , B ⊢ C)
----          -> (Γ ⊢ B)
----          -> (Γ , A ⊢ C)
----    partial {Γ} {A} {B} M W = subst σ M
----      where σ : ∀ {C} -> Γ , A , B ∋ C -> Γ , A ⊢ C
----            σ Z = ignore-var W
----            σ (S x) = ` x
----    
----    
----    --ext-lemma : ∀ {Γ A B C} (V : Γ ⊢ A) (W : Γ , A ⊢ B) (σ : ∀ {C} -> Γ , A ∋ C -> Γ ⊢ C)
----    --  -> W ≡ subst (exts (lemma-sigma V)) (rename S_ W)
----    --          -> ignore-var W ≡ subst (exts σ) (rename (ext S_) (ignore-var W))
----    --ext-lemma W σ eq = {!!}
----    
----    -- exts (lemma-sigma V) Z == Z --- not possible
----    
----    -- exts (lemma-sigma V) (S Z) == rename S_ V
----    -- exts (lemma-sigma V) (S (S x)) == rename S_ (` x) == S x
----    
----    -- lemma-sigma (rename S_ W) = W
----    
----    --simple : ∀ {Γ B} (W : Γ ⊢ B)
----    --       -> subst (lemma-sigma (rename S_ W)) ≡ ignore-var W
----    --simple W = ?
----    
----    
----    
----    simplify : ∀ {Γ A B C} (V : Γ ⊢ A) (W : Γ ⊢ C)
----         -> W ≡ subst (lemma-sigma V) (rename S_ W)
----    simplify V (` x) = {!!}
----    simplify V (ƛ W) = {!!}
----    simplify V (W · W₁) = {!!}
----    simplify V `zero = {!!}
----    simplify V (`suc W) = {!!}
----    simplify V (case W W₁ W₂) = {!!}
----    simplify V (`left W or B) = {!!}
----    simplify V (`right W or A) = {!!}
----    simplify V (⊎-elim W W₁ W₂) = {!!}
----    simplify V (μ W) = {!!}
----    simplify V (con x) = {!!}
----    simplify V (W `* W₁) = {!!}
----    simplify V (`let W W₁) = {!!}
----    simplify V `⟨ W , W₁ ⟩ = {!!}
----    simplify V (`proj₁ W) = {!!}
----    simplify V (`proj₂ W) = {!!}
----    simplify V (case× W W₁) = {!!}
----    simplify V [] = {!!}
----    simplify V (𝟘-elim x) = {!!}
----    
----    -- exts (lemma-sigma V) Z     = ` Z
----    -- exts (lemma-sigma V) (S Z) = rename S_ (lemma-sigma V Z) = rename S_ V
----    -- exts (lemma-sigma V) (S (S x)) = rename S_ (` (S x)) = S (S x)
----    
----    -- rename (ext S_) W = --- preserves Z in W
----    --                     --- renames S x to S (S x) and so on
----    -- 
----    
----    -- theorem: (lemma-sigma V) (ext S_ x) = ` x
----    
----    mytheorem : ∀ {Γ A C} (V : Γ ⊢ A) (x : Γ , A ∋ C)
----              -> exts (lemma-sigma V) (ext S_ x) ≡ ` x
----    mytheorem V Z = refl
----    mytheorem V (S Z) = refl
----    mytheorem V (S (S x)) = refl
----    
----    
----    body : ∀ {Γ A B C} (V : Γ ⊢ A) (W : Γ , B ⊢ C)
----         -> W ≡ subst (exts (lemma-sigma V)) (rename (ext S_) W)
----    body V (` Z) = refl
----    body V (` (S x)) = refl
----    body V (ƛ W) = {!!}
----    body V (W · W₁) = {!!}
----    body V `zero = refl
----    body V (`suc W) = {!!}
----    body V (case W W₁ W₂) = {!!}
----    body V (`left W or B) = {!!}
----    body V (`right W or A) = {!!}
----    body V (⊎-elim W W₁ W₂) = {!!}
----    body V (μ W) = {!!}
----    body V (con x) = refl
----    body V (W `* W₁) = {!!}
----    body V (`let W W₁) = {!!}
----    body V `⟨ W , W₁ ⟩ = {!!}
----    body V (`proj₁ W) = {!!}
----    body V (`proj₂ W) = {!!}
----    body V (case× W W₁) = {!!}
----    body V [] = refl
----    body V (𝟘-elim x) = {!!}
----    
----    basis : ∀ {Γ A B C} (V : Γ ⊢ A) (W : Γ ⊢ B)
----          -> (x : Γ , A , B ∋ C)
----          -> lemma-sigma-2 V W x ≡
----                subst (lemma-sigma V) (lemma-sigma (rename S_ W) x)
----    basis V (` x) Z = refl
----    basis {C = D ⇒ E} V (ƛ W) Z = cong ƛ_ {!!}
----    basis V (W · W₁) Z = cong₂ _·_ (basis V W Z) (basis V W₁ Z)
----    basis V `zero Z = refl
----    basis V (`suc W) Z = cong `suc_ (basis V W Z)
----    basis V (case W W₁ W₂) Z = {!!}
----    basis V (`left W or B) Z = {!!}
----    basis V (`right W or A) Z = {!!}
----    basis V (⊎-elim W W₁ W₂) Z = {!!}
----    basis V (μ W) Z = {!!}
----    basis V (con x) Z = {!!}
----    basis V (W `* W₁) Z = {!!}
----    basis V (`let W W₁) Z = {!!}
----    basis V `⟨ W , W₁ ⟩ Z = {!!}
----    basis V (`proj₁ W) Z = {!!}
----    basis V (`proj₂ W) Z = {!!}
----    basis V (case× W W₁) Z = {!!}
----    basis V [] Z = {!!}
----    basis V (𝟘-elim x) Z = {!!}
----    basis V (` x) (S Z) = {!!}
----    basis V (ƛ W) (S Z) = refl
----    basis V (W · W₁) (S Z) = {!!}
----    basis V `zero (S Z) = {!!}
----    basis V (`suc W) (S Z) = {!!}
----    basis V (case W W₁ W₂) (S Z) = {!!}
----    basis V (`left W or B) (S Z) = {!!}
----    basis V (`right W or A) (S Z) = {!!}
----    basis V (⊎-elim W W₁ W₂) (S Z) = {!!}
----    basis V (μ W) (S Z) = {!!}
----    basis V (con x) (S Z) = {!!}
----    basis V (W `* W₁) (S Z) = {!!}
----    basis V (`let W W₁) (S Z) = {!!}
----    basis V `⟨ W , W₁ ⟩ (S Z) = {!!}
----    basis V (`proj₁ W) (S Z) = {!!}
----    basis V (`proj₂ W) (S Z) = {!!}
----    basis V (case× W W₁) (S Z) = {!!}
----    basis V [] (S Z) = {!!}
----    basis V (𝟘-elim x) (S Z) = {!!}
----    basis V (` x₁) (S (S x)) = {!!}
----    basis V (ƛ W) (S (S x)) = refl
----    basis V (W · W₁) (S (S x)) = {!!}
----    basis V `zero (S (S x)) = {!!}
----    basis V (`suc W) (S (S x)) = {!!}
----    basis V (case W W₁ W₂) (S (S x)) = {!!}
----    basis V (`left W or B) (S (S x)) = {!!}
----    basis V (`right W or A) (S (S x)) = {!!}
----    basis V (⊎-elim W W₁ W₂) (S (S x)) = {!!}
----    basis V (μ W) (S (S x)) = {!!}
----    basis V (con x₁) (S (S x)) = {!!}
----    basis V (W `* W₁) (S (S x)) = {!!}
----    basis V (`let W W₁) (S (S x)) = {!!}
----    basis V `⟨ W , W₁ ⟩ (S (S x)) = {!!}
----    basis V (`proj₁ W) (S (S x)) = {!!}
----    basis V (`proj₂ W) (S (S x)) = {!!}
----    basis V (case× W W₁) (S (S x)) = {!!}
----    basis V [] (S (S x)) = {!!}
----    basis V (𝟘-elim x₁) (S (S x)) = {!!}
----    
----    lemma : ∀ {Γ A B C}
----          → (N : Γ , A , B ⊢ C)
----          → (V : Γ ⊢ A)
----          → (W : Γ ⊢ B)
----          -> N [ V ][ W ] ≡ subst {Γ , A , B} {Γ} (lemma-sigma-2 V W) N
----    lemma N V W  =  refl
----    
----     where open Eq.≡-Reasoning using (_≡⟨⟩_; step-≡) renaming (begin_ to begin+_; _∎ to _∎+)
----    
----    
----    conjecture0 :
----      ∀ {Γ A B C} (V : Γ ⊢ A) (W : Γ ⊢ B) (N : Γ , A , B ⊢ C) →
----        N [ V ][ W ] ≡ (partial N W) [ V ]
----    conjecture0 V W N = {!!}
----    
----    
----    
----    conjecture :
----      ∀ {Γ A B C} (V : Γ ⊢ A) (W : Γ ⊢ B) (N : Γ , A , B ⊢ C) →
----        N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
----    conjecture V W (` x) = {!!}
----    conjecture V W (ƛ N) = {!!}
----    conjecture V W (N · N₁) = {!!}
----    conjecture V W `zero = {!!}
----    conjecture V W (`suc N) = {!!}
----    conjecture V W (case N N₁ N₂) = {!!}
----    conjecture V W (`left N or B) = {!!}
----    conjecture V W (`right N or A) = {!!}
----    conjecture V W (⊎-elim N N₁ N₂) = {!!}
----    conjecture V W (μ N) = {!!}
----    conjecture V W (con x) = {!!}
----    conjecture V W (N `* N₁) = {!!}
----    conjecture V W (`let N N₁) = {!!}
----    conjecture V W `⟨ N , N₁ ⟩ = {!!}
----    conjecture V W (`proj₁ N) = {!!}
----    conjecture V W (`proj₂ N) = {!!}
----    conjecture V W (case× N N₁) = {!!}
----    conjecture V W [] = {!!}
----    conjecture V W (𝟘-elim x) = {!!}


--double-subst :
--  ∀ {Γ A B C} (V : Γ ⊢ A) (W : Γ ⊢ B) (N : Γ , A , B ⊢ C) →
--    N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
--double-subst {Γ} {A} {B} {C} V W N =
--  begin+
--    N [ V ][ W ]
--  ≡⟨ refl ⟩
--    subst {Γ , A , B} (lemma-sigma-2 V W) N
--  ≡⟨ {!!} ⟩
--    (N [ rename S_ W ]) [ V ]
--  ∎+
-- where open Eq.≡-Reasoning using (_≡⟨⟩_; step-≡) renaming (begin_ to begin+_; _∎ to _∎+)
--       σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
--       σ Z          =  W
--       σ (S Z)      =  V
--       σ (S (S x))  =  ` x


```
Note the arguments need to be swapped and `W` needs to have
its context adjusted via renaming in order for the right-hand
side to be well typed.

## Test examples

We repeat the [test examples](/DeBruijn/#examples) from Chapter [DeBruijn](/DeBruijn/),
in order to make sure we have not broken anything in the process of extending our base calculus.
```agda
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two

Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```

## Unicode

This chapter uses the following unicode:

    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs or \sigma)
    †  U+2020  DAGGER (\dag)
    ‡  U+2021  DOUBLE DAGGER (\ddag)
