---
title     : "Permutations":
permalink : /Permutations/
---

```agda
module cs.plfa.part1.Perm where
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
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)
```


## Lists

Lists are defined in Agda as follows:
```agda
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
```
Let's unpack this definition. If `A` is a set, then `List A` is a set.
The next two lines tell us that `[]` (pronounced _nil_) is a list of
type `A` (often called the _empty_ list), and that `_∷_` (pronounced
_cons_, short for _constructor_) takes a value of type `A` and a value
of type `List A` and returns a value of type `List A`.  Operator `_∷_`
has precedence level 5 and associates to the right.

For example,
```agda
_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []
```
denotes the list of the first three natural numbers.  Since `_∷_`
associates to the right, the term parses as `0 ∷ (1 ∷ (2 ∷ []))`.
Here `0` is the first element of the list, called the _head_,
and `1 ∷ (2 ∷ [])` is a list of the remaining elements, called the
_tail_. A list is a strange beast: it has a head and a tail,
nothing in between, and the tail is itself another list!

As we've seen, parameterised types can be translated to
indexed types. The definition above is equivalent to the following:
```agda
data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A
```
Each constructor takes the parameter as an implicit argument.
Thus, our example list could also be written:
```agda
_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))
```
where here we have provided the implicit parameters explicitly.

Including the pragma:

    {-# BUILTIN LIST List #-}

tells Agda that the type `List` corresponds to the Haskell type
list, and the constructors `[]` and `_∷_` correspond to nil and
cons respectively, allowing a more efficient representation of lists.


## List syntax

We can write lists more conveniently by introducing the following definitions:
```agda
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
```
This is our first use of pattern declarations.  For instance,
the third line tells us that `[ x , y , z ]` is equivalent to
`x ∷ y ∷ z ∷ []`, and permits the former to appear either in
a pattern on the left-hand side of an equation, or a term
on the right-hand side of an equation.


## Append

Our first function on lists is written `_++_` and pronounced
_append_:

```agda
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
```
The type `A` is an implicit argument to append, making it a _polymorphic_
function (one that can be used at many types). A list appended to the empty list
yields the list itself. A list appended to a non-empty list yields a list with
the head the same as the head of the non-empty list, and a tail the same as the
other list appended to tail of the non-empty list.

Here is an example, showing how to compute the result
of appending two lists:
```agda
_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎
```
Appending two lists requires time linear in the
number of elements in the first list.


## Reasoning about append

We can reason about lists in much the same way that we reason
about numbers.  Here is the proof that append is associative:
```agda
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎
```
The proof is by induction on the first argument. The base case instantiates
to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs`,
and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated by a recursive
invocation of the proof, in this case `++-assoc xs ys zs`.

Recall that Agda supports [sections](/Induction/#sections).
Applying `cong (x ∷_)` promotes the inductive hypothesis:

    (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

to the equality:

    x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ (xs ++ (ys ++ zs))

which is needed in the proof.

It is also easy to show that `[]` is a left and right identity for `_++_`.
That it is a left identity is immediate from the definition:
```agda
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎
```
That it is a right identity follows by simple induction:
```agda
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎
```
As we will see later,
these three properties establish that `_++_` and `[]` form
a _monoid_ over lists.

## Length

Our next function finds the length of a list:
```agda
length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)
```
Again, it takes an implicit parameter `A`.
The length of the empty list is zero.
The length of a non-empty list
is one greater than the length of the tail of the list.

Here is an example showing how to compute the length of a list:
```agda
_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎
```
Computing the length of a list requires time
linear in the number of elements in the list.

In the second-to-last line, we cannot write simply `length []` but
must instead write `length {ℕ} []`.  Since `[]` has no elements, Agda
has insufficient information to infer the implicit parameter.


## Reasoning about length

The length of one list appended to another is the
sum of the lengths of the lists:
```agda
length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎
```
The proof is by induction on the first argument. The base case
instantiates to `[]`, and follows by straightforward computation.  As
before, Agda cannot infer the implicit type parameter to `length`, and
it must be given explicitly.  The inductive case instantiates to
`x ∷ xs`, and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated
by a recursive invocation of the proof, in this case `length-++ xs ys`,
and it is promoted by the congruence `cong suc`.


## Reverse

Using append, it is easy to formulate a function to reverse a list:
```agda
reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]
```
The reverse of the empty list is the empty list.
The reverse of a non-empty list
is the reverse of its tail appended to a unit list
containing its head.

Here is an example showing how to reverse a list:
```agda
_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎
```
Reversing a list in this way takes time _quadratic_ in the length of
the list. This is because reverse ends up appending lists of lengths
`1`, `2`, up to `n - 1`, where `n` is the length of the list being
reversed, append takes time linear in the length of the first
list, and the sum of the numbers up to `n - 1` is `n * (n - 1) / 2`.
(We will validate that last fact in an exercise later in this chapter.)

#### Exercise `reverse-++-distrib` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first:

    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

```agda
-- Your code goes here
reverse-++-distrib : ∀ {A : Set} -> ∀ (xs ys : List A) ->
    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys =
  begin 
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) ([ x ]) ⟩
    reverse ys ++ reverse xs ++ [ x ]
  ∎


```


#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution:

    reverse (reverse xs) ≡ xs

```agda
-- Your code goes here
reverse-singleton : ∀ {A : Set} -> ∀ (x : A) -> reverse [ x ] ≡ [ x ]
reverse-singleton x = refl

reverse-involution : ∀ {A : Set} -> ∀ (xs : List A) ->
    reverse (reverse xs) ≡ xs
reverse-involution [] = refl
reverse-involution (x ∷ xs) =
  begin
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) ([ x ]) ⟩
    reverse (reverse [ x ]) ++ reverse (reverse xs)
  ≡⟨ cong (_++ (reverse (reverse xs))) (reverse-singleton x) ⟩
    [ x ] ++ reverse (reverse xs)
  ≡⟨ cong (x ∷_ ) (reverse-involution xs) ⟩
    (x ∷ xs)
  ∎


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

Having defined shunt by generalisation, it is now easy to respecialise to
give a more efficient definition of reverse:
```agda
reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []
```

Given our previous lemma, it is straightforward to show
the two definitions equivalent:
```agda
reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎
```

Here is an example showing fast reverse of the list `[ 0 , 1 , 2 ]`:
```agda
_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎
```
Now the time to reverse a list is linear in the length of the list.

## Map {#Map}

Map applies a function to every element of a list to generate a corresponding list.
Map is an example of a _higher-order function_, one which takes a function as an
argument or returns a function as a result:
```agda
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs
```
Map of the empty list is the empty list.
Map of a non-empty list yields a list
with head the same as the function applied to the head of the given list,
and tail the same as map of the function applied to the tail of the given list.

Here is an example showing how to use map to increment every element of a list:
```agda
_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎
```
Map requires time linear in the length of the list.

It is often convenient to exploit currying by applying
map to a function to yield a new function, and at a later
point applying the resulting function:
```agda
sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎
```

A type that is parameterised on another type, such as list, often has a
corresponding map, which accepts a function and returns a function
from the type parameterised on the domain of the function to the type
parameterised on the range of the function. Further, a type that is
parameterised on _n_ types often has a map that is parameterised on
_n_ functions.


#### Exercise `map-compose` (practice)

Prove that the map of a composition is equal to the composition of two maps:

    map (g ∘ f) ≡ map g ∘ map f

The last step of the proof requires extensionality.

```agda
-- Your code goes here
open import plfa.part1.Isomorphism using (extensionality)
map-compose : ∀ {A B C : Set} -> ∀ (f : A -> B) -> ∀ (g : B -> C) -> 
    map (g ∘ f) ≡ map g ∘ map f
map-compose {A} f g = extensionality elements
  where elements : ∀ (as : List A) -> map (g ∘ f) as ≡ map g (map f as)
        elements [] = refl
        elements (a ∷ as) = cong (((g ∘ f) a) ∷_) (elements as)
```

#### Exercise `map-++-distribute` (practice)

Prove the following relationship between map and append:

    map f (xs ++ ys) ≡ map f xs ++ map f ys

```agda
-- Your code goes here
```

#### Exercise `map-Tree` (practice)

Define a type of trees with leaves of type `A` and internal
nodes of type `B`:
```agda
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
```
Define a suitable map operator over trees:

    map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D

```agda
-- Your code goes here
```

## Fold {#Fold}

Fold takes an operator and a value, and uses the operator to combine
each of the elements of the list, taking the given value as the result
for the empty list:
```agda
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs
```
Fold of the empty list is the given value.
Fold of a non-empty list uses the operator to combine
the head of the list and the fold of the tail of the list.

Here is an example showing how to use fold to find the sum of a list:
```agda
_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎
```
Here we have an instance of `foldr` where `A` and `B` are both `ℕ`.
Fold requires time linear in the length of the list.

It is often convenient to exploit currying by applying
fold to an operator and a value to yield a new function,
and at a later point applying the resulting function:
```agda
sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎
```

Just as the list type has two constructors, `[]` and `_∷_`,
so the fold function takes two arguments, `e` and `_⊗_`
(in addition to the list argument).
In general, a data type with _n_ constructors will have
a corresponding fold function that takes _n_ arguments.

As another example, observe that

    foldr _∷_ [] xs ≡ xs

Here, if `xs` is of type `List A`, then we see we have an instance of
`foldr` where `A` is `A` and `B` is `List A`.  It follows that

    xs ++ ys ≡ foldr _∷_ ys xs

Demonstrating both these equations is left as an exercise.


#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example:

    product [ 1 , 2 , 3 , 4 ] ≡ 24

```agda
-- Your code goes here
```

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows:

    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

```agda
-- Your code goes here
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
--foldr-++ _⊗_ e xs [] rewrite ++-identityʳ xs = refl
--foldr-++ _⊗_ e xs (y ∷ ys) = {!!}
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    (x ⊗ foldr _⊗_ e (xs ++ ys))
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
    (x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs)
  ∎




```

#### Exercise `foldr-∷` (practice)

Show

    foldr _∷_ [] xs ≡ xs

Show as a consequence of `foldr-++` above that

    xs ++ ys ≡ foldr _∷_ ys xs


```agda
-- Your code goes here
```

#### Exercise `map-is-foldr` (practice)

Show that map can be defined using fold:

    map f ≡ foldr (λ x xs → f x ∷ xs) []

The proof requires extensionality.

```agda
-- Your code goes here
```

#### Exercise `fold-Tree` (practice)

Define a suitable fold function for the type of trees given earlier:

    fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C


```agda
-- Your code goes here
```

#### Exercise `map-is-fold-Tree` (practice)

Demonstrate an analogue of `map-is-foldr` for the type of trees.

```agda
-- Your code goes here
```

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows:
```agda
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
```
For example:
```agda
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl
```
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`:

    sum (downFrom n) * 2 ≡ n * (n ∸ 1)


## Monoids

Typically when we use a fold the operator is associative and the
value is a left and right identity for the operator, meaning that the
operator and the value form a _monoid_.

We can define a monoid as a suitable record type:
```agda
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid
```

As examples, sum and zero, multiplication and one, and append and the empty
list, are all examples of monoids:
```agda
+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }
```

If `_⊗_` and `e` form a monoid, then we can re-express fold on the
same operator and an arbitrary value:
```agda
foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎
```

In a previous exercise we showed the following.
```agda
postulate
  foldr-++' : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) (xs ys : List A) →
    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
```

As a consequence we can decompose fold over append in a monoid
into two folds as follows.
```agda
foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎
```

#### Exercise `foldl` (practice)

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example:

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

```agda
-- Your code goes here
```


#### Exercise `foldr-monoid-foldl` (practice)

Show that if `_⊗_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.

```agda
-- Your code goes here
```


## All {#All}

We can also define predicates over lists. Two of the most important
are `All` and `Any`.

Predicate `All P` holds if predicate `P` is satisfied by every element of a list:
```agda
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
```
The type has two constructors, reusing the names of the same constructors for lists.
The first asserts that `P` holds for every element of the empty list.
The second asserts that if `P` holds of the head of a list and for every
element of the tail of a list, then `P` holds for every element of the list.
Agda uses types to disambiguate whether the constructor is building
a list or evidence that `All P` holds.

For example, `All (_≤ 2)` holds of a list where every element is less
than or equal to two.  Recall that `z≤n` proves `zero ≤ n` for any
`n`, and that if `m≤n` proves `m ≤ n` then `s≤s m≤n` proves `suc m ≤
suc n`, for any `m` and `n`:
```agda
_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []
```
Here `_∷_` and `[]` are the constructors of `All P` rather than of `List A`.
The three items are proofs of `0 ≤ 2`, `1 ≤ 2`, and `2 ≤ 2`, respectively.

(One might wonder whether a pattern such as `[_,_,_]` can be used to
construct values of type `All` as well as type `List`, since both use
the same constructors. Indeed it can, so long as both types are in
scope when the pattern is declared.  That's not the case here, since
`List` is defined before `[_,_,_]`, but `All` is defined later.)


## Any

Predicate `Any P` holds if predicate `P` is satisfied by some element of a list:
```agda
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
```
The first constructor provides evidence that the head of the list
satisfies `P`, while the second provides evidence that some element of
the tail of the list satisfies `P`.  For example, we can define list
membership as follows:
```agda
infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)
```
For example, zero is an element of the list `[ 0 , 1 , 0 , 2 ]`.  Indeed, we can demonstrate
this fact in two different ways, corresponding to the two different
occurrences of zero in the list, as the first element and as the third element:
```agda
_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))
```
Further, we can demonstrate that three is not in the list, because
any possible proof that it is in the list leads to contradiction:
```agda
not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))
```
The five occurrences of `()` attest to the fact that there is no
possible evidence for `3 ≡ 0`, `3 ≡ 1`, `3 ≡ 0`, `3 ≡ 2`, and
`3 ∈ []`, respectively.

## All and append

A predicate holds for every element of one list appended to another if and
only if it holds for every element of both lists:
```agda
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩
```

#### Exercise `Any-++-⇔` (recommended)

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

#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.

```agda
-- Your code goes here
```

#### Exercise `¬Any⇔All¬` (recommended)

Show that `Any` and `All` satisfy a version of De Morgan's Law:

    (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs

(Can you see why it is important that here `_∘_` is generalised
to arbitrary levels, as described in the section on
[universe polymorphism](/Equality/#unipoly)?)

Do we also have the following?

    (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs

If so, prove; if not, explain why.


```agda
```

#### Exercise `¬Any≃All¬` (stretch)

Show that the equivalence `¬Any⇔All¬` can be extended to an isomorphism.
You will need to use extensionality.

```agda
-- Your code goes here

```

#### Exercise `All-∀` (practice)

Show that `All P xs` is isomorphic to `∀ x → x ∈ xs → P x`.

```agda
-- You code goes here
```


#### Exercise `Any-∃` (practice)

Show that `Any P xs` is isomorphic to `∃[ x ] (x ∈ xs × P x)`.

```agda
-- You code goes here
```


## Decidability of All

If we consider a predicate as a function that yields a boolean,
it is easy to define an analogue of `All`, which returns true if
a given predicate returns true for every element of a list:
```agda
all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p
```
The function can be written in a particularly compact style by
using the higher-order functions `map` and `foldr`.

As one would hope, if we replace booleans by decidables there is again
an analogue of `All`.  First, return to the notion of a predicate `P` as
a function of type `A → Set`, taking a value `x` of type `A` into evidence
`P x` that a property holds for `x`.  Say that a predicate `P` is _decidable_
if we have a function that for a given `x` can decide `P x`:
```agda
Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)
```
Then if predicate `P` is decidable, it is also decidable whether every
element of a list satisfies the predicate:
```agda
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }
```
If the list is empty, then trivially `P` holds for every element of
the list.  Otherwise, the structure of the proof is similar to that
showing that the conjunction of two decidable propositions is itself
decidable, using `_∷_` rather than `⟨_,_⟩` to combine the evidence for
the head and tail of the list.


#### Exercise `Any?` (stretch)

Just as `All` has analogues `all` and `All?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `Any?` which determine whether a predicate holds
for some element of a list.  Give their definitions.

```agda
any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ false ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no (λ ())
Any? P? (x ∷ xs) with P? x   | Any? P? xs
...                 | no ¬Px | no ¬Pxs     =  no λ{ (here x) → ¬Px x ; (there xs) → ¬Pxs xs}
...                 | yes Px | _           =  yes (here Px)
...                 | _      | yes Pxs     =  yes (there Pxs)


-- Your code goes here
```


#### Exercise `split` (stretch)

The relation `merge` holds when two lists merge to give a third list.
```agda
data merge {A : Set} : (xs ys zs : List A) → Set where

  [] :
      --------------
      merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge xs (y ∷ ys) (y ∷ zs)
```

For example,
```agda
_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

```

Given a decidable predicate and a list, we can split the list
into two lists that merge to give the original list, where all
elements of one list satisfy the predicate, and all elements of
the other do not satisfy the predicate.

Define the following variant of the traditional `filter` function on
lists, which given a decidable predicate and a list returns a list of
elements that satisfy the predicate and a list of elements that don't,
with their corresponding proofs.

    split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
      → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )

```agda
split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
      → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )
split P? [] = ⟨ [] , ⟨ [] , ⟨ [] , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩
split P? (z ∷ zs) with P? z | split P? zs
... | yes Pz | ⟨ xs , ⟨ ys , ⟨ xs-ys-zs , ⟨ Pxs , ¬Pys ⟩ ⟩ ⟩ ⟩ = 
                         ⟨ (z ∷ xs) , ⟨ ys , ⟨ (left-∷ xs-ys-zs) , ⟨ Pz ∷ Pxs , ¬Pys ⟩ ⟩ ⟩ ⟩
... | no ¬Pz | ⟨ xs , ⟨ ys , ⟨ xs-ys-zs , ⟨ Pxs , ¬Pys ⟩ ⟩ ⟩ ⟩ = 
                         ⟨ (xs) , ⟨ z ∷ ys , ⟨ (right-∷ xs-ys-zs) , ⟨ Pxs , ¬Pz ∷ ¬Pys ⟩ ⟩ ⟩ ⟩
-- Your code goes here
```

## Ordered lists

```agda


open import Data.Product using (Σ-syntax)

data Permutation++ {A : Set} : (xs ys zs : List A) -> Set where
  -- xs is a permutation of ys ++ zs
  [] : Permutation++ [] [] []
  here : {xs ys zs : List A} -> {x : A} -> Permutation++ xs ys zs
      ->  Permutation++ (x ∷ xs) ys (x ∷ zs)
  there-left : {xs ys zs : List A} -> {y : A}
       -> Permutation++ xs (y ∷ ys) zs
       -> Permutation++ xs ys (y ∷ zs)
  there-right : {xs ys zs : List A} -> {z : A}
       -> Permutation++ xs ys (z ∷ zs)
       -> Permutation++ xs (z ∷ ys) zs

infix 4 _⋈_
data _⋈_ {A : Set} : (xs ys : List A) -> Set where
  permutation : ∀ {xs zs : List A} -> Permutation++ xs [] zs -> xs ⋈ zs

data _⊳_≡_ {A : Set} : (x : A) (xs ys : List A) -> Set where
  -- ys is formed by inserting x somewhere into xs
  here : ∀ {x : A} {xs : List A} -> x ⊳ xs ≡ (x ∷ xs)
  there : ∀ {x y : A} {ys zs : List A} -> y ⊳ ys ≡ zs -> y ⊳ (x ∷ ys) ≡ (x ∷ zs)

infix 4 _<>_
data _<>_ {A : Set} : (xs ys : List A) -> Set where
  [] : [] <> []
  insert : ∀ {x : A} {xs ys zs : List A} -> x ⊳ ys ≡ zs -> xs <> ys -> x ∷ xs <> zs

self' : ∀ {A : Set} (xs : List A) -> xs <> xs
self' [] = []
self' (x ∷ xs) = insert here (self' xs)

refl-<> : ∀ {A : Set} {xs : List A} -> xs <> xs
refl-<> {xs = xs} = self' xs

sym-<>  : ∀ {A : Set} {xs ys : List A} -> xs <> ys -> ys <> xs
sym-<> [] = []
sym-<> (insert here pf) = insert here (sym-<> pf)
sym-<> (insert {ys = y ∷ ys} (there {y = x} x⊳ys≡zs) pf) with sym-<> pf
... | thing = {!!}

insertion : ∀ {A : Set} {x : A} {xs zs : List A} -> x ⊳ xs ≡ zs -> (x ∷ xs) <> zs
insertion here = insert here refl-<>
insertion (there pf) = insert (there pf) refl-<>

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

find-<> : ∀ {A : Set} {x : A} {xs ys zs : List A}
       -> (x ∷ xs) <> ys
       -> ∃[ zs ] x ⊳ zs ≡ ys
find-<> (insert {ys = ys} pf _) = ⟨ ys , pf ⟩
 
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

<>-same : ∀ {A : Set} {xs ys : List A} -> (xs <> ys) -> same-length xs ys
<>-same [] = []
<>-same (insert x pf) with insert-same x | <>-same pf
... | same-∷ pf' | pf'' = same-∷ (trans-same pf'' pf')


reverse-insert : ∀ {A : Set} {x : A} {xs : List A}
               -> (x ∈ xs) -> ∃[ ys ] x ⊳ ys ≡ xs
reverse-insert (here {xs = ys} refl) = ⟨ ys , here ⟩
reverse-insert (there {x = y} x∈xs) with reverse-insert x∈xs
... | ⟨ ys , x>xs=ys ⟩ = ⟨ y ∷ ys , there x>xs=ys ⟩

pullout-x : ∀ {A : Set} {x : A} {xs ys zs : List A}
      -> x ⊳ xs ≡ ys
      -> ys <> zs
      -> ∃[ as ] x ⊳ as ≡ zs × xs <> as
pullout-x here (insert {ys = ys} {zs = zs} a>as==bs perm) = ⟨ ys , ⟨ a>as==bs , perm ⟩ ⟩
pullout-x {xs = y' ∷ _} (there insertion) (insert here ys'<>as) 
    with pullout-x insertion ys'<>as
... | ⟨ bs , ⟨ z>bs=ys , ys<>bs ⟩ ⟩ = ⟨ y' ∷ bs , ⟨ there z>bs=ys ,  insert here ys<>bs   ⟩ ⟩
pullout-x {zs = z' ∷ zs'} (there insertion) (insert (there y'>cs==zs') ys'<>z'::cs) 
   with pullout-x insertion ys'<>z'::cs
... | ⟨ cs , ⟨ here , xs'<>cs ⟩ ⟩ = ⟨ zs' , ⟨ here , (insert y'>cs==zs' xs'<>cs) ⟩ ⟩
... | ⟨ (z' ∷ ds) , ⟨ there x>ds=cs , xs'<>z'∷ds ⟩ ⟩
        with insert-swap x>ds=cs y'>cs==zs'
...                | ⟨ es , ⟨ y'>ds=es , x>es=zs' ⟩ ⟩ = 
                         ⟨ (z' ∷ es) , ⟨ (there x>es=zs') , (insert (there y'>ds=es) xs'<>z'∷ds) ⟩ ⟩

trans-<> : ∀ {A : Set} {xs ys zs : List A} -> xs <> ys -> ys <> zs -> xs <> zs
trans-<> [] [] = []
trans-<> {A} (insert x⊳as≡ys xs<>as) ys<>zs with pullout-x x⊳as≡ys ys<>zs
... | ⟨ cs , ⟨ x⊳cs≡zs , as<>cs ⟩ ⟩ = insert x⊳cs≡zs (trans-<> xs<>as as<>cs)

<>-head-swap : ∀ {A : Set} {x₁ x₂ : A} {xs ys : List A}
               -> xs <> ys
               -> (x₁ ∷ x₂ ∷ xs) <> (x₂ ∷ x₁ ∷ ys)
<>-head-swap xs<>ys = insert (there here) (insert here xs<>ys)

⋈-head-swap : ∀ {A : Set} {x₁ x₂ : A} {xs ys : List A}
               -> xs ⋈ ys
               -> (x₁ ∷ x₂ ∷ xs) ⋈ (x₂ ∷ x₁ ∷ ys)
⋈-head-swap (permutation xs⋈ys) = permutation (there-left (here (there-right (here xs⋈ys))))



lemma-ins : ∀ {A : Set} {x : A} {xs ys ys' zs : List A}
          -> x ⊳ ys ≡ ys'
          -> Permutation++ zs xs ys
          -> Permutation++ (x ∷ zs) xs ys'
lemma-ins here perm = here perm
lemma-ins (there ins) perm with lemma-ins ins (there-right perm)
... | perm' = there-left perm'

legacy-insert : ∀ {A : Set} {x : A} {xs ys zs : List A}
              -> x ⊳ ys ≡ zs -> xs ⋈ ys -> x ∷ xs ⋈ zs
legacy-insert ins (permutation p) = permutation (lemma-ins ins p)

<>→⋈ : ∀ {A : Set} {xs ys : List A} -> xs <> ys -> xs ⋈ ys
<>→⋈ [] = permutation []
<>→⋈ (insert ins xs<>ys) = legacy-insert ins (<>→⋈ xs<>ys)

shunt-⊳ : ∀ {A : Set} {x : A} {ys zs : List A} (xs : List A)
        -> x ⊳ ys ≡ zs
        -> x ⊳ shunt xs ys ≡ shunt xs zs
shunt-⊳ [] pf = pf
shunt-⊳ (y ∷ ys) pf = shunt-⊳ ys (there pf)

reverse-lemma : ∀ {A : Set} {xs ys zs : List A}
              -> Permutation++ zs xs ys -> zs <> shunt xs ys
reverse-lemma [] = []
reverse-lemma {xs = []} (here p) with reverse-lemma p
... | p' = insert here p'
reverse-lemma {xs = x ∷ xs} (here p) = insert (shunt-⊳ xs (there here)) (reverse-lemma p)
reverse-lemma (there-left p) = reverse-lemma p
reverse-lemma (there-right p) = reverse-lemma p

⋈→<> : ∀ {A : Set} {xs ys : List A} -> xs ⋈ ys -> xs <> ys
⋈→<> (permutation p) = reverse-lemma p

infix 4 _swapped-is_
data _swapped-is_ {A : Set} : List A -> List A -> Set where
  here : ∀ {x y : A} {zs : List A} -> x ∷ y ∷ zs swapped-is y ∷ x ∷ zs
  there : ∀ {z : A} {xs ys : List A} -> xs swapped-is ys -> z ∷ xs swapped-is z ∷ ys

infix 4 _swapped*-is_
data _swapped*-is_ {A : Set} : List A -> List A -> Set where
  refl : ∀ {xs : List A} -> xs swapped*-is xs
  swap : ∀ {xs ys zs : List A} -> (xs swapped-is ys) -> ys swapped*-is zs -> xs swapped*-is zs

swapped→<> : ∀ {A : Set} {xs ys : List A} (pf : xs swapped-is ys) -> xs <> ys
swapped→<> here = insert (there here) refl-<>
swapped→<> (there pf) = insert here (swapped→<> pf)

swapped*→<> : ∀ {A : Set} {xs ys : List A} (pf : xs swapped*-is ys) -> xs <> ys
swapped*→<> refl = refl-<>
swapped*→<> (swap one many) = trans-<> (swapped→<> one) (swapped*→<> many)

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

<>→swapped* : ∀ {A : Set} {xs ys : List A} -> (xs <> ys) -> (xs swapped*-is ys)
<>→swapped* [] = refl
<>→swapped* (insert ins pf) = insert-swapped* ins (<>→swapped* pf)


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

<>-∈ : ∀ {A : Set} {xs ys : List A} -> (xs <> ys) -> ∀ {x : A} -> (x ∈ xs) ⇔ (x ∈ ys)
<>-∈ {xs = xs} {ys = ys} xs<>ys! {x} = record { to = to xs<>ys! ; from = from xs<>ys! }
  where to : ∀ {A : Set} {xs ys : List A} -> (xs <> ys) -> ∀ {x : A} -> (x ∈ xs) -> (x ∈ ys)
        to (insert x⊳ys≡zs _) (here refl) = insert-∈-left x⊳ys≡zs
        to (insert x⊳ys≡zs pf) (there x∈xs) = insert-∈-right x⊳ys≡zs (to pf x∈xs)

        from : ∀ {A : Set} {xs ys : List A} -> (xs <> ys) -> ∀ {x : A} -> (x ∈ ys) -> (x ∈ xs)
        from (insert here pf) (here refl) = here refl
        from (insert (there x⊳ys≡zs) pf) (here refl) = there (from pf (here refl))
        from (insert x⊳bs≡y∷ys xs<>bs) z∈ys with insert-breakdown x⊳bs≡y∷ys z∈ys
        ... | inj₁ x≡y = here x≡y
        ... | inj₂ x∈ys = there (from xs<>bs x∈ys)


cong-<> : ∀ {A : Set} {xs ys zs : List A}
        -> ys ≡ zs -> xs <> ys -> xs <> zs
cong-<> refl pf = pf

module <>-Reasoning {A : Set} where

  infix  1 begin<>_
  infixr 2 _<>⟨⟩_ step-<> step-≡-<>
  infix  3 _∎<>

  begin<>_ : ∀ {x y : List A}
    → x <> y
      -----
    → x <> y
  begin<> x<>y  =  x<>y

  _<>⟨⟩_ : ∀ (x : List A) {y : List A}
    → x <> y
      -----
    → x <> y
  x <>⟨⟩ x<>y  =  x<>y

  step-<> : ∀ (x {y z} : List A) → y <> z → x <> y → x <> z
  step-<> x y<>z x<>y  =  trans-<> x<>y y<>z

  step-≡-<> : ∀ (xs : List A)  {ys zs : List A} → ys <> zs -> xs ≡ ys -> xs <> zs
  step-≡-<> xs xs<>ys refl = xs<>ys

  syntax step-<> x y<>z x<>y  =  x <>⟨  x<>y ⟩ y<>z
  syntax step-≡-<> xs xs<>ys zs≡xs  =  xs <>≡⟨ zs≡xs ⟩ xs<>ys

  _∎<> : ∀ (x : List A)
      -----
    → x <> x
  x ∎<>  =  refl-<>

open <>-Reasoning


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
       -> ns <> n ∷ (xs ++ ys)
       -> Heap ns

open import Data.Nat.Properties using (≤-trans; ≤-refl)



--min : ∀ {ns : List ℕ} (h : Heap ns)
--    -> ∃[ n ] n ∈ ns
--    -> ∃[ n ] n ∈ ns × (∀ {m : ℕ} -> m ∈ ns -> n ≤ m)
--min {ns} (root {xs = xs} {ys = ys} n left right small-l small-r perm) _ = ⟨ n , ⟨ n∈ns , smallest ⟩ ⟩
--  where n∈ns : n ∈ ns
--        open _⇔_
--        n∈ns = from (<>-∈ perm) (here refl)
--        smallest : ∀ {m : ℕ} → m ∈ ns → n ≤ m
--        smallest {m} m∈ns with to (<>-∈ perm) m∈ns
--        ... | here refl = ≤-refl
--        ... | there m∈xs++ys with to (Any-++-⇔ xs ys) m∈xs++ys
--        ... | inj₁ m∈xs = small-l m∈xs
--        ... | inj₂ m∈ys = small-r m∈ys



insert-snoc :  ∀ {A : Set} {xs ys : List A} {x z : A}
            -> x ⊳ xs ≡ ys
            -> x ⊳ (xs ++ [ z ]) ≡ (ys ++ [ z ])
insert-snoc here = here
insert-snoc (there pf) = there (insert-snoc pf)

cong-<>-snoc : ∀ {A : Set} {xs ys : List A} {z : A}
           -> xs <> ys
           -> xs ++ [ z ] <> ys ++ [ z ]
cong-<>-snoc [] = refl-<>
cong-<>-snoc (insert x pf) = insert (insert-snoc x) (cong-<>-snoc pf)

cong-<>-++ : ∀ {A : Set} {xs ys zs : List A}
           -> xs <> ys
           -> xs ++ zs <> ys ++ zs
cong-<>-++ {xs = xs} {ys = ys} {zs = []} xs<>ys rewrite ++-identityʳ xs | ++-identityʳ ys = xs<>ys
cong-<>-++ {xs = xs} {ys = ys} {zs = z ∷ zs} pf = 
  begin<>
    xs ++ z ∷ zs
  <>≡⟨ sym (++-assoc xs [ z ] zs) ⟩
    (xs ++ [ z ]) ++ zs
  <>⟨ cong-<>-++ (cong-<>-snoc pf) ⟩
    (ys ++ [ z ]) ++ zs
  <>≡⟨ ++-assoc ys [ z ] zs ⟩
    ys ++ z ∷ zs
  ∎<>

merge-heaps : ∀ {ns ms : List ℕ} -> Heap ns -> Heap ms -> Heap (ns ++ ms)
merge-heaps [] h = h
merge-heaps {ns = ns} h [] rewrite ++-identityʳ ns = h
merge-heaps {ns = ns} {ms = ms}
            h₁@(root {xs = xs} {ys = ys} {ns = ns₁} n₁ l₁ r₁ small₁ perm1)
            h₂@(root {ns = ns₂} n₂ l₂ r₂ small₂ perm2) 
  with compare n₁ n₂
... | less n₁≤n₂ = root n₁ l₁ (merge-heaps r₁ h₂) lemma2 lemma1
        where lemma1 : ns ++ ms <> n₁ ∷ xs ++ ys ++ ms
              lemma2 : ∀ {m : ℕ} → m ∈ ns ++ ms → n₁ ≤ m
              lemma1 = begin<>
                         ns ++ ms
                       <>⟨ cong-<>-++ perm1 ⟩
                         (n₁ ∷ xs ++ ys) ++ ms
                       <>≡⟨ refl ⟩
                         n₁ ∷ (xs ++ ys) ++ ms
                       <>≡⟨ cong (_∷_ n₁) (++-assoc xs ys ms) ⟩
                         n₁ ∷ xs ++ ys ++ ms
                       ∎<>

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

length-perm : ∀ {A : Set} {xs ys : List A} {k : ℕ} -> length xs is k -> xs <> ys -> length ys is k
length-perm [] [] = []
length-perm (there pf) (insert here perm) = there (length-perm pf perm)
length-perm (there (there as-l-k)) (insert (there a⊳ys≡zs) (insert x⊳xs≡ys perm))
   = there (insert-length a⊳ys≡zs (length-pred (insert-length x⊳xs≡ys (length-perm as-l-k perm))))

delete-min : ∀ {ns : List ℕ} {k : ℕ}
           -> length ns is suc k
           -> (h : Heap ns)
           -> ∃[ m ] ∃[ ms ] Heap ms × length ms is k × (ns <> m ∷ ms) × (∀ {z : ℕ} -> (z ∈ ns) -> m ≤ z)
delete-min (len) (root n left right small perm) with heap-elements (merge-heaps left right)
... | ⟨ elements , refl ⟩ =
        ⟨ n , ⟨ elements , ⟨ newheap , ⟨ length-pred (length-perm len perm) , ⟨ perm , small ⟩ ⟩ ⟩ ⟩ ⟩
  where newheap = merge-heaps left right

singleton-heap : ∀ (n : ℕ) -> Heap [ n ]
singleton-heap n = root n [] [] (λ { (here refl) → ≤-refl}) refl-<>

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



drain-heap : ∀ {ns : List ℕ} {n : ℕ} -> (length ns is n) -> Heap ns -> ∃[ ms ] ns <> ms × Ordered ms
drain-heap {[]} {zero} pf [] = ⟨ [] , ⟨ [] , ordered-[] ⟩ ⟩
drain-heap {z ∷ zs} {suc k} (length) h@(root n _ _ orig-order perm)
  with delete-min length h -- ⟨ n , from (<>-∈ perm) (here refl) ⟩
... | ⟨ min , ⟨ ms , ⟨ newheap , ⟨ len , ⟨ perm1 , small ⟩ ⟩ ⟩ ⟩ ⟩ with drain-heap len newheap
... | ⟨ rest , ⟨ ms<>rest , ordered ⟩ ⟩ = ⟨ min ∷ rest , ⟨ fullperm , fullorder ⟩ ⟩
  where smallest = λ y y∈rest → small (from (<>-∈ perm1) (there (from (<>-∈ ms<>rest) y∈rest)))
        fullorder = from (Ordered-≤ min rest) ⟨ ordered , smallest ⟩
        fullperm : z ∷ zs <> min ∷ rest
        fullperm = 
           begin<>
             z ∷ zs
           <>⟨ perm1 ⟩ 
             min ∷ ms
           <>⟨ insert here ms<>rest ⟩ 
             min ∷ rest
           ∎<>

             
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
   ⟨ 1 + kₗ + kᵣ , length-perm (there (length-++-is lenₗ lenᵣ)) (sym-<> perm) ⟩

           -- 
heapsort : (ns : List ℕ) -> ∃[ ms ] ns <> ms × Ordered ms
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
