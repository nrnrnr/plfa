---
title     : "Lists: Lists and higher-order functions"
permalink : /Lists/
---

```agda
module cs.plfa.part1.Lists where
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

```agda
sum-lemma : ∀ (n : ℕ) (ns : List ℕ) -> sum (n ∷ ns) ≡ n + sum ns
sum-lemma n ns = refl

eqn-n : (n : ℕ) -> Set
eqn-n n = sum (downFrom n) * 2 ≡ n * (n ∸ 1)

open import cs.plfa.part1.Induction using (*-distrib-+)
open import cs.plfa.part1.Relations using (*-comm; *-zero)

*ˡ-distrib-+ : ∀ (m p q : ℕ) -> m * (p + q) ≡ m * p + m * q
*ˡ-distrib-+ m p q = 
  begin 
    m * (p + q)
  ≡⟨ *-comm m (p + q) ⟩
    (p + q) * m
  ≡⟨ *-distrib-+ p q m ⟩
    p * m + q * m
  ≡⟨ cong (_+ (q * m)) (*-comm p m) ⟩
    m * p + q * m
  ≡⟨ cong (m * p +_) (*-comm q m) ⟩
    m * p + m * q
  ∎


sum-down : ∀ (n : ℕ) -> sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-down zero = refl
sum-down (suc n) = 
    begin 
      sum (n ∷ downFrom n) * 2
    ≡⟨⟩
      (n + sum (downFrom n)) * 2
    ≡⟨ *-distrib-+ n (sum (downFrom n)) 2 ⟩
      (n * 2) + sum (downFrom n) * 2
    ≡⟨ cong ((n * 2) +_) (sum-down n) ⟩
      (n * 2) + n * (n ∸ 1)
    ≡⟨ sym (*ˡ-distrib-+ n 2 (n ∸ 1)) ⟩
      n * (2 + (n ∸ 1))
    ≡⟨ lemma1 n ⟩
      n * (suc n)
    ≡⟨ *-comm n (suc n) ⟩
      (suc n) * (suc n ∸ 1)
    ∎
 where lemma1 : ∀ (n : ℕ) -> n * suc (suc (n ∸ 1)) ≡ n * suc n
       lemma1 zero = refl
       lemma1 (suc m) = refl


-- Your code goes here
```

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
All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ {A} {P} xs ys = 
  record { to = to xs ys; from = from xs ys
         ; from∘to = from-to xs ys
         ; to∘from = to-from xs ys
         }
 where equiv = All-++-⇔
       to : ∀ (xs ys : List A) -> (All P (xs ++ ys)) → All P xs × All P ys
       from : ∀ (xs ys : List A) -> All P xs × All P ys -> (All P (xs ++ ys))
       to xs ys = _⇔_.to (equiv xs ys)
       from xs ys = _⇔_.from (equiv xs ys)
       from-to  : ∀ (xs ys : List A) -> (pf : All P (xs ++ ys)) → from xs ys (to xs ys pf) ≡ pf
       to-from : (xs ys : List A) -> (pf : All P xs × All P ys) → to xs ys (from xs ys pf) ≡ pf
       to-from [] ys ⟨ [] , pys ⟩ = refl
       to-from (x ∷ xs) ys ⟨ px ∷ pxs , pys ⟩ =
          begin
            to (x ∷ xs) ys (from (x ∷ xs) ys ⟨ px ∷ pxs , pys ⟩)
          ≡⟨⟩
            to (x ∷ xs) ys (px ∷ from (xs) ys ⟨ pxs , pys ⟩)
          ≡⟨ cong (λ{⟨ f , s ⟩ -> ⟨ px ∷ f , s ⟩}) (to-from xs ys ⟨ pxs , pys ⟩) ⟩ 
            ⟨ px ∷ pxs , pys ⟩
          ∎
       from-to [] ys pf = refl
       from-to (x ∷ xs) ys (pf ∷ pfs) = cong (pf ∷_) (from-to xs ys pfs)
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
¬Any⇔All¬ : ∀ {A : Set} {P : A -> Set} (xs : List A) -> (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs = record { to = to xs; from = from xs } 
  where to : ∀ {A : Set} {P : A -> Set} (xs : List A) -> (¬_ ∘ Any P) xs -> All (¬_ ∘ P) xs
        from : ∀ {A : Set} {P : A -> Set} (xs : List A) -> All (¬_ ∘ P) xs -> (¬_ ∘ Any P) xs
        to [] _ = []
        to (x ∷ xs) pf = (pf ∘ here) ∷ to xs (pf ∘ there)
        from [] [] ()
        from (x ∷ xs) (pf ∷ pfs) = λ{ (here x) → pf x ; (there x₁) → from xs pfs x₁ }

open import Data.Empty using (⊥-elim)

--de-morgan-query : ∀ {A : Set} {P : A -> Set} (xs : List A) -> (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs
--de-morgan-query {A} {P} zs = record { to = to zs; from = from zs } 
--  where to : ∀ {A : Set} {P : A -> Set} (xs : List A) -> (¬_ ∘ All P) xs -> Any (¬_ ∘ P) xs
--        from : ∀ {A : Set} {P : A -> Set} (xs : List A) -> Any (¬_ ∘ P) xs -> (¬_ ∘ All P) xs
--        to [] pf = ⊥-elim (pf [])
--        to {A} {P} (x ∷ xs) pf = here λ x₁ → {!!}
--        from [] ()
--        from (x ∷ xs) (here pf) = λ { (x ∷ x₁) → pf x}
--        from (x ∷ xs) (there pf) = λ{ (x ∷ x₁) → from xs pf x₁}


-- When you have `¬ (All P xs)`, you don't know *which* element of xs
-- falsifies P.  So you have no way to construct the evident for `Any (¬ P) xs`.

```

#### Exercise `¬Any≃All¬` (stretch)

Show that the equivalence `¬Any⇔All¬` can be extended to an isomorphism.
You will need to use extensionality.

```agda
-- Your code goes here
¬Any≃All¬ : ∀ {A : Set} {P : A -> Set} (xs : List A) -> (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any≃All¬ xs = record { to = to xs ; from = from xs ; from∘to = from-to xs ; to∘from = to-from xs }
 where equiv = ¬Any⇔All¬


       to : ∀ {A : Set} {P : A -> Set} (xs : List A) -> (¬_ ∘ Any P) xs -> All (¬_ ∘ P) xs
       from : ∀ {A : Set} {P : A -> Set} (xs : List A) -> All (¬_ ∘ P) xs -> (¬_ ∘ Any P) xs
       to xs = _⇔_.to (equiv xs)
       from xs = _⇔_.from (equiv xs)
       from-to  : ∀ {A : Set} {P : A -> Set} (xs : List A) -> (pf : (¬_ ∘ Any P) xs) → from xs (to xs pf) ≡ pf
       to-from : ∀ {A : Set} {P : A -> Set} (xs : List A) -> (pf : All (¬_ ∘ P) xs) → to xs (from xs pf) ≡ pf

       to-from [] [] = refl
       to-from (x ∷ xs) (pf ∷ pfs) = cong (pf ∷_) (to-from xs pfs)

       extended-from-to : ∀ {A : Set} {P : A -> Set} -> 
                          (xs : List A) (pf : (¬_ ∘ Any P) xs) (pfs : Any P xs) →
                          from xs (to xs pf) pfs ≡ pf pfs
       extended-from-to [] pf ()
       extended-from-to (x ∷ xs) pf (here x₁) = refl
       extended-from-to (x ∷ xs) pf (there pfs) = extended-from-to xs (pf ∘ there) pfs


       from-to xs pf = extensionality (extended-from-to xs pf)
  

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
data Ordered : (List ℕ -> Set) where
  ordered-[] : Ordered []
  ordered-[x] : ∀ {n : ℕ} -> Ordered [ n ]
  ordered-∷ : ∀ {n₁ n₂ : ℕ} {ns : List ℕ} -> n₁ ≤ n₂ -> Ordered (n₂ ∷ ns) 
            -> Ordered (n₁ ∷ n₂ ∷ ns)


open import Data.Nat.Properties using (≤-trans)

Ordered-≤' : ∀ (n : ℕ) (ns : List ℕ) -> Ordered (n ∷ ns) ⇔ (Ordered ns × All (λ y -> n ≤ y) ns)
Ordered-≤' n ns = record { to = to n ns ; from = from n ns }
  where lemma1 : ∀ (n m : ℕ) (xs : List ℕ) -> n ≤ m -> All (_≤_ m) xs -> All (_≤_ n) xs
        lemma1 n m [] n≤m [] = []
        lemma1 n m (y ∷ ys) n≤m (m≤y ∷ pf) = n≤y ∷ lemma1 n m ys n≤m pf
          where n≤y = ≤-trans n≤m m≤y

        to : ∀ (n : ℕ) (ns : List ℕ) -> Ordered (n ∷ ns) -> (Ordered ns × All (λ y -> n ≤ y) ns)
        from : ∀ (n : ℕ) (ns : List ℕ) -> (Ordered ns × All (λ y -> n ≤ y) ns) -> Ordered (n ∷ ns)

        to n [] ordered-[x] = ⟨ ordered-[] , [] ⟩
        to n (m ∷ ms) (ordered-∷ n≤m pf) with to m ms pf
        ... | ⟨ _ , m≤ms ⟩ = ⟨ pf , (n≤m ∷ lemma1 n m ms n≤m m≤ms) ⟩
        from n [] ⟨ O-ns , n≤ns ⟩ = ordered-[x]
        from n [ x ] ⟨ ordered-[x] , n≤x ∷ _ ⟩ = ordered-∷ n≤x ordered-[x]
        from n (x ∷ y ∷ ys) ⟨ ordered-∷ x≤y O-y-ys , n≤x ∷ n≤all ⟩ =
           ordered-∷ n≤x (ordered-∷ x≤y O-y-ys)
        
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
        
data Order (m n : ℕ) : Set where
  less : m ≤ n -> Order  m n
  greater : n ≤ m -> Order  m n

compare : (m n : ℕ) -> Order m n
compare zero n = less z≤n
compare (suc m) zero = greater z≤n
compare (suc m) (suc n) with compare m n
... | less x = less (s≤s x)
... | greater x = greater (s≤s x)


open import Data.Product using (Σ-syntax)
--open import cs.plfa.part1.Decidable using (yes; no; _≤?_; ¬s≤z; ¬s≤s)

----  ¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
----  ¬s≤z ()
----  
----  ¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
----  ¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n
----  
----  _≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
----  zero  ≤? n                   =  yes z≤n
----  suc m ≤? zero                =  no ¬s≤z
----  suc m ≤? suc n with m ≤? n
----  ...               | yes m≤n  =  yes (s≤s m≤n)
----  ...               | no ¬m≤n  =  no (¬s≤s ¬m≤n)
----  
----  

extract : ∀ {A : Set} {xs ys zs : List A} -> merge xs ys zs -> List A
extract [] = []
extract (left-∷ {x} m) = x ∷ extract m
extract (right-∷ {y} m) = y ∷ extract m

extract-≡ : ∀ {A : Set} {xs ys zs : List A} -> (m : merge xs ys zs) -> extract m ≡ zs
extract-≡ [] = refl
extract-≡ (left-∷ {x} m) = cong (x ∷_) (extract-≡ m)
extract-≡ (right-∷ {y} m) = cong (y ∷_) (extract-≡ m)

mergex : (xs ys : List ℕ) -> List ℕ
mergex [] ys = ys
mergex xs [] = xs
mergex (x ∷ xs) (y ∷ ys) with compare x y | mergex xs (y ∷ ys) | mergex (x ∷ xs) ys
...     | less _ | zs | _ = x ∷ zs
...     | greater _ | _ | zs = y ∷ zs



data _implies_ {A : Set} : (P Q : A -> Set) -> Set where
  implication : ∀ {P Q : A → Set}
    → (∀ (x : A) → P x -> Q x)
      -----------------------
    → P implies Q


all-implies : ∀ {A : Set} (P Q : A -> Set) -> (P implies Q) ->
              ∀ {xs : List A} -> All P xs -> All Q xs
all-implies P Q implies [] = []
all-implies P Q (implication P->Q) {x ∷ xs} (Px ∷ pf) = P->Q x Px ∷ all-implies P Q (implication P->Q) pf

any-bigger : ∀ {A : Set} {x : A} {xs : List A} (P : A -> Set) -> 
             Any P xs -> Any P (x ∷ xs)
any-bigger P pf = there pf 


all-any-bigger-lemma : ∀ {A : Set} {x : A} {xs zs : List A}
           -> All (λ section → Any (_≡_ section) zs) xs
           -> All (λ section → Any (_≡_ section) (x ∷ zs)) xs
all-any-bigger-lemma [] = []
all-any-bigger-lemma {A} {x} {xs} {zs} (x∈zs ∷ pfs) =
           (there x∈zs) ∷ all-implies P Q (implication (λ v → any-bigger (_≡_ v))) pfs
  where P : A -> Set
        Q : A -> Set
        P section = Any (_≡_ section) zs
        Q section = Any (_≡_ section) (x ∷ zs)


merge-keep-xs : ∀ {A : Set} {xs ys zs : List A} -> merge xs ys zs -> All (_∈ zs) xs
merge-keep-ys : ∀ {A : Set} {xs ys zs : List A} -> merge xs ys zs -> All (_∈ zs) ys
merge-only-xs-ys : ∀ {A : Set} {xs ys zs : List A} -> merge xs ys zs ->
                    All (λ z -> z ∈ xs ⊎ z ∈ ys) zs

merge-keep-xs [] = []
merge-keep-xs (left-∷ pf) = here refl ∷ merge-keep-xs (right-∷ pf)
merge-keep-xs {A} (right-∷ {x} {xs} {ys} {zs} pf) with merge-keep-xs pf
... | thing = all-any-bigger-lemma thing
  where Q = λ v -> Any (_≡_ v) (x ∷ zs)
        P : A -> Set
        P = λ v -> Any (_≡_ v) (zs)
-- Goal: All (λ section → Any (_≡_ section) (x ∷ zs)) xs

merge-keep-ys [] = []
merge-keep-ys {A} (left-∷ {x} {xs} {ys} {zs} pf) = all-any-bigger-lemma (merge-keep-ys pf)
merge-keep-ys (right-∷ pf) = (here refl) ∷ (merge-keep-ys (left-∷ pf))

merge-only-xs-ys [] = []
merge-only-xs-ys (left-∷ {x} {xs} {ys} {zs} pf) =
     inj₁ (here refl) ∷ all-implies P Q (implication P->Q) (merge-only-xs-ys pf)
  where Q = λ z → Any (_≡_ z) (x ∷ xs) ⊎ Any (_≡_ z) ys
        P = λ z → Any (_≡_ z) xs ⊎ Any (_≡_ z) ys

        P->Q : ∀ {A : Set} {x : A} {xs ys : List A} (z : A) ->
                 Any (_≡_ z) xs ⊎ Any (_≡_ z) ys -> 
                 Any (_≡_ z) (x ∷ xs) ⊎ Any (_≡_ z) ys
        P->Q z (inj₁ z∈xs) = inj₁ (there z∈xs)
        P->Q z (inj₂ z∈ys) = inj₂ z∈ys

merge-only-xs-ys (right-∷ {y} {xs} {ys} {zs} pf) =
     inj₂ (here refl) ∷ all-implies P Q (implication P->Q) (merge-only-xs-ys pf)
  where Q = λ z → Any (_≡_ z) xs ⊎ Any (_≡_ z) (y ∷ ys)
        P = λ z → Any (_≡_ z) xs ⊎ Any (_≡_ z) ys

        P->Q : ∀ {A : Set} {y : A} {ys xs : List A} (z : A) ->
               Any (_≡_ z) xs ⊎ Any (_≡_ z) ys ->
               Any (_≡_ z) xs ⊎ Any (_≡_ z) (y ∷ ys)

        P->Q z (inj₁ z∈xs) = inj₁ z∈xs
        P->Q z (inj₂ z∈ys) = inj₂ (there z∈ys)


merge-keep : ∀ {A : Set} {xs ys zs : List A} -> merge xs ys zs 
           -> All (_∈ zs) xs × All (_∈ zs) ys × All (λ z -> z ∈ xs ⊎ z ∈ ys) zs
merge-keep m = ⟨ (merge-keep-xs m) , ⟨ (merge-keep-ys m) , (merge-only-xs-ys m) ⟩ ⟩

merge-keep-xs' : ∀ {A : Set} {xs ys zs : List A} -> merge xs ys zs -> 
                 ∀ (x : A) -> (x ∈ xs -> x ∈ zs)
merge-only-xs-ys' : ∀ {A : Set} {xs ys zs : List A} -> merge xs ys zs ->
                 ∀ (z : A) -> (z ∈ zs -> z ∈ xs ⊎ z ∈ ys)

--merge-keep-ys : ∀ {A : Set} {xs ys zs : List A} -> merge xs ys zs -> All (_∈ zs) ys

merge-keep-xs' (left-∷ merged) x (here ≡x) = here ≡x
merge-keep-xs' (left-∷ merged) x (there x∈xs) = there (merge-keep-xs' merged x x∈xs)
merge-keep-xs' (right-∷ merged) x x∈xs = there (merge-keep-xs' merged x x∈xs)

merge-only-xs-ys' (left-∷ merged) z (here z≡x) = inj₁ (here z≡x)
merge-only-xs-ys' (left-∷ merged) z (there z∈zs) with merge-only-xs-ys' merged z z∈zs
... | inj₁ z∈xs = inj₁ (there z∈xs)
... | inj₂ z∈ys = inj₂ z∈ys
merge-only-xs-ys' (right-∷ merged) z (here z≡y) = inj₂ (here z≡y )
merge-only-xs-ys' (right-∷ merged) z (there z∈zs) with merge-only-xs-ys' merged z z∈zs
... | inj₁ z∈xs = inj₁ z∈xs
... | inj₂ z∈ys = inj₂ (there z∈ys)



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

_ : [ 1 , 2 ] ⋈ [ 2 , 1 ]
_ = permutation (there-left (here (there-right (here []))))

_ : [ 1 , 2 , 3 ] ⋈ [ 3 , 1 , 2 ]
_ = permutation (there-left (here (here (there-right (here [])))))

self-permutation : ∀ {A : Set} (xs : List A) -> xs ⋈ xs
self-permutation [] = permutation []
self-permutation (x ∷ xs) with self-permutation xs
... | permutation pxs = permutation (here pxs)

self-permutation++ : ∀ {A : Set} {xs : List A} -> Permutation++ xs [] xs
self-permutation++ {A} {[]} = []
self-permutation++ {A} {x ∷ xs} = here self-permutation++

shunt-self-permutation++ : ∀ {A : Set} {xs ys : List A} -> Permutation++ (shunt xs ys) xs ys
shunt-self-permutation++ {A} {[]} {ys} = self-permutation++
shunt-self-permutation++ {A} {x ∷ xs} {ys} = there-right shunt-self-permutation++

perm-shunt : ∀ {A : Set} (xs ys zs : List A)
           -> Permutation++ xs ys zs -> Permutation++ xs [] (shunt ys zs)
perm-shunt xs [] zs pf = pf
perm-shunt xs (x ∷ ys) zs pf = perm-shunt xs ys (x ∷ zs) (there-left pf)

perm-shunt' : ∀ {A : Set} {xs ys zs : List A}
           -> Permutation++ xs ys zs -> Permutation++ xs [] (shunt ys zs)
perm-shunt' {A} {xs} {[]} {zs} pf = pf
perm-shunt' {A} {xs} {(x ∷ ys)} {zs} pf = perm-shunt' {A} {xs} {ys} {(x ∷ zs)} (there-left pf)

shunt-perm : ∀ {A : Set} (xs ys zs : List A)
           -> Permutation++ xs [] (shunt ys zs)
           -> Permutation++ xs ys zs
shunt-perm xs [] zs pf = pf
shunt-perm xs (y ∷ ys) zs pf = there-right (shunt-perm xs ys (y ∷ zs) pf)

perm-membership : ∀ {A : Set} {xs ys zs : List A}
                -> Permutation++ zs xs ys
                -> ∀ {x : A} -> (x ∈ zs) ⇔ (x ∈ xs ⊎ x ∈ ys)
perm-membership pf = record { to = to pf ; from = {!!} }
  where to : ∀ {A : Set } {x : A} {xs ys zs : List A} -> Permutation++ zs xs ys -> (x ∈ zs) -> (x ∈ xs ⊎ x ∈ ys)
        from : ∀ {A : Set} {x : A} {xs ys zs : List A} -> Permutation++ zs xs ys -> (x ∈ xs ⊎ x ∈ ys) -> (x ∈ zs)
        to (there-left perm) pf with to perm pf
        ... | inj₁ (here refl) = inj₂ (here refl)
        ... | inj₁ (there x) = inj₁ x
        ... | inj₂ x∈zs = inj₂ (there x∈zs)
        to (there-right perm) pf with to perm pf
        ... | inj₁ (here refl) = inj₁ (there (here refl))
        ... | inj₁ (there x∈xs) = inj₁ (there (there x∈xs))
        ... | inj₂ (here x≡y) = inj₁ (here x≡y)
        ... | inj₂ (there x∈ys) = inj₂ x∈ys
        to (here perm) (here x≡z) = inj₂ (here x≡z)
        to (here perm) (there x∈zs) with to perm x∈zs
        ... | inj₁ x∈xs = inj₁ x∈xs
        ... | inj₂ x∈ys = inj₂ (there x∈ys)

        from prem pf = {!!}

placementx : ∀ {A : Set} (xs yls yrs : List A) (x : A)
          -> Permutation++ xs yls yrs
          -> Permutation++ (x ∷ xs) yls (x ∷ yrs)
placementx xs yls yrs x pf = here pf

self-reverse-permutation++ : ∀ {A : Set} {xs : List A} -> Permutation++ xs xs []
self-reverse-permutation++ {A} {[]} = []
self-reverse-permutation++ {A} {x ∷ xs} = there-right (here (self-reverse-permutation++))

--placement++ : ∀ {A : Set} (xs ls rs : List A) (x : A)
--> Permutation++ xs ls rs -> Permutation++ (x ∷ xs) ls (x ∷ rs)




placement : ∀ {A : Set} (x : A) (xs ys : List A) 
          -> (x ∷ shunt xs ys) ⋈ (shunt xs (x ∷ ys))
placement x xs ys =
  permutation (perm-shunt (x ∷ shunt xs ys) xs (x ∷ ys) (here shunt-self-permutation++))


reverse-perm : ∀ {A : Set} (xs : List A) -> xs ⋈ reverse′ xs
reverse-perm [] = permutation []
reverse-perm (x ∷ xs) =
  permutation (perm-shunt (x ∷ xs) xs [ x ] (here (self-reverse-permutation++)))

module M where

  merge-perm++ : ∀ {A : Set} {xs ys zs : List A}
               -> merge xs ys zs -> Permutation++ zs xs ys
  merge-perm++ [] = []
  merge-perm++ (left-∷ pf) = there-right (here (merge-perm++ pf))
  merge-perm++ (right-∷ pf) = here (merge-perm++ pf)

  merge-perm : ∀ {A : Set} {xs ys zs : List A} -> merge xs ys zs -> _⋈_ zs (shunt xs ys)
  merge-perm {A} {xs} {ys} {zs} pf = permutation (perm-shunt zs xs ys (merge-perm++ pf))

  --merge-extract : ∀ {A : Set} -> ∀ {xs ys zs : List A} -> (merge xs ys zs) -> zs
  --merge-extract : ∀ {xs ys zs : List ℕ} -> (merge xs ys zs) -> zs
  --   List ℕ should be a sort, but it isn't
  --   when checking that the expression zs has type _1874merge-result thing = ?
  --merge-extract [] = []
  --merge-extract (left-∷ {x} {xs} {ys} {zs} m) = x ∷ merge-extract m
  --merge-extract (right-∷ {x} {xs} {ys} {zs} m) = x ∷ merge-extract m



  ordered-tail : ∀ {x : ℕ} {xs : List ℕ} -> Ordered (x ∷ xs) -> Ordered xs
  ordered-tail ordered-[x] = ordered-[]
  ordered-tail (ordered-∷ x ordered-[x]) = ordered-[x]
  ordered-tail (ordered-∷ x (ordered-∷ x₁ pf)) = ordered-∷ x₁ pf

  _ : Ordered [ 1 , 2 , 3 , 4 ]
  _ = ordered-∷ (s≤s z≤n) (ordered-∷ (s≤s (s≤s z≤n)) (ordered-∷ (s≤s (s≤s (s≤s z≤n))) ordered-[x]))

  data HeadMin : ∀ (xs ys zs : List ℕ) -> Set where
    -- the head of zs, if present, is at most the minimum of the heads of xs and ys
    head-min-left-[]  : ∀ {ys : List ℕ} -> Ordered ys -> HeadMin [] ys ys
    head-min-right-[] : ∀ {xs : List ℕ} -> Ordered xs -> HeadMin xs [] xs
    head-min-≤ : ∀ {x y : ℕ} {xs ys zs : List ℕ} -> 
                    x ≤ y -> HeadMin xs (y ∷ ys) zs -> HeadMin (x ∷ xs) (y ∷ ys) (x ∷ zs)
    head-min-> : ∀ {x y : ℕ} {xs ys zs : List ℕ} -> 
                    y ≤ x -> HeadMin (x ∷ xs) ys zs -> HeadMin (x ∷ xs) (y ∷ ys) (y ∷ zs)



  merge≤ : ∀ (xs ys : List ℕ) -> ∃[ zs ] (merge xs ys zs)
  merge≤ [] [] = ⟨ [] , [] ⟩
  merge≤ (x ∷ xs) [] with merge≤ xs [] 
  ... | ⟨ zs , merge ⟩ = ⟨ (x ∷ zs) , (left-∷ merge) ⟩
  merge≤ [] (y ∷ ys) with merge≤ [] ys
  ... | ⟨ zs , merge ⟩ = ⟨ (y ∷ zs) , (right-∷ merge) ⟩
  merge≤ (x ∷ xs) (y ∷ ys) with compare x y | merge≤ xs (y ∷ ys) | merge≤ (x ∷ xs) ys
  ... | less _ | ⟨ zs , merge ⟩ | _ = ⟨ x ∷ zs , left-∷ merge ⟩
  ... | greater _ | _ | ⟨ zs , merge ⟩ = ⟨ (y ∷ zs) , (right-∷ merge) ⟩



  --merge-sorted : ∀ (xs ys : List ℕ) (oxs : Ordered xs) (oys : Ordered ys) ->
  --               Ordered (Data.Product.Σ.proj₁ (merge≤ xs ys))
  --merge-sorted xs ys oxs oys with merge≤ xs ys
  --merge-sorted xs ys oxs oys | ⟨ [] , [] ⟩ = ordered-[]
  --merge-sorted xs ys oxs oys | ⟨ (z ∷ zs) , left-∷ {x} {xs'} {ys'} {zs'} merged ⟩ with merge-sorted xs' ys (ordered-tail oxs) oys
  --merge-sorted (x ∷ _) ys oxs oys | ⟨ [ x ] , left-∷ merged ⟩ | _ = ordered-[x]
  --merge-sorted (x ∷ _) ys oxs oys | ⟨ x ∷ z ∷ zs , left-∷ {x} {xs} {ys} {z ∷ zs} merged ⟩ | thing = ordered-∷ {!!} {!!}
  ----   where small : 
  --merge-sorted xs ys oxs oys | ⟨ (z ∷ zs) , right-∷ merged ⟩ = {!!}

  merge-right-id : ∀ {A : Set} {ys zs : List A} -> merge [] ys zs -> merge [] ys ys
  merge-right-id [] = []
  merge-right-id (right-∷ pf) = right-∷ (merge-right-id pf)

  merge-right-≡ : ∀ {A : Set} {ys zs : List A} -> merge [] ys zs -> ys ≡ zs
  merge-right-≡ [] = refl
  merge-right-≡ (right-∷ pf) rewrite (merge-right-≡ pf) = refl

  merge-left-≡ : ∀ {A : Set} {xs zs : List A} -> merge xs [] zs -> xs ≡ zs
  merge-left-≡ [] = refl
  merge-left-≡ (left-∷ pf) rewrite (merge-left-≡ pf) = refl

  cong-Ordered : ∀ {xs ys : List ℕ} -> (xs ≡ ys) -> (Ordered xs) -> Ordered ys
  cong-Ordered {.[]} {[]} xs≡ys ordered-[] = ordered-[]
  cong-Ordered {.([ _ ])} {[ x ]} xs≡ys ordered-[x] = ordered-[x]
  cong-Ordered {(x ∷ x' ∷ xs)} {y ∷ y' ∷ ys} refl (ordered-∷ x≤y pf) = ordered-∷ x≤y pf

  --conjecture:  ∀ (xs ys : List ℕ) (x y : ℕ) (x≤y : x ≤ y) -> merge≤ (x ∷ xs) (y ∷ ys)

  --merge-sorted : ∀ (xs ys : List ℕ) (oxs : Ordered xs) (oys : Ordered ys) ->
  --               Ordered (Data.Product.Σ.proj₁ (merge≤ xs ys))
  --merge-sorted xs ys oxs oys with merge≤ xs ys
  --merge-sorted [] [] oxs oys | ⟨ [] , [] ⟩ = ordered-[]
  --merge-sorted [] (y ∷ ys) oxs oys | ⟨ y ∷ ys' , right-∷ snd ⟩ = cong-Ordered (merge-right-≡ (right-∷ snd)) oys
  --  merge-sorted [] ys oxs oys | ⟨ ys' , merged ⟩ = cong-Ordered (merge-right-≡ merged) oys
  --  merge-sorted xs [] oxs oys | ⟨ _ , merged ⟩ = cong-Ordered (merge-left-≡ merged) oxs
  --  merge-sorted (x ∷ xs) (y ∷ ys) oxs oys | thing with compare x y
  --  merge-sorted (x ∷ xs) (y ∷ ys) oxs oys | ⟨ (x ∷ zs) , left-∷ snd ⟩ | less x≤y = {!!}
  --     where x-smallest : ∀ {z : ℕ} -> (z ∈ zs) -> x ≤ z
  --           x-smallest = {!!}
  --           ordered-zs : Ordered zs
  --           result : Data.Product.Σ.proj₁ (merge≤ xs (y ∷ ys)) ≡ zs
  --           result = {!!}
  --           ordered-zs with merge-sorted xs (y ∷ ys) (ordered-tail oxs) oys
  --           ... | thing = cong-Ordered result thing
  --  merge-sorted (x ∷ xs) (y ∷ ys) oxs oys | ⟨ (y ∷ zs) , right-∷ snd ⟩ | less x≤y = {!!}
  --  merge-sorted (x ∷ xs) (y ∷ ys) oxs oys | thing | greater x₁ = {!!} 



  --_ : HeadMin [ 1 , 3 ] [ 2 , 4 ] [ 1 , 2 , 3 , 4 ]
  --_ = head-min-≤ (s≤s z≤n) (head-min-> (s≤s (s≤s z≤n)) (head-min-≤ (s≤s (s≤s (s≤s z≤n))) head-min-left-[]))

  ----  conjecture : ∀ {xs ys zs : List ℕ} -> HeadMin xs ys zs -> Ordered zs
  ----  conjecture (head-min-left-[] pf) = pf
  ----  conjecture (head-min-right-[] pf) = pf
  ----  conjecture (head-min-≤ x (head-min-left-[] x₁)) = ordered-∷ x x₁
  ----  conjecture (head-min-≤ {x} {y} x≤y (head-min-≤ {y'} {z} thing pf)) = ordered-∷ {!!} {!!}
  ----  conjecture (head-min-≤ x (head-min-> y pf)) = {!!}
  ----  conjecture (head-min-> x pf) = {!!}
  ----  
  ----  
  ----  merge-ordered : (xs ys : List ℕ) -> Ordered xs -> Ordered ys -> Σ[ zs ∈ List ℕ ] (Ordered zs)
  ----  merge-ordered [] ys oxs oys = ⟨ ys , oys ⟩
  ----  merge-ordered xs [] oxs oys = ⟨ xs , oxs ⟩
  ----  merge-ordered (x ∷ xs) (y ∷ ys) oxs oys 
  ----    with x ≤? y 
  ----       | merge-ordered xs (y ∷ ys) (ordered-tail oxs) oys 
  ----       | merge-ordered (x ∷ xs) ys oxs (ordered-tail oys)
  ----  ... | yes x≤y | ⟨ zs , ozs ⟩ | _ = ⟨ (x ∷ zs) , {!ordered-∷ ? ?!} ⟩
  ----  ... | no  x>y | _ | thing = {!!}
```

## merge sort with proof

```agda
data merged≤ : (xs ys zs : List ℕ) → Set where

  [] :
      --------------
      merged≤ [] [] []

  left-∷-[] : ∀ {x xs zs}
    → merged≤ xs [] zs
      --------------------------
    → merged≤ (x ∷ xs) [] (x ∷ zs)

  left-∷-∷ : ∀ {x y xs ys zs}
    → x ≤ y
    → merged≤ xs (y ∷ ys) zs
      --------------------------
    → merged≤ (x ∷ xs) (y ∷ ys) (x ∷ zs)

  right-[]-∷ : ∀ {y ys zs}
    → merged≤ [] ys zs
      --------------------------
    → merged≤ [] (y ∷ ys) (y ∷ zs)

  right-∷-∷ : ∀ {x y xs ys zs}
    → y ≤ x
    → merged≤ (x ∷ xs) ys zs
      --------------------------
    → merged≤ (x ∷ xs) (y ∷ ys) (y ∷ zs)


merge≤ : ∀ (xs ys : List ℕ) -> ∃[ zs ] (merged≤ xs ys zs)
merge≤ [] [] = ⟨ [] , [] ⟩
merge≤ (x ∷ xs) [] with merge≤ xs [] 
... | ⟨ zs , merge ⟩ = ⟨ (x ∷ zs) , (left-∷-[] merge) ⟩
merge≤ [] (y ∷ ys) with merge≤ [] ys
... | ⟨ zs , merge ⟩ = ⟨ (y ∷ zs) , (right-[]-∷ merge) ⟩
merge≤ (x ∷ xs) (y ∷ ys) with compare x y | merge≤ xs (y ∷ ys) | merge≤ (x ∷ xs) ys
... | less x≤y | ⟨ zs , m ⟩ | _ = ⟨ x ∷ zs , left-∷-∷ x≤y m ⟩
... | greater y≤x | _ | ⟨ zs , m ⟩ = ⟨ (y ∷ zs) , right-∷-∷ y≤x m ⟩


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



merge-ordered : ∀ {xs ys zs : List ℕ} -> Ordered xs -> Ordered ys -> merged≤ xs ys zs
              -> Ordered zs
merge-ordered oxs oys [] = ordered-[]
merge-ordered oxs oys (left-∷-[] {x} {xs} {zs} m) = 
                                        _⇔_.from (Ordered-≤ x zs) ⟨ ozs , x≤zs ⟩
  where ozs : Ordered zs
        xs≡zs : xs ≡ zs
        x≤zs : ∀ (y : ℕ) -> y ∈ zs -> x ≤ y
        x≤xs : ∀ (y : ℕ) -> y ∈ xs -> x ≤ y

        xs≡zs = merged≤-left-≡ m
        ozs = M.cong-Ordered (xs≡zs) (M.ordered-tail oxs)
        x≤xs = Data.Product.Σ.proj₂ (_⇔_.to (Ordered-≤ x xs) oxs)
        x≤zs y y∈zs = x≤xs y (cong-∈ (sym xs≡zs) y∈zs)

        
merge-ordered oxs oys (left-∷-∷ {x} {y} {xs} {ys} {zs} x≤y m) = 
                                        _⇔_.from (Ordered-≤ x zs) ⟨ ozs , x≤zs ⟩
  where ozs : Ordered zs
        x≤zs : ∀ (y : ℕ) -> y ∈ zs -> x ≤ y
        x≤xs : ∀ (y : ℕ) -> y ∈ xs -> x ≤ y
        ozs = merge-ordered (M.ordered-tail oxs) oys m
        x≤xs = Data.Product.Σ.proj₂ (_⇔_.to (Ordered-≤ x xs) oxs)
        y≤ys = Data.Product.Σ.proj₂ (_⇔_.to (Ordered-≤ y ys) oys)
        x≤zs v v∈zs with merged-only-xs-ys m v v∈zs 
        ... | inj₁ v∈xs = x≤xs v v∈xs
        ... | inj₂ (here refl) = x≤y
        ... | inj₂ (there v∈ys) = ≤-trans x≤y (y≤ys v v∈ys)

merge-ordered oxs oys (right-[]-∷ m) = {!!}
merge-ordered oxs oys (right-∷-∷ x m) = {!!}

data Split {A : Set} : (xs ys zs : List A) -> Set where
  [] : Split [] [] []
  swap-∷ : ∀ {x xs ys zs} -> Split xs ys zs -> Split (x ∷ ys) xs (x ∷ zs)

spl : ∀ {A : Set} (zs : List A) -> ∃[ xs ] ∃[ ys ] Split xs ys zs
spl [] = ⟨ [] , ⟨ [] , [] ⟩ ⟩
spl (z ∷ zs) with spl zs
... | ⟨ xs , ⟨ ys , split ⟩ ⟩ = ⟨ z ∷ ys , ⟨ xs , (swap-∷ split) ⟩ ⟩


data STree {A : Set} : (zs : List A) -> Set where
  [] : STree []
  [x] : ∀ (x : A) -> STree ([ x ])
  fork : ∀ {xs ys ns : List A} -> STree xs -> STree ys -> Permutation++ ns xs ys -> STree ns

--tree : ∀ {A : Set} (zs : List A) -> STree zs
--tree [] = []
--tree [ x ] = [x]
--tree (z1 ∷ z2 ∷ zs) with spl (z1 ∷ z2 ∷ zs)
--... | ⟨ xs , ⟨ ys , snd ⟩ ⟩ = fork (tree xs) (tree ys) snd 

pswap : ∀ {A : Set} {xs ys zs : List A} -> Permutation++ xs ys zs -> Permutation++ xs zs ys
pswap [] = []
pswap (here p) = there-right (here (pswap p))
pswap (there-left p) = there-right (pswap p)
pswap (there-right p) = there-left (pswap p)

tree-∷ : ∀ {A : Set} -> (x : A) -> {ns : List A} -> (STree ns) -> STree (x ∷ ns)
tree-∷ x [] = [x] x
tree-∷ x ([x] y) = fork ([x] x) ([x] y) (there-right (here (here [])))
tree-∷ x (fork xs ys p) = fork (tree-∷ x ys) xs (pswap (here p))

tree-of-list : ∀ {A : Set} -> (xs : List A) -> STree xs
tree-of-list [] = []
tree-of-list (x ∷ xs) = tree-∷ x (tree-of-list xs)

data _Sorted : List ℕ -> Set where
  sorted-as : ∀ {zs : List ℕ} -> ∀ (ns : List ℕ) -> Ordered ns -> ns ⋈ zs -> zs Sorted


merge-erase : ∀ {xs ys zs : List ℕ} -> merged≤ xs ys zs -> merge xs ys zs
merge-erase [] = []
merge-erase (left-∷-[] pf) = left-∷ (merge-erase pf)
merge-erase (left-∷-∷ x pf) = left-∷ (merge-erase pf)
merge-erase (right-[]-∷ pf) = right-∷ (merge-erase pf)
merge-erase (right-∷-∷ x pf) = right-∷ (merge-erase pf)

empty-perm-left' : ∀ {A : Set} (y : A) (ys zs : List A) -> ¬ (Permutation++ [] (y ∷ ys) zs)
empty-perm-right' : ∀ {A : Set} (y : A) (ys zs : List A) -> ¬ (Permutation++ [] zs (y ∷ ys))

empty-perm-left' y ys (z ∷ zs) (there-left pf) = empty-perm-left' z (y ∷ ys) zs pf
empty-perm-left' y ys (zs) (there-right pf) = empty-perm-right' y zs ys pf
empty-perm-right' y ys zs (there-left pf) = empty-perm-left' y zs ys pf
empty-perm-right' y ys (z ∷ zs) (there-right pf) = empty-perm-right' z (y ∷ ys) zs pf

empty-perm-left : ∀ {A : Set} {y : A} {ys zs : List A} -> ¬ (Permutation++ [] (y ∷ ys) zs)
empty-perm-left {A} {y} {ys} {zs} = empty-perm-left' y ys zs


--perm-lemma-5 : ∀ {A : Set} {xs ys zs xs' : List A}
--             -> Permutation++ xs ⋈ xs'
--             -> zs ⋈ (shunt xs ys)
--             -> zs ⋈ (shunt xs' ys)

perm-find-z : ∀ {A : Set} {xs ys zs : List A} (z : A)
          -> Permutation++ (z ∷ zs) xs ys
          -> ∃[ xs' ] ∃[ ys' ] Permutation++ zs xs' ys'
perm-find-z _ (here {zs} {xs} {ys} {x} pf) = ⟨ xs , ⟨ ys , pf ⟩ ⟩
perm-find-z z (there-left pf) = perm-find-z z pf
perm-find-z z (there-right pf) = perm-find-z z pf


perm-cons : ∀ {A : Set} {z : A} {xs ys : List A}
          -> xs ⋈ ys -> (z ∷ xs) ⋈ (z ∷ ys)
perm-cons (permutation x) = permutation (here x)



perm-find-x : ∀ {A : Set} {xs ys zs zs' : List A} (x : A)
          -> Permutation++ zs (x ∷ xs) ys
          -> Permutation++ zs' xs ys
perm-find-x x (here {zs} {x ∷ xs} {ys} {z} pf) = there-left {!!}
perm-find-x x (there-left pf) = {!!}
perm-find-x x (there-right pf) = {!!}

perm-swap++ : ∀ {A : Set} {y1 y2 : A} {xs ys zs : List A}
          -> Permutation++ zs xs (y1 ∷ y2 ∷ ys)
          -> Permutation++ zs xs (y2 ∷ y1 ∷ ys)
perm-swap++ (here pf) = there-left (here (there-right pf))
perm-swap++ (there-left (here pf)) = here (there-left pf)
perm-swap++ (there-left (there-left pf)) = {!!}
perm-swap++ (there-left (there-right pf)) = perm-swap++ pf
perm-swap++ (there-right pf) = {!!}


perm-swap : ∀ {A : Set} {y1 y2 : A} {xs ys : List A}
          -> xs ⋈ (y1 ∷ y2 ∷ ys)
          -> xs ⋈ (y2 ∷ y1 ∷ ys)
perm-swap (permutation (here pf)) = permutation (there-left (here (there-right pf)))
perm-swap {ys = []} (permutation (there-left (here pf))) = permutation (here (there-left pf))
perm-swap {ys = []} (permutation (there-left (there-left (there-right pf)))) =
  perm-swap (permutation (there-left pf))
perm-swap {ys = []} (permutation (there-left (there-right pf))) = perm-swap (permutation pf)
perm-swap {ys = z ∷ zs} (permutation (there-left {xs} {[]} {(z1 ∷ z2 ∷ zs)} {y} pf)) =
   permutation {!!}
--... | thing = permutation {!!}

perm-find : ∀ {A : Set} {as : List A}
          -> ∀ {a : A} -> a ∈ as -> ∃[ as' ] as ⋈ (a ∷ as')
perm-find (here {x} {xs} refl) = ⟨ xs , self-permutation (x ∷ xs)  ⟩
perm-find {A} {as} {a} (there {x} {xs} pf) with perm-find pf
... | ⟨ ys , pys ⟩ = ⟨ (x ∷ ys) , perm-swap (perm-cons pys) ⟩


perm-lemma-4 : ∀ {A : Set} {xs ys zs xs' : List A}
             -> xs ⋈ xs'
             -> zs ⋈ (shunt xs ys)
             -> zs ⋈ (shunt xs' ys)
--perm-lemma-4 xs⋈xs' zs⋈Rxs++ys = {!!}
perm-lemma-4 (permutation xs⋈xs') (permutation zs⋈Rxs++ys) = permutation {!!}

perm-lemma-3 : ∀ {A : Set} {xs ys zs xs' : List A}
             -> xs ⋈ xs'
             -> Permutation++ zs xs ys
             -> Permutation++ zs xs' ys
perm-lemma-3 (permutation []) [] = []
perm-lemma-3 (permutation (there-left pf)) [] = ⊥-elim (empty-perm-left pf)
perm-lemma-3 xs⋈xs' (here zxy) = here (perm-lemma-3 xs⋈xs' zxy)
perm-lemma-3 xs⋈xs' (there-left {xs = yyy} {y = y} zxy) 
  = there-left {!!}
perm-lemma-3 (permutation x) (there-right zxy) = {!!}

perm-lemma-2 : ∀ {xs ys zs xs' ys' zs' : List ℕ}
             -> xs ⋈ xs'
             -> ys ⋈ ys'
             -> Permutation++ zs' xs' ys'
             -> Permutation++ zs xs ys
             -> zs ⋈ zs'
--perm-lemma-2 xs⋈xs' ys⋈ys' zxy' zxy = {!!}
perm-lemma-2 xs⋈xs' ys⋈ys' zxy' zxy = {!!}             


perm-lemma-1 : ∀ {xs ys zs xs' ys' zs' : List ℕ}
             -> xs ⋈ xs'
             -> ys ⋈ ys'
             -> Permutation++ zs' xs' ys'
             -> merged≤ xs ys zs
             -> zs ⋈ zs'
perm-lemma-1  = {!!}

mergesort : ∀ (ns : List ℕ) -> ns Sorted
mergesort ns = sort (tree-of-list ns)
  where sort : ∀ {ns : List ℕ} -> STree ns -> ns Sorted
        sort [] = sorted-as [] ordered-[] (permutation [])
        sort ([x] x) = sorted-as [ x ] ordered-[x] (permutation (here []))
        sort (fork left right perm) with sort left | sort right
        ... | sorted-as xs oxs pxs | sorted-as ys oys pys with merge≤ xs ys
        ... | ⟨ zs , merged ⟩ =
             sorted-as zs (merge-ordered oxs oys merged)
             (perm-lemma-1 pxs pys perm merged)


--        go (split-start []) = ⟨ [] , ⟨ ordered-[] , (permutation []) ⟩ ⟩
--        go (split-start [ x ]) = ⟨ [ x ] , ⟨ ordered-[x] , (permutation (here [])) ⟩ ⟩
--        go (split-start (x ∷ y ∷ ms)) = {!go (split-consume {x} (split-start {[x]} {[y]} {ms}})!}
--        go (split-consume pf) = {!!}

--        go [] [] [ n ] = ⟨ [ n ] , ⟨ ordered-[x] , (permutation (here [])) ⟩ ⟩
--        go lefts rights [] with go [] [] lefts | go [] [] rights
--        ... | ⟨ lefts' , pl ⟩ | ⟨ rights' , pr ⟩ = {!!}
--        go lefts rights (x ∷ xs) with go (x ∷ rights) lefts xs
--        ... | ⟨ ms , pms ⟩ = {!!}




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
