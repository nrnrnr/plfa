
```
module Naturals-solutions where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
```

This file gives solutions to exercises in plfa.part1.Naturals

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.

```
_ : suc (suc (suc (suc (suc (suc (suc zero)))))) ≡ 7
_ = refl
```

#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.

```
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4 
  ≡⟨⟩
    suc (suc (suc zero)) + suc (suc (suc (suc zero)))  
  ≡⟨⟩
    suc (suc zero) + suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    suc zero + suc (suc (suc (suc (suc (suc zero)))))
  ≡⟨⟩
    zero + suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    7
  ∎
```

#### Exercise `*-example` (practice) {#mult-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.

```
_ : 3 * 4 ≡ 12
_ =
  begin
     3 * 4 
  ≡⟨⟩
     4 + 2 * 4
  ≡⟨⟩
     4 + (4 + 1 * 4)
  ≡⟨⟩
     4 + (4 + (4 + 0 * 4))
  ≡⟨⟩
    12
  ∎
```

#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations:

    m ^ 0        =  1
    m ^ (1 + n)  =  m * (m ^ n)

Check that `3 ^ 4` is `81`.

```
infix 5 _^_

_^_ : ℕ → ℕ → ℕ
m ^ zero        =  1
m ^ (suc n)  =  m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl
```

#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

```
_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    suc (suc (suc (suc (suc zero)))) ∸ suc (suc (suc zero))
  ≡⟨⟩
    suc (suc (suc (suc zero))) ∸ suc (suc zero)
  ≡⟨⟩
    suc (suc (suc zero)) ∸ suc zero
  ≡⟨⟩
    suc (suc zero) ∸ zero
  ≡⟨⟩
    suc (suc zero)
  ≡⟨⟩
    2
  ∎

_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    suc (suc (suc zero)) ∸ suc (suc (suc (suc (suc zero)))) 
  ≡⟨⟩
    suc (suc zero) ∸ suc (suc (suc (suc zero))) 
  ≡⟨⟩
    suc zero ∸ suc (suc (suc zero))
  ≡⟨⟩
    zero ∸ suc (suc zero)
  ≡⟨⟩
    0
  ∎
```


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring:
```
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin
```

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have:

    inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `⟨⟩ O`.
Confirm that these both give the correct answer for zero through four.

```
inc : Bin -> Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ = refl
_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl
_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl
_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl
_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl

to   : ℕ → Bin
to zero    = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ 
from ⟨⟩    = zero
from (b O) = 2 * from b
from (b I) = suc (2 * from b)

_ : to 0 ≡ ⟨⟩ O
_ = refl
_ : to 1 ≡ ⟨⟩ I
_ = refl
_ : to 2 ≡ ⟨⟩ I O
_ = refl
_ : to 3 ≡ ⟨⟩ I I
_ = refl
_ : to 4 ≡ ⟨⟩ I O O
_ = refl

_ : from (⟨⟩ O) ≡ 0 
_ = refl
_ : from (⟨⟩ I) ≡ 1
_ = refl
_ : from (⟨⟩ I O) ≡ 2
_ = refl
_ : from (⟨⟩ I I) ≡ 3
_ = refl
_ : from (⟨⟩ I O O) ≡ 4
_ = refl

```
