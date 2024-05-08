module cs.plfa.part1.Bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

data Magnitude : Set where
  -- track whether a ℕ or a Bin is zero
  Zero : Magnitude
  Positive : Magnitude

data Bin : Magnitude -> Set where
  ⟨⟩  : Bin Zero
  _O : Bin Positive → Bin Positive  -- forbid leading zeros
  _I : ∀ {a : Magnitude} -> Bin a → Bin Positive


------------------- simple opertions on binary and Peano numbers

inc : ∀ {a : Magnitude} -> Bin a → Bin Positive
  -- increment a binary number
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

  -- test case
_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl


double : ℕ → ℕ
double 0 = 0
double (suc n) = suc (suc (double n))

  -- test case
_ : double 3 ≡ 6
_ = refl


--------------------------------- conversions --------------

-- needed to give a type for "ℕ to Bin" conversion
ℕ-magnitude : ℕ -> Magnitude
ℕ-magnitude zero = Zero
ℕ-magnitude (suc _) = Positive

to : ∀ (n : ℕ) → Bin (ℕ-magnitude n)
to 0 = ⟨⟩
to (suc n) = inc (to n)

from : ∀ {m : Magnitude} -> Bin m → ℕ
from ⟨⟩ = 0
from (b I) = suc (double (from b))
from (b O) = double (from b)

  -- Issue: I'd like not to pollute `from` by making it return evidence
  -- that the ℕ-magnitude of its result is equal to `m`.  But without
  -- something like that, I can't seem to write the type of one of my
  -- inverse laws.

--------------------------------- inverses --------------

suc-inc-lemma : ∀ {m : Magnitude} -> ∀ (b : Bin m) → from (inc b) ≡ suc (from b)
suc-inc-lemma ⟨⟩ = refl
suc-inc-lemma (b O) = refl
suc-inc-lemma (b I) = 
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    double (from (inc b))
  ≡⟨ cong double (suc-inc-lemma b)  ⟩ 
    double (suc (from b))
  ≡⟨⟩
    suc (suc (double (from b)))
  ≡⟨⟩
    suc (from (b I))
  ∎


from-to-law : ∀ (n : ℕ) → from (to n) ≡ n
from-to-law zero =
  refl
from-to-law (suc m) =
  begin
    from (to (suc m))  
  ≡⟨⟩
    from (inc (to m))
  ≡⟨ suc-inc-lemma (to m) ⟩
    suc (from (to m))
  ≡⟨ cong suc (from-to-law m) ⟩
    suc m
  ∎

----- other direction


double-mag-lemma : ∀ (n : ℕ) -> ℕ-magnitude (double n) ≡ ℕ-magnitude n
double-mag-lemma zero = refl
double-mag-lemma (suc n) = refl

mag-from-lemma : ∀ {m : Magnitude} -> ∀ (b : Bin m) → ℕ-magnitude (from b) ≡ m
mag-from-lemma ⟨⟩ = refl
mag-from-lemma (b I) = refl
mag-from-lemma {m} (b O) = 
  begin
    ℕ-magnitude (from (b O))
  ≡⟨⟩
    ℕ-magnitude (double (from b))
  ≡⟨ double-mag-lemma (from b) ⟩
    ℕ-magnitude (from b)
  ≡⟨ mag-from-lemma b ⟩
    m
  ∎    

to-from-law : ∀ (m : Magnitude) -> ∀ (b : Bin m) → b ≡ to (from b)
