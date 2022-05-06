module Ordering where 

open import Level        renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl; sym; trans; cong)
open import Data.Sum     using (_⊎_)
open import Relation.Nullary     using (¬_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-trans; ≤-total)

-- Non-strict partial order relation on a set A
-- Note: all of this could have been imported from the standard library...
-- https://agda.github.io/agda-stdlib/Relation.Binary.Bundles.html#6007
-- https://agda.github.io/agda-stdlib/Relation.Binary.Definitions.html
record PartialOrdering {l : Level} : Set (lsuc l) where 
  field
    P : Set l
    -- order relation
    _≤ᵖ_ : P → P → Set
    -- reflexivity
    ≤ᵖ-refl : {p : P} → p ≤ᵖ p
    -- antisymmetry
    ≤ᵖ-antisym : {p₁ p₂ : P} → p₁ ≤ᵖ p₂ → p₂ ≤ᵖ p₁ → p₁ ≡ p₂ 
    -- transitivity
    ≤ᵖ-trans : {p₁ p₂ p₃ : P} → p₁ ≤ᵖ p₂ → p₂ ≤ᵖ p₃ → p₁ ≤ᵖ p₃

-- Non-strict total ordering
record TotalOrdering {l : Level} : Set (lsuc l) where   
  field
    PartialOrd : PartialOrdering {l}
  open PartialOrdering PartialOrd public
  field 
    -- strongly connected (total): either one or the other must be true
    ≤ᵖ-total : (p₁ p₂ : P) → (p₁ ≤ᵖ p₂) ⊎ (p₂ ≤ᵖ p₁)

-- If you uncomment the next two lines Agda complains... ?!?!
-- module _ {l : Level} where
--   open TotalOrdering {l}

  data Order (a b : P) : Set where
    le : a ≤ᵖ b → Order a b
    gt : ¬ (a ≤ᵖ b) → Order a b

  data TriOrder (a b : P) : Set l where 
    a<b : a ≤ᵖ b → a ≢ b → TriOrder a b
    a=b : a ≡ b → TriOrder a b 
    a>b : b ≤ᵖ a → a ≢ b → TriOrder a b

record Priority {l : Level} : Set (lsuc l) where
  field
    Ord : TotalOrdering {l}
  open TotalOrdering Ord public  -- export all names to the outside!

  field
    cmp : (p₁ p₂ : P) → Order p₁ p₂
    cmp' : (p₁ p₂ : P) → TriOrder p₁ p₂

module ℕ-ordering where 
  -- Example: natural numbers are partially ordered
  ℕ-partialOrd : PartialOrdering
  ℕ-partialOrd = record { 
    P = ℕ ; 
    _≤ᵖ_ = _≤_ ; 
    ≤ᵖ-refl = ≤-refl ; 
    ≤ᵖ-antisym = ≤-antisym ;
    ≤ᵖ-trans = ≤-trans }

  -- Example: natural numbers are totally ordered
  ℕ-totalOrd : TotalOrdering
  ℕ-totalOrd = record { 
    PartialOrd = ℕ-partialOrd ; 
    ≤ᵖ-total = ≤-total }

  module _ where   
    open TotalOrdering ℕ-totalOrd
    open import Data.Nat.Properties using (≤-pred; suc-injective)
    
    ℕ-priority : Priority
    ℕ-priority = record { 
      Ord = ℕ-totalOrd ; 
      cmp = cmp-aux ; 
      cmp' = cmp'-aux }
      where
        cmp-aux-suc : {p₁ p₂ : ℕ} → Order p₁ p₂ → Order (suc p₁) (suc p₂)
        cmp-aux-suc (le x) = le (s≤s x)
        cmp-aux-suc (gt x) = gt (λ ss → x (≤-pred ss))
       
        cmp-aux : (p₁ p₂ : ℕ) → Order p₁ p₂
        cmp-aux zero p₂ = le z≤n
        cmp-aux (suc p₁) zero = gt (λ ())
        cmp-aux (suc p₁) (suc p₂) = cmp-aux-suc (cmp-aux p₁ p₂)
        
        cmp'-aux-suc : {p₁ p₂ : ℕ} → TriOrder p₁ p₂ → TriOrder (suc p₁) (suc p₂)
        cmp'-aux-suc (a<b x x₁) = a<b (s≤s x) (λ x₂ → x₁ (suc-injective x₂))
        cmp'-aux-suc (a=b x) = a=b (cong suc x)
        cmp'-aux-suc (a>b x x₁) = a>b (s≤s x) (λ x₂ → x₁ (suc-injective x₂))

        cmp'-aux : (p₁ p₂ : ℕ) → TriOrder p₁ p₂
        cmp'-aux zero zero = a=b refl
        cmp'-aux zero (suc p₂) = a<b z≤n (λ ())
        cmp'-aux (suc p₁) zero = a>b z≤n (λ ())
        cmp'-aux (suc p₁) (suc p₂) = cmp'-aux-suc (cmp'-aux p₁ p₂)
