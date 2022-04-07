module PriorityQueue where

open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-trans; ≤-total)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_; curry; uncurry)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (Vec; []; _∷_)

open import Function     using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

-- data Smaller {l : Level} (A : Set l) : Set l where
--   yes : A
--   no :

-- record Priority {l : Level} : Set (lsuc l) where
--   field
--     Priorities : Set
-- --  cmp : (p p' : Priorities) →  {!   !}

-- record Ordering {l : Level} : Set (lsuc l) where
--   field
--     P' : Priority {l}
--   open Priority P'
--   field
--     -- order relation
--     _≤ᵖ_   : Priorities → Priorities → Set
--     -- reflexivity
--     ≤ᵖ-refl : {p : Priorities} → p ≤ᵖ p
--     -- antisymmetry
--     ≤ᵖ-antis : {p₁ p₂ : Priorities} → p₁ ≤ᵖ p₂ → p₂ ≤ᵖ p₁ → p₁ ≡ p₂ 
--     -- transitivity
--     ≤ᵖ-trans  : {p₁ p₂ p₃ : Priorities} → p₁ ≤ᵖ p₂ → p₂ ≤ᵖ p₃ → p₁ ≤ᵖ p₃

-- Non-strict partial order relation on a set A
-- NB this exists also in Data.Nat.Properties
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
    ≤ᵖ-total  : (p₁ p₂ : P) → (p₁ ≤ᵖ p₂) ⊎ (p₂ ≤ᵖ p₁)

  data Order (a b : P) : Set where
    le : a ≤ᵖ b → Order a b
    ge : b ≤ᵖ a → Order a b

  cmp : (p₁ p₂ : P) → Order p₁ p₂
  cmp p₁ p₂ with ≤ᵖ-total p₁ p₂
  ... | inj₁ p₁≤p₂ = le p₁≤p₂
  ... | inj₂ p₂≤p₁ = ge p₂≤p₁

record Priority {l : Level} : Set (lsuc l) where
  field
    Ord : TotalOrdering {l}
  open TotalOrdering Ord public  -- export all names to the outside!


module Tests where 
  -- -- Example: natural numbers are partially ordered
  ℕ-partialOrd : PartialOrdering
  ℕ-partialOrd = record { 
    P = ℕ ; 
    _≤ᵖ_ = _≤_ ; 
    ≤ᵖ-refl = ≤-refl ; 
    ≤ᵖ-antisym = ≤-antisym ;
    ≤ᵖ-trans = ≤-trans }

  -- -- Example: natural numbers are totally ordered
  ℕ-totalOrd : TotalOrdering
  ℕ-totalOrd = record { 
    PartialOrd = ℕ-partialOrd ; 
    ≤ᵖ-total = ≤-total }

  ℕ-priority : Priority
  ℕ-priority = record { Ord = ℕ-totalOrd }
  
  open Priority ℕ-priority
  test : Order 2 3
  test = cmp 2 3

-- orderingℕ : Ordering 
-- orderingℕ = record {
--   P' = record { Priorities = ℕ } ;
--   _≤ᵖ_ = λ x x₁ → x ≤ x₁ ;
--   ≤ᵖ-refl = ≤-refl ;
--   ≤ᵖ-antis = ≤-antisym ;
--   ≤ᵖ-trans = ≤-trans }


record PriorityQueue {l : Level} 
                     (Pr : Priority {l}) (Value : Set) : Set (lsuc l) where 
  open Priority Pr renaming (P to Priorities)

  field 
    -- type of priorityQueue data (for storing priority-value pairs)
    priorityQueue : Set
    -- empty priorityQueue
    emp : priorityQueue
    -- insert element with priority
    insert : priorityQueue → Value → Priorities → priorityQueue

    peek : priorityQueue → Value
    pop : priorityQueue → priorityQueue
    
 