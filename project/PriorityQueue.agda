module PriorityQueue where

open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-trans)
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

record Priority {l : Level} : Set (lsuc l) where
  field
    Priorities : Set
--  cmp : (p p' : Priorities) →  {!   !}
    
record Ordering {l : Level} : Set (lsuc l) where
  field
    P' : Priority {l}
  open Priority P'
  field
  -- order relation
    _≤ᵖ_   : Priorities → Priorities → Set
    -- reflexivity
    ≤ᵖ-refl : {p : Priorities} → p ≤ᵖ p
    -- antisymmetry
    ≤ᵖ-antis : {p₁ p₂ : Priorities} → p₁ ≤ᵖ p₂ → p₂ ≤ᵖ p₁ → p₁ ≡ p₂ 
    -- transitivity
    ≤ᵖ-trans  : {p₁ p₂ p₃ : Priorities} → p₁ ≤ᵖ p₂ → p₂ ≤ᵖ p₃ → p₁ ≤ᵖ p₃

orderingℕ : Ordering 
orderingℕ = record {
  P' = record { Priorities = ℕ } ;
  _≤ᵖ_ = λ x x₁ → x ≤ x₁ ;
  ≤ᵖ-refl = ≤-refl ;
  ≤ᵖ-antis = ≤-antisym ;
  ≤ᵖ-trans = ≤-trans }
  
-- data _</≡/>_ (p₁ p₂ : Priority) : Set where
--   p₁<p₂ : p₁ ≤ᵖ p₂ → p₁ </≡/> p₂
--   p₁≡p₂ : p₁ ≡ᵖ p₂ → p₁ </≡/> p₂
--   p₁>p₂ : p₁ >ᵖ p₂ → p₁ </≡/> p₂


-- record PriorityQueue (A : Set) : Set where 
--   field 
--     -- type of priorityQueue data (for storing priority-value pairs)
--     PQ : Set
--     -- empty priorityQueue
--     emp : PQ
--     -- insert element with priority
--     insert : PQ → Priority × A → PQ
-- 
--     peek : PQ → A
--     pop : PQ → PQ
    
