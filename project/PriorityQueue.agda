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

open import Relation.Nullary     using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b


-- Non-strict partial order relation on a set A
-- Note: see also Data.Nat.Properties
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

    ≤ᵖ-total-strict : (p₁ p₂ : P) → (p₁ ≤ᵖ p₂) ⊎ (¬ (p₁ ≤ᵖ p₂))

  data Order (a b : P) : Set where
    le : a ≤ᵖ b → Order a b
    gt : ¬ (a ≤ᵖ b) → Order a b

  data TriOrder (a b : P) : Set l where 
    a<b : a ≤ᵖ b → a ≢ b → TriOrder a b
    a=b : a ≡ b → TriOrder a b 
    a>b : b ≤ᵖ a → a ≢ b → TriOrder a b
  
  cmp : (p₁ p₂ : P) → Order p₁ p₂
  cmp p₁ p₂ with ≤ᵖ-total-strict p₁ p₂
  ... | inj₁ p₁≤p₂ = le p₁≤p₂
  ... | inj₂ p₁>p₂ = gt p₁>p₂

  cmp-tri : (p₁ p₂ : P) → TriOrder p₁ p₂
  cmp-tri p₁ p₂ = {!   !}

  -- cmp-aux : {p₁ p₂ : P} → (p₁ ≤ᵖ p₂) → p₁ ≢ p₂ → cmp p₁ p₂ ≡ le (p₁ ≤ᵖ p₂)
  -- cmp-aux p q = ?

record Priority {l : Level} : Set (lsuc l) where
  field
    Ord : TotalOrdering {l}
  open TotalOrdering Ord public  -- export all names to the outside!


record PriorityQueue {l₁ l₂ l₃ : Level} 
                     (Pr : Priority {l₁}) (Value : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where 
  open Priority Pr renaming (P to Priorities)

  field 
    -- type of priorityQueue data (for storing priority-value pairs)
    priorityQueue : Set l₃
    -- empty priorityQueue
    emp : priorityQueue
    -- insert element with priority
    insert : priorityQueue → Priorities × Value → priorityQueue
    -- peek element with priority
    peek : priorityQueue → Maybe Value
    -- pop element with priority
    pop : priorityQueue → priorityQueue
  
    -- behavioural properties
    peek-emp : peek emp ≡ nothing
    pop-emp : pop emp ≡ emp
    insert₁-peek : ((p , v) : Priorities × Value) → peek (insert emp (p , v)) ≡ just v
    insert₁-pop : (pv : Priorities × Value) → pop (insert emp pv) ≡ emp
    
    insert₂-peek-p₁≤p₂ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → peek (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ just v₁
    insert₂-peek-p₂≤p₁ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂ 
                  → peek (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ just v₂
    insert₂-pop-p₁≤p₂ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → pop (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ insert emp (p₂ , v₂)
    insert₂-pop-p₂≤p₁ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂
                  → pop (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ insert emp (p₁ , v₁)
    
    
module ListPriorityQueueUnordered {l₁ l₂ : Level} 
                                  (Pr : Priority {l₁}) (Value : Set l₂) where
  
  open Priority Pr renaming (P to Priorities)
  open PriorityQueue

  ListPriorityQueue : PriorityQueue Pr Value
  ListPriorityQueue = record { 
    priorityQueue = List (Priorities × Value) ;
     emp = [] ;
     insert = insert-aux ;
     peek = peek-aux ;
     pop = pop-aux ;
     peek-emp = refl ;
     pop-emp = refl ;
     insert₁-peek = insert₁-peek-aux ;
     insert₁-pop = insert₁-pop-aux ; 
     insert₂-peek-p₁≤p₂ = insert₂-peek-p₁≤p₂-aux ;
     insert₂-peek-p₂≤p₁ = {!   !} ;
     insert₂-pop-p₁≤p₂ = {!   !} ;
     insert₂-pop-p₂≤p₁ = {!   !} }
     
    where 
      insert-aux : List (Priorities × Value) → Priorities × Value → List (Priorities × Value)
      insert-aux xs pv = pv ∷ xs

      peek-aux-aux : List (Priorities × Value) → Maybe (Priorities × Value)
      peek-aux-aux [] = nothing
      peek-aux-aux ((p , v) ∷ xs) with peek-aux-aux xs 
      peek-aux-aux ((p , v) ∷ xs) | just (p' , v') with cmp p p' 
      peek-aux-aux ((p , v) ∷ xs) | just (p' , v') | TotalOrdering.le _ = just (p , v)
      peek-aux-aux ((p , v) ∷ xs) | just (p' , v') | TotalOrdering.gt _ = just (p' , v')
      peek-aux-aux ((p , v) ∷ xs) | nothing = just (p , v)

      peek-aux : List (Priorities × Value) → Maybe Value
      peek-aux xs with peek-aux-aux xs
      ... | just (p , v) = just v
      ... | nothing = nothing

      pop-aux : List (Priorities × Value) → List (Priorities × Value)
      pop-aux [] = []
      pop-aux ((p , v) ∷ xs) with peek-aux-aux xs
      pop-aux ((p , v) ∷ xs) | just (p' , v') with cmp p p'
      pop-aux ((p , v) ∷ xs) | just (p' , v') | TotalOrdering.le _ = xs
      pop-aux ((p , v) ∷ xs) | just (p' , v') | TotalOrdering.gt _ = pop-aux xs
      pop-aux ((p , v) ∷ xs) | nothing = []

      insert₁-peek-aux : ((p , v) : Priorities × Value) →
                         peek-aux (insert-aux [] (p , v)) ≡ just v
      insert₁-peek-aux (p , v) = refl

      insert₁-pop-aux : (pv : Priorities × Value) → [] ≡ []
      insert₁-pop-aux x = refl

      insert₂-peek-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                    → p₁ ≤ᵖ p₂
                    → p₁ ≢ p₂
                    → peek-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ just v₁ 
      insert₂-peek-p₁≤p₂-aux (p , v) (p' , v') p≤p' p≢p' with cmp p' p 
      ... | TotalOrdering.le p'≤p = ⊥-elim (p≢p' (≤ᵖ-antisym p≤p' p'≤p))
      ... | TotalOrdering.gt _ = refl
      -- insert₂-peek-p₁≤p₂-aux (p , v) (p' , v') x y with  ≤ᵖ-total p' p | cmp p' p
      -- ... | inj₁ x₁ | TotalOrdering.le x₂ = {!   !}
      -- ... | inj₁ x₁ | TotalOrdering.ge x₂ = {!   !}
      -- ... | inj₂ y₁ | TotalOrdering.le x₁ = {!   !}
      -- ... | inj₂ y₁ | TotalOrdering.ge x₁ = {!   !}
      --   -- begin
      --   --   peek-aux (insert-aux (insert-aux [] (p , v)) (p' , v'))
      --   -- ≡⟨ refl ⟩
      --   --   peek-aux (insert-aux ((p , v) ∷ []) (p' , v'))
      --   -- ≡⟨ refl ⟩
      --   --   peek-aux ((p' , v') ∷ (p , v) ∷ [])  
      --   -- ≡⟨ {! F !} ⟩
      --   --   just v  
      --   -- ∎ 




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
    ≤ᵖ-total = ≤-total ; 
    ≤ᵖ-total-strict = λ p₁ p₂ → {!   !} }
  -- ℕ-totalOrd = record { 
  --   PartialOrd = ℕ-partialOrd ; 
  --   ≤ᵖ-total = ≤-total }

  ℕ-priority : Priority
  ℕ-priority = record { Ord = ℕ-totalOrd }
  
  open Priority ℕ-priority
  test : Order 2 3
  test = cmp 2 3
  