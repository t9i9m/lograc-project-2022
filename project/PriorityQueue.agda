{-# OPTIONS --sized-types #-}

module PriorityQueue where

open import Ordering using (Priority; module ℕ-ordering) -- This is our file

open import Level        renaming (zero to lzero; suc to lsuc)
open import Size
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length; foldl)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-trans; ≤-total)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_; curry; uncurry)
open import Relation.Nullary     using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)


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
    peek : priorityQueue → Maybe (Priorities × Value)
    -- pop element with priority
    pop : priorityQueue → priorityQueue
  
    -- behavioural properties
    -- Note: instead of Maybe, we could have prevented peeking or popping emp using data types?
    peek-emp : peek emp ≡ nothing
    pop-emp : pop emp ≡ emp
    insert₁-peek : ((p , v) : Priorities × Value) → peek (insert emp (p , v)) ≡ just (p , v)
    insert₁-pop : (pv : Priorities × Value) → pop (insert emp pv) ≡ emp
    insert₂-peek-p₁≤p₂ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → peek (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ just (p₁ , v₁)
    insert₂-peek-p₂≤p₁ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂ 
                  → peek (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ just (p₂ , v₂)
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
     insert₂-peek-p₂≤p₁ = insert₂-peek-p₂≤p₁-aux ;
     insert₂-pop-p₁≤p₂ = insert₂-pop-p₁≤p₂-aux ;
     insert₂-pop-p₂≤p₁ = insert₂-pop-p₂≤p₁-aux }
     
    where 
      insert-aux : List (Priorities × Value) → Priorities × Value → List (Priorities × Value)
      insert-aux xs pv = pv ∷ xs

      peek-aux : List (Priorities × Value) → Maybe (Priorities × Value)
      peek-aux [] = nothing
      peek-aux ((p , v) ∷ xs) with peek-aux xs 
      peek-aux ((p , v) ∷ xs) | just (p' , ₂) with cmp p p' 
      peek-aux ((p , v) ∷ xs) | just (p' , v') | le _ = just (p , v)
      peek-aux ((p , v) ∷ xs) | just (p' , v') | gt _ = just (p' , v')
      peek-aux ((p , v) ∷ xs) | nothing = just (p , v)

      pop-aux : List (Priorities × Value) → List (Priorities × Value)
      pop-aux [] = []
      pop-aux ((p , v) ∷ xs) with peek-aux xs
      pop-aux ((p , v) ∷ xs) | just (p' , v') with cmp p p'
      pop-aux ((p , v) ∷ xs) | just (p' , v') | le _ = xs
      pop-aux ((p , v) ∷ xs) | just (p' , v') | gt _ = (p , v) ∷ pop-aux xs
      pop-aux ((p , v) ∷ xs) | nothing = []

      insert₁-peek-aux : ((p , v) : Priorities × Value) →
                         peek-aux (insert-aux [] (p , v)) ≡ just (p , v)
      insert₁-peek-aux (p , v) = refl

      insert₁-pop-aux : (pv : Priorities × Value) → pop-aux (insert-aux [] pv) ≡ []
      insert₁-pop-aux x = refl

      insert₂-peek-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                    → p₁ ≤ᵖ p₂
                    → p₁ ≢ p₂
                    → peek-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ just (p₁ , v₁)
      insert₂-peek-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₂ p₁ 
      ... | le p₂≤p₁ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
      ... | gt _ = refl

      insert₂-peek-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                    → p₂ ≤ᵖ p₁
                    → p₁ ≢ p₂ 
                    → peek-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ just (p₂ , v₂)
      insert₂-peek-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₂ p₁
      ... | le _ = refl
      ... | gt p₂>p₁ = ⊥-elim (p₂>p₁ p₂≤p₁)

      insert₂-pop-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                    → p₁ ≤ᵖ p₂
                    → p₁ ≢ p₂
                    → pop-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ insert-aux [] (p₂ , v₂)
      insert₂-pop-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₂ p₁ 
      ... | le p₂≤p₁ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
      ... | gt p₂>p₁ = refl

      insert₂-pop-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                    → p₂ ≤ᵖ p₁
                    → p₁ ≢ p₂ 
                    → pop-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ insert-aux [] (p₁ , v₁)
      insert₂-pop-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₂ p₁
      ... | le _ = refl
      ... | gt p₂>p₁ = ⊥-elim (p₂>p₁ p₂≤p₁)

-- Weight biased leftist heap
module MinHeap {l₁ l₂ l₃ : Level} 
               (Pr : Priority {l₁}) (Value : Set l₂) where
  
  open Priority Pr renaming (P to Priorities)
  open PriorityQueue      

  module _ where 
    open ℕ-ordering using (ℕ-priority)
    open Priority ℕ-priority renaming (cmp to ℕ-cmp)

    Rank : Set
    Rank = ℕ

    data Heap {i : Size} : Set (l₁ ⊔ l₂) where 
      empty : Heap
      node  : {i₁ i₂ : Size< i} → Rank → Priorities × Value 
                → (l : Heap {i₁}) → (r : Heap {i₂}) → Heap

    rank : (h : Heap) → Rank
    rank empty = zero
    rank (node r _ _ _) = r

    merge : {i j : Size} → (l : Heap {i}) → (r : Heap {j}) → Heap
    merge empty r = r
    merge l empty = l
    merge (node s₁ (p₁ , v₁) l₁ r₁) (node s₂ (p₂ , v₂) l₂ r₂) 
      with cmp p₁ p₂ 
          | ℕ-cmp (rank r₁ + s₂) (rank l₁) 
          | ℕ-cmp (rank r₂ + s₁) (rank l₂)
    ... | le _ | le _ | _    = node (s₁ + s₂) (p₁ , v₁) l₁ (merge r₁ (node s₂ (p₂ , v₂) l₂ r₂))
    ... | le _ | gt _ | _    = node (s₁ + s₂) (p₁ , v₁) (merge r₁ (node s₂ (p₂ , v₂) l₂ r₂)) l₁
    ... | gt _ | _    | le _ = node (s₁ + s₂) (p₂ , v₂) l₂ (merge r₂ (node s₁ (p₁ , v₁) l₁ r₁))
    ... | gt _ | _    | gt _ = node (s₁ + s₂) (p₂ , v₂) (merge r₂ (node s₁ (p₁ , v₁) l₁ r₁)) l₂

    singleton : Priorities × Value → Heap
    singleton pv = node 1 pv empty empty

  MinHeapPriorityQueue : PriorityQueue Pr Value
  MinHeapPriorityQueue = record { 
    priorityQueue = Heap ;
    emp = empty ;
    insert = λ h pv → merge h (singleton pv) ;
    peek = peek-aux ;
    pop = pop-aux ;
    peek-emp = refl ;
    pop-emp = refl ;
    insert₁-peek = insert₁-peek-aux ;
    insert₁-pop = insert₁-pop-aux ; 
    insert₂-peek-p₁≤p₂ = insert₂-peek-p₁≤p₂-aux ;
    insert₂-peek-p₂≤p₁ = insert₂-peek-p₂≤p₁-aux ;
    insert₂-pop-p₁≤p₂ = insert₂-pop-p₁≤p₂-aux ;
    insert₂-pop-p₂≤p₁ = insert₂-pop-p₂≤p₁-aux }

    where

      peek-aux : Heap → Maybe (Priorities × Value)
      peek-aux empty = nothing
      peek-aux (node _ pv _ _) = just pv

      pop-aux : Heap → Heap
      pop-aux empty = empty
      pop-aux (node _ _ l r) = merge l r

      insert₁-peek-aux : ((p , v) : Priorities × Value) →
                         peek-aux (merge empty (singleton (p , v))) ≡ just (p , v)
      insert₁-peek-aux (p , v) = refl

      insert₁-pop-aux : (pv : Priorities × Value) → empty ≡ empty
      insert₁-pop-aux x = refl

      insert₂-peek-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → peek-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ just (p₁ , v₁)
      insert₂-peek-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₁ p₂ 
      ... | le _ = refl
      ... | gt p₁>p₂ = ⊥-elim (p₁>p₂ p₁≤p₂)
      
      insert₂-peek-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂
                  → peek-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ just (p₂ , v₂)
      insert₂-peek-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₁ p₂ 
      ... | le p₁≤p₂ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
      ... | gt _ = refl

      insert₂-pop-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → pop-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ node 1 (p₂ , v₂) empty empty 
      insert₂-pop-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₁ p₂ 
      ... | le p₁≤p₂ = refl
      ... | gt p₂>p₁ = ⊥-elim (p₂>p₁ p₁≤p₂)

      insert₂-pop-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂
                  → pop-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ node 1 (p₁ , v₁) empty empty 
      insert₂-pop-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₁ p₂ 
      ... | le p₁≤p₂ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
      ... | gt _ = refl
 