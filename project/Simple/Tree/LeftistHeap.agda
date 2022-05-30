-- Weight biased leftist heap

{-# OPTIONS --sized-types #-}
open import Ordering using (Priority; module ℕ-ordering) -- This is our file
open import Level        renaming (zero to lzero; suc to lsuc)

module Simple.Tree.LeftistHeap {l₁ l₂ l₃ : Level} (Pr : Priority {l₁}) (Value : Set l₂) where

open import Simple.PriorityQueue
open Priority Pr renaming (P to Priorities)

open import Size
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; _×_)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl)


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
                → pop-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ singleton (p₂ , v₂)
    insert₂-pop-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₁ p₂ 
    ... | le p₁≤p₂ = refl
    ... | gt p₂>p₁ = ⊥-elim (p₂>p₁ p₁≤p₂)

    insert₂-pop-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                → p₂ ≤ᵖ p₁
                → p₁ ≢ p₂
                → pop-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ singleton (p₁ , v₁)
    insert₂-pop-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₁ p₂ 
    ... | le p₁≤p₂ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
    ... | gt _ = refl
