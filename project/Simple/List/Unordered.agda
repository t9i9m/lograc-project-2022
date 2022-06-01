-- Priority queue on an unordered list.

open import Ordering using (Priority; module ℕ-ordering) -- This is our file
open import Level        renaming (zero to lzero; suc to lsuc)

module Simple.List.Unordered {l₁ l₂ : Level} (Pr : Priority {l₁}) (Value : Set l₂) where

open import Simple.PriorityQueue
open Priority Pr renaming (P to Priorities)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length; foldl)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Product using (_,_; _×_)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl)


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
    peek-aux ((p , v) ∷ xs) | just (p' , v') with cmp p p' 
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

