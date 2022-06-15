-- Priority queue on an unordered vector (Ranked)

open import Ordering using (Priority; module ℕ-ordering) -- This is our file
open import Level        renaming (zero to lzero; suc to lsuc)

module Ranked.Vec.Unordered {l₁ l₂ : Level} (Pr : Priority {l₁}) (Value : Set l₂) where

open import Ranked.PriorityQueue
open import VecProperties
open Priority Pr renaming (P to Priorities)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Data.Vec     using (Vec; []; _∷_; head; tail)
open import Relation.Nullary     using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

PV = Priorities × Value


VecPriorityQueue : PriorityQueue Pr Value
VecPriorityQueue = record { 
  priorityQueue = priorityQueue-aux ;
  emp = [] ;
  insert = insert-aux ;
  peek = peek-aux ;
  pop = pop-aux ;
  _∈ʰ_ = λ pv h → pv [∈] h ;
  heap→vec = heap→vec-aux ;
  vec→heap = vec→heap-aux ;
  insert₁-peek = insert₁-peek-aux ;
  insert₁-pop = insert₁-pop-aux ; 
  insert₂-peek-p₁≤p₂ = insert₂-peek-p₁≤p₂-aux ;
  insert₂-peek-p₂≤p₁ = insert₂-peek-p₂≤p₁-aux ;
  insert₂-pop-p₁≤p₂ = insert₂-pop-p₁≤p₂-aux ;
  insert₂-pop-p₂≤p₁ = insert₂-pop-p₂≤p₁-aux ;
  pop-≤ = pop-≤-aux ;
  peek-vec◂pop-vec = peek-vec◂pop-vec-aux ;
  vec→heap→vec-Permutation = vec→heap→vec-Permutation-aux }
  
  where 

    priorityQueue-aux : Rank → Set (l₁ ⊔ l₂)
    priorityQueue-aux = λ n → Vec (PV) n

    insertₙ-aux : {n m : Rank} → (h : Vec (PV) n) 
                → (xs : Vec (PV) m)
                → Vec (PV) (m + n)
    insertₙ-aux {n} {m} h xs = Data.Vec.foldl (λ n' → Vec (PV) (n' + n)) (λ x → _∷ x) h xs 

    insert-aux : {n : Rank} → Vec (PV) n → PV → Vec (PV) (suc n)
    insert-aux xs pv = pv ∷ xs

    -- This is actually just finding the minimum element `min`
    peek-aux : {n : Rank} → Vec (PV) (suc n) → PV
    peek-aux {zero} (pv ∷ []) = pv
    peek-aux {suc zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) with cmp p₁ p₂
    peek-aux {suc zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) | le _ = (p₁ , v₁)
    peek-aux {suc zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) | gt _ = (p₂ , v₂)
    peek-aux {suc (suc n)} (x ∷ xs) = peek-aux (x ∷ (peek-aux xs) ∷ [])

    pop-aux : {n : Rank} → Vec (PV) (suc n) → Vec (PV) n
    pop-aux {zero} h = []
    pop-aux {suc n} ((p₁ , v₁) ∷ xs) with peek-aux xs
    pop-aux {suc n} ((p₁ , v₁) ∷ xs) | (p₂ , v₂) with cmp p₁ p₂ 
    pop-aux {suc n} ((p₁ , v₁) ∷ xs) | p₂ , v₂ | le _ = xs
    pop-aux {suc n} ((p₁ , v₁) ∷ xs) | p₂ , v₂ | gt _ = (p₁ , v₁) ∷ pop-aux xs

    heap→vec-aux : {n : Rank} → Vec (PV) n → Vec (PV) n
    heap→vec-aux {zero} h = []
    heap→vec-aux {suc n} h = peek-aux h ∷ (heap→vec-aux (pop-aux h))

    vec→heap-aux : {n : Rank} → Vec (PV) n → priorityQueue-aux n
    vec→heap-aux xs = Data.Vec.foldl priorityQueue-aux insert-aux [] xs

    insert₁-peek-aux : ((p , v) : PV) →
                        peek-aux (insert-aux [] (p , v)) ≡ (p , v)
    insert₁-peek-aux (p , v) = refl

    insert₁-pop-aux : (pv : PV) → pop-aux (insert-aux [] pv) ≡ []
    insert₁-pop-aux x = refl

    insert₂-peek-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : PV) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → peek-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ (p₁ , v₁)
    insert₂-peek-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₂ p₁ 
    ... | le p₂≤p₁ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
    ... | gt _ = refl

    insert₂-peek-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : PV) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂ 
                  → peek-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ (p₂ , v₂)
    insert₂-peek-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₂ p₁
    ... | le _ = refl
    ... | gt p₂>p₁ = ⊥-elim (p₂>p₁ p₂≤p₁)

    insert₂-pop-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : PV) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → pop-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ insert-aux [] (p₂ , v₂)
    insert₂-pop-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₂ p₁ 
    ... | le p₂≤p₁ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
    ... | gt p₂>p₁ = refl

    insert₂-pop-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : PV) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂ 
                  → pop-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ insert-aux [] (p₁ , v₁)
    insert₂-pop-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₂ p₁
    ... | le _ = refl
    ... | gt p₂>p₁ = ⊥-elim (p₂>p₁ p₂≤p₁) 

    lemma-1 : {n : Rank} → (h : Vec (PV) (2 + n))
            → proj₁ (head h) ≤ᵖ proj₁ (peek-aux (tail h))
            → head h ≡ peek-aux h
    lemma-1 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p with cmp p₁ p₂ 
    lemma-1 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | le _ = refl
    lemma-1 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | gt p₁>p₂ = ⊥-elim (p₁>p₂ p)
    lemma-1 {suc n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs))
    lemma-1 {suc n} ((p₁ , v₁) ∷ xs) p | le _ = refl
    lemma-1 {suc n} ((p₁ , v₁) ∷ xs) p | gt x = ⊥-elim (x p)

    lemma-2 : {n : Rank} → (h : Vec (PV) (2 + n))
            → proj₁ (head h) ≤ᵖ proj₁ (peek-aux (tail h))
            → tail h ≡ pop-aux h
    lemma-2 {n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs))
    ... | le _ = refl
    ... | gt x = ⊥-elim (x p)

    lemma-3 : {n : Rank} → (h : Vec (PV) (2 + n))
            → proj₁ (peek-aux (tail h)) ≤ᵖ proj₁ (head h)
            → proj₁ (peek-aux (tail h)) ≡ proj₁ (peek-aux h)
    lemma-3 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p with cmp p₁ p₂ 
    lemma-3 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | le x = ≤ᵖ-antisym p x
    lemma-3 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | gt x = refl
    lemma-3 {suc n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs)) 
    lemma-3 {suc n} ((p₁ , v₁) ∷ xs) p | le x = ≤ᵖ-antisym p x
    lemma-3 {suc n} ((p₁ , v₁) ∷ xs) p | gt x = refl

    lemma-3' : {n : Rank} → (h : Vec (PV) (2 + n))
            → ¬ (proj₁ (head h) ≤ᵖ proj₁ (peek-aux (tail h)))
            → peek-aux (tail h) ≡ peek-aux h
    lemma-3' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p with cmp p₁ p₂ 
    lemma-3' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | le x = ⊥-elim (p x)
    lemma-3' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | gt x = refl
    lemma-3' {suc n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs)) 
    lemma-3' {suc n} ((p₁ , v₁) ∷ xs) p | le x = ⊥-elim (p x)
    lemma-3' {suc n} ((p₁ , v₁) ∷ xs) p | gt x = refl

    lemma-4 : {n : Rank} → (h : Vec (PV) (2 + n))
            → ¬ (proj₁ (head h) ≤ᵖ proj₁ (peek-aux (tail h)))
            → (head h) ∷ (pop-aux (tail h)) ≡ pop-aux h
    lemma-4 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p with cmp p₁ p₂ 
    lemma-4 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | le x = ⊥-elim (p x)
    lemma-4 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | gt _ = refl
    lemma-4 {suc n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs))
    lemma-4 {suc n} ((p₁ , v₁) ∷ xs) p | le x = ⊥-elim (p x)
    lemma-4 {suc n} ((p₁ , v₁) ∷ xs) p | gt x = refl

    lemma-5 : {n : Rank} → (h : Vec (PV) (2 + n))
            → proj₁ (peek-aux h) ≡ proj₁ (peek-aux (head h ∷ peek-aux (tail h) ∷ []))
    lemma-5 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) with cmp p₁ p₂ 
    lemma-5 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) | le x = refl
    lemma-5 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) | gt x = refl
    lemma-5 {suc n} ((p₁ , v₁) ∷ xs) with cmp p₁ (proj₁ (peek-aux xs))
    lemma-5 {suc n} ((p₁ , v₁) ∷ xs) | le x = refl
    lemma-5 {suc n} ((p₁ , v₁) ∷ xs) | gt x = refl

    lemma-5' : {n : Rank} → (h : Vec (PV) (3 + n))
            → proj₁ (peek-aux (head h ∷ (pop-aux (tail h)))) ≡ proj₁ (peek-aux (head h ∷ (peek-aux (pop-aux (tail h))) ∷ []))
    lemma-5' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ (p₃ , v₃) ∷ []) with cmp p₁ p₃ | cmp p₂ p₃
    lemma-5' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ (p₃ , v₃) ∷ []) | le _ | le _ = refl
    lemma-5' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ (p₃ , v₃) ∷ []) | gt _ | le _ = refl
    lemma-5' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ (p₃ , v₃) ∷ []) | _ | gt _ = refl
    lemma-5' {suc n} h = refl

    pop-≤-aux : {n : Rank} (h : Vec (PV) (suc (suc n))) 
            → proj₁ (peek-aux h) ≤ᵖ proj₁ (peek-aux (pop-aux h))
    pop-≤-aux {zero} ((p₁ , _) ∷ (p₂ , _) ∷ []) with cmp p₁ p₂ 
    pop-≤-aux {zero} ((p₁ , _) ∷ (p₂ , _) ∷ []) | le p₁≤p₂ = p₁≤p₂
    pop-≤-aux {zero} ((p₁ , _) ∷ (p₂ , _) ∷ []) | gt p₁>p₂ = ≤ᵖ-total-lemma p₁>p₂
    pop-≤-aux {suc n} ((p₀ , v₀) ∷ hs) with pop-≤-aux hs
    pop-≤-aux {suc n} ((p₀ , v₀) ∷ hs) | p₁≤p₂ with cmp p₀ (proj₁ (peek-aux hs))
    pop-≤-aux {suc n} ((p₀ , v₀) ∷ hs) | p₁≤p₂ | le p₀≤p₁ = p₀≤p₁
    pop-≤-aux {suc n} ((p₀ , v₀) ∷ hs) | p₁≤p₂ | gt p₀>p₁ with cmp p₀ (proj₁ (peek-aux (pop-aux hs))) | lemma-5' ((p₀ , v₀) ∷ hs)
    pop-≤-aux {suc n} ((p₀ , v₀) ∷ hs) | p₁≤p₂ | gt p₀>p₁ | le p₀≤p₂ | q = subst (proj₁ (peek-aux hs) ≤ᵖ_) (sym q) (≤ᵖ-total-lemma p₀>p₁)
    pop-≤-aux {suc n} ((p₀ , v₀) ∷ hs) | p₁≤p₂ | gt p₀>p₁ | gt p₀>p₂ | q = subst ((proj₁ (peek-aux hs) ≤ᵖ_)) (sym q) p₁≤p₂

    peek-vec◂pop-vec-aux : {n : Rank} (xs : Vec (PV) (suc n))
                → (PV) ,
                peek-aux (vec→heap-aux xs) ◂ heap→vec-aux (pop-aux (vec→heap-aux xs)) ≡ xs
    peek-vec◂pop-vec-aux (x ∷ []) = here
    peek-vec◂pop-vec-aux (x ∷ x₁ ∷ xs) = {!   !}

    vec→heap→vec-Permutation-aux : {n : Rank} (xs : Vec (PV) n) 
                              → IsPermutation PV (heap→vec-aux (vec→heap-aux xs)) xs
    vec→heap→vec-Permutation-aux [] = []
    vec→heap→vec-Permutation-aux (x ∷ xs) = (peek-vec◂pop-vec-aux (x ∷ xs)) ∷ id-permutation PV (heap→vec-aux (pop-aux (vec→heap-aux (x ∷ xs))))
