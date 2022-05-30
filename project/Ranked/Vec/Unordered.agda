-- Priority queue on an unordered vector.

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


VecPriorityQueue : PriorityQueue Pr Value
VecPriorityQueue = record { 
  priorityQueue = priorityQueue-aux ;
  emp = [] ;
  insert = insert-aux ;
  peek = peek-aux ;
  pop = pop-aux ;
  _∈ʰ_ = λ pv h → pv [∈] h ;  -- Reuse the [∈] relation for Vectors
  vec→heap = vec→heap-aux ;
  heap→vec = heap→vec-aux ;
  insert₁-peek = insert₁-peek-aux ;
  insert₁-pop = insert₁-pop-aux ; 
  insert₂-peek-p₁≤p₂ = insert₂-peek-p₁≤p₂-aux ;
  insert₂-peek-p₂≤p₁ = insert₂-peek-p₂≤p₁-aux ;
  insert₂-pop-p₁≤p₂ = insert₂-pop-p₁≤p₂-aux ;
  insert₂-pop-p₂≤p₁ = insert₂-pop-p₂≤p₁-aux ;
  pop-≤ = pop-≤-aux ; 
  insert-∈ = insert-∈-aux ;
  insert-[∈] = insert-[∈]-aux ;
  insert-preserves-∈ = insert-preserves-∈-aux ;
  [∈]⇒∈ʰ-lemma = [∈]⇒∈ʰ-lemma-aux ;
  ∈ʰ⇒[∈]-lemma = ∈ʰ⇒[∈]-lemma-aux }
  
  where 

    priorityQueue-aux : Rank → Set (l₁ ⊔ l₂)
    priorityQueue-aux = λ n → Vec (Priorities × Value) n

    insertₙ-aux : {n m : Rank} → (h : Vec (Priorities × Value) n) 
                → (xs : Vec (Priorities × Value) m)
                → Vec (Priorities × Value) (m + n)
    insertₙ-aux {n} {m} h xs = Data.Vec.foldl (λ n' → Vec (Priorities × Value) (n' + n)) (λ x → _∷ x) h xs 

    insert-aux : {n : Rank} → Vec (Priorities × Value) n → Priorities × Value → Vec (Priorities × Value) (suc n)
    insert-aux xs pv = pv ∷ xs

    -- This is actually just finding the minimum element `min`
    peek-aux : {n : Rank} → Vec (Priorities × Value) (suc n) → Priorities × Value
    peek-aux {zero} (pv ∷ []) = pv
    peek-aux {suc zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) with cmp p₁ p₂
    peek-aux {suc zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) | le _ = (p₁ , v₁)
    peek-aux {suc zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) | gt _ = (p₂ , v₂)
    peek-aux {suc (suc n)} (x ∷ xs) = peek-aux (x ∷ (peek-aux xs) ∷ [])

    pop-aux : {n : Rank} → Vec (Priorities × Value) (suc n) → Vec (Priorities × Value) n
    pop-aux {zero} h = []
    pop-aux {suc n} ((p₁ , v₁) ∷ xs) with peek-aux xs
    pop-aux {suc n} ((p₁ , v₁) ∷ xs) | (p₂ , v₂) with cmp p₁ p₂ 
    pop-aux {suc n} ((p₁ , v₁) ∷ xs) | p₂ , v₂ | le _ = xs
    pop-aux {suc n} ((p₁ , v₁) ∷ xs) | p₂ , v₂ | gt _ = (p₁ , v₁) ∷ pop-aux xs

    vec→heap-aux : {n : Rank} → Vec (Priorities × Value) n → Vec (Priorities × Value) n
    vec→heap-aux xs = Data.Vec.foldl priorityQueue-aux insert-aux [] xs

    heap→vec-aux : {n : Rank} → Vec (Priorities × Value) n → Vec (Priorities × Value) n
    heap→vec-aux {zero} h = []
    heap→vec-aux {suc n} h = peek-aux h ∷ (heap→vec-aux (pop-aux h))

    insert₁-peek-aux : ((p , v) : Priorities × Value) →
                        peek-aux (insert-aux [] (p , v)) ≡ (p , v)
    insert₁-peek-aux (p , v) = refl

    insert₁-pop-aux : (pv : Priorities × Value) → pop-aux (insert-aux [] pv) ≡ []
    insert₁-pop-aux x = refl

    insert₂-peek-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → peek-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ (p₁ , v₁)
    insert₂-peek-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₂ p₁ 
    ... | le p₂≤p₁ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
    ... | gt _ = refl

    insert₂-peek-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂ 
                  → peek-aux (insert-aux (insert-aux [] (p₁ , v₁)) (p₂ , v₂)) ≡ (p₂ , v₂)
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

    lemma-1 : {n : Rank} → (h : Vec (Priorities × Value) (2 + n))
            → proj₁ (head h) ≤ᵖ proj₁ (peek-aux (tail h))
            → head h ≡ peek-aux h
    lemma-1 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p with cmp p₁ p₂ 
    lemma-1 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | le _ = refl
    lemma-1 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | gt p₁>p₂ = ⊥-elim (p₁>p₂ p)
    lemma-1 {suc n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs))
    lemma-1 {suc n} ((p₁ , v₁) ∷ xs) p | le _ = refl
    lemma-1 {suc n} ((p₁ , v₁) ∷ xs) p | gt x = ⊥-elim (x p)

    lemma-2 : {n : Rank} → (h : Vec (Priorities × Value) (2 + n))
            → proj₁ (head h) ≤ᵖ proj₁ (peek-aux (tail h))
            → tail h ≡ pop-aux h
    lemma-2 {n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs))
    ... | le _ = refl
    ... | gt x = ⊥-elim (x p)

    lemma-3 : {n : Rank} → (h : Vec (Priorities × Value) (2 + n))
            → proj₁ (peek-aux (tail h)) ≤ᵖ proj₁ (head h)
            → proj₁ (peek-aux (tail h)) ≡ proj₁ (peek-aux h)
    lemma-3 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p with cmp p₁ p₂ 
    lemma-3 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | le x = ≤ᵖ-antisym p x
    lemma-3 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | gt x = refl
    lemma-3 {suc n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs)) 
    lemma-3 {suc n} ((p₁ , v₁) ∷ xs) p | le x = ≤ᵖ-antisym p x
    lemma-3 {suc n} ((p₁ , v₁) ∷ xs) p | gt x = refl

    lemma-3' : {n : Rank} → (h : Vec (Priorities × Value) (2 + n))
            → ¬ (proj₁ (head h) ≤ᵖ proj₁ (peek-aux (tail h)))
            → peek-aux (tail h) ≡ peek-aux h
    lemma-3' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p with cmp p₁ p₂ 
    lemma-3' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | le x = ⊥-elim (p x)
    lemma-3' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | gt x = refl
    lemma-3' {suc n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs)) 
    lemma-3' {suc n} ((p₁ , v₁) ∷ xs) p | le x = ⊥-elim (p x)
    lemma-3' {suc n} ((p₁ , v₁) ∷ xs) p | gt x = refl

    lemma-4 : {n : Rank} → (h : Vec (Priorities × Value) (2 + n))
            → ¬ (proj₁ (head h) ≤ᵖ proj₁ (peek-aux (tail h)))
            → (head h) ∷ (pop-aux (tail h)) ≡ pop-aux h
    lemma-4 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p with cmp p₁ p₂ 
    lemma-4 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | le x = ⊥-elim (p x)
    lemma-4 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) p | gt _ = refl
    lemma-4 {suc n} ((p₁ , v₁) ∷ xs) p with cmp p₁ (proj₁ (peek-aux xs))
    lemma-4 {suc n} ((p₁ , v₁) ∷ xs) p | le x = ⊥-elim (p x)
    lemma-4 {suc n} ((p₁ , v₁) ∷ xs) p | gt x = refl

    lemma-5 : {n : Rank} → (h : Vec (Priorities × Value) (2 + n))
            → proj₁ (peek-aux h) ≡ proj₁ (peek-aux (head h ∷ peek-aux (tail h) ∷ []))
            -- → peek-aux (head h ∷ (pop-aux (tail h))) ≡ peek-aux (head h ∷ (peek-aux (pop-aux (tail h))) ∷ [])
    lemma-5 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) with cmp p₁ p₂ 
    lemma-5 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) | le x = refl
    lemma-5 {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ []) | gt x = refl
    lemma-5 {suc n} ((p₁ , v₁) ∷ xs) with cmp p₁ (proj₁ (peek-aux xs))
    lemma-5 {suc n} ((p₁ , v₁) ∷ xs) | le x = refl
    lemma-5 {suc n} ((p₁ , v₁) ∷ xs) | gt x = refl

    lemma-5' : {n : Rank} → (h : Vec (Priorities × Value) (3 + n))
            → proj₁ (peek-aux (head h ∷ (pop-aux (tail h)))) ≡ proj₁ (peek-aux (head h ∷ (peek-aux (pop-aux (tail h))) ∷ []))
    lemma-5' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ (p₃ , v₃) ∷ []) with cmp p₁ p₃ | cmp p₂ p₃
    lemma-5' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ (p₃ , v₃) ∷ []) | le _ | le _ = refl
    lemma-5' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ (p₃ , v₃) ∷ []) | gt _ | le _ = refl
    lemma-5' {zero} ((p₁ , v₁) ∷ (p₂ , v₂) ∷ (p₃ , v₃) ∷ []) | _ | gt _ = refl
    lemma-5' {suc n} h = refl

    pop-≤-aux : {n : Rank} (h : Vec (Priorities × Value) (suc (suc n))) 
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

    insert-∈-aux : {n : Rank} (h : Vec (Priorities × Value) n)
                  → (pv : Priorities × Value) 
                  → pv [∈] insert-aux h pv
    insert-∈-aux h pv = ∈-head

    -- Read as "head in vec" lemma
    -- N.B. It seems Agda can figure out lemma-4 by itself (for the ∈-tail case).
    head-[∈]-lemma : {n : Rank} (h : Vec (Priorities × Value) n)
                          → (pv : Priorities × Value)
                          → pv [∈] (heap→vec-aux (pv ∷ h))
    head-[∈]-lemma {zero} [] pv = ∈-head
    head-[∈]-lemma {suc n} (x ∷ h) (p , v) with cmp p (proj₁ (peek-aux (x ∷ h)))
    head-[∈]-lemma {suc n} (x ∷ h) (p , v) | le p≤p' rewrite sym (lemma-1 ((p , v) ∷ x ∷ h) p≤p') = ∈-head
    head-[∈]-lemma {suc n} (x ∷ h) (p , v) | gt p>p' = ∈-tail (head-[∈]-lemma (pop-aux (x ∷ h)) (p , v))

    insert-[∈]-aux : {n : Rank} (h : Vec (Priorities × Value) n)
                      → (pv : Priorities × Value) 
                      → pv [∈] (heap→vec-aux (insert-aux h pv))
    insert-[∈]-aux {n} h pv = head-[∈]-lemma h pv

    insert-preserves-∈-aux : {n : Rank} (h : Vec (Priorities × Value) n)
                            → (pv : Priorities × Value) {pv' : Priorities × Value} 
                            → pv [∈] h 
                            → pv [∈] insert-aux h pv'
    insert-preserves-∈-aux .(pv ∷ _) pv ∈-head = ∈-tail ∈-head
    insert-preserves-∈-aux .(_ ∷ _) pv (∈-tail pv∈h) = ∈-tail (∈-tail pv∈h)

    -- Need to show that if an element is in the list, it is also in the reversed list...
    [∈]⇒∈ʰ-lemma-aux : {n : ℕ} (xs : Vec (Priorities × Value) n)
                  → (pv : Priorities × Value)
                  → pv [∈] xs
                  → pv [∈] vec→heap-aux xs
    [∈]⇒∈ʰ-lemma-aux {n} xs pv p∈xs = [∈]-rev xs p∈xs
    
    module _ where
      open PriorityQueue VecPriorityQueue using (SortedVec)
      open SortedVec

      private
        variable
          n : ℕ

      -- If we pop all elements from a heap into a vector, that vector will be sorted
      -- according to the priorities of the elements in the heap (thanks to pop-≤).
      heap→vec-Sorted : (h : Vec (Priorities × Value) n) → SortedVec (heap→vec-aux h)
      heap→vec-Sorted {zero} h = []-sorted
      heap→vec-Sorted {suc zero} h = [a]-sorted
      heap→vec-Sorted {suc (suc n)} h = [a≤b]-sorted (pop-≤-aux h) (heap→vec-Sorted (pop-aux h))

      -- Need to figure out a good definition to make proofs doable...
      insert-sorted : (xs : Vec (Priorities × Value) n)
            → (pv : Priorities × Value)
            → Vec (Priorities × Value) (1 + n)
      insert-sorted [] pv = pv ∷ []
      insert-sorted (x ∷ xs) (p , v) with cmp p (proj₁ (peek-aux (x ∷ xs)))
      ... | le x₁ = (p , v) ∷ x ∷ xs
      ... | gt x₁ = {! x ∷   !}
      -- insert-sorted [] pv = pv ∷ []
      -- insert-sorted ((p' , v') ∷ xs) (p , v) with cmp p p'
      -- ... | le x = (p , v) ∷ (p' , v') ∷ xs
      -- ... | gt x = (p' , v') ∷ (insert-sorted xs (p , v))
      
      -- insert-sorted : {xs : Vec (Priorities × Value) n}
      --               → SortedVec xs → (pv : Priorities × Value)
      --               → Vec (Priorities × Value) (1 + n)

      insert-sorted-lemma : (xs : Vec (Priorities × Value) (1 + n))
                          → (pv : Priorities × Value)
                          → proj₁ pv ≤ᵖ proj₁ (peek-aux xs) 
                          → insert-sorted xs pv ≡ pv ∷ xs
      insert-sorted-lemma xs pv q = {!   !}

      insert-sorted-Sorted : (xs : Vec (Priorities × Value) n)
                    → SortedVec xs
                    → (pv : Priorities × Value)
                    → SortedVec (insert-sorted xs pv)
      insert-sorted-Sorted xs pv = {!   !} 

      [∈]-insert-sorted : (xs : Vec (Priorities × Value) n)
                        → (pv : Priorities × Value)
                        → (y : Priorities × Value)
                        → pv [∈] xs 
                        → pv [∈] insert-sorted xs y
      [∈]-insert-sorted xs pv y q = {!   !}

      insert-sorted-tail : (xs : Vec (Priorities × Value) (2 + n))
                          → proj₁ (peek-aux (tail xs)) ≤ᵖ proj₁ (head xs) 
                          → insert-sorted (heap→vec-aux (tail xs)) (head xs) ≡ peek-aux (tail xs) ∷ insert-sorted (heap→vec-aux (pop-aux (tail xs))) (head xs)
      insert-sorted-tail xs q = {!   !}

      peek-sorted : {xs : Vec (Priorities × Value) (1 + n)}
                  → SortedVec xs 
                  → peek-aux xs ≡ head xs
      peek-sorted [a]-sorted = refl
      peek-sorted {xs = (pv₁ ∷ pv₂ ∷ rest)} ([a≤b]-sorted a≤b b∷xs) with cmp (proj₁ pv₁) (proj₁ (peek-aux (pv₂ ∷ rest)))
      ... | le x = sym (lemma-1 (pv₁ ∷ pv₂ ∷ rest) x)
      ... | gt x rewrite peek-sorted b∷xs = ⊥-elim (x a≤b) 

      -- The smallest element in the heap is the smallest element in the vector.
      peek-vec-lemma : (h : Vec (Priorities × Value) (1 + n))
                      → (pv : Priorities × Value)
                      → peek-aux h ≡ peek-aux (heap→vec-aux h)
      peek-vec-lemma h pv = sym (begin
        peek-aux (heap→vec-aux h) ≡⟨ peek-sorted (heap→vec-Sorted h) ⟩
        peek-aux h ∎)

      ≤-vec-lemma : (xs : Vec (Priorities × Value) (1 + n))
                  → (pv : Priorities × Value)
                  → proj₁ pv ≤ᵖ proj₁ (peek-aux xs) 
                  → proj₁ pv ≤ᵖ proj₁ (peek-aux (heap→vec-aux xs))
      ≤-vec-lemma xs pv q rewrite sym (peek-vec-lemma xs pv) = q

      insert-heap→vec : {n : ℕ} (h : Vec (Priorities × Value) (1 + n)) 
                      → heap→vec-aux h ≡ insert-sorted (heap→vec-aux (tail h)) (head h)
      insert-heap→vec {n = 0} (x ∷ []) = refl
      insert-heap→vec {n = suc n} (x ∷ xs) with cmp (proj₁ x) (proj₁ (peek-aux xs))
      insert-heap→vec {n = suc n} (x ∷ xs) | le x₂ = begin
        peek-aux (x ∷ xs) ∷ peek-aux xs ∷ heap→vec-aux (pop-aux xs) ≡⟨ cong (_∷ peek-aux xs ∷ heap→vec-aux (pop-aux xs)) (sym (lemma-1 (x ∷ xs) x₂)) ⟩
        x ∷ peek-aux xs ∷ heap→vec-aux (pop-aux xs) ≡⟨ refl ⟩
        x ∷ heap→vec-aux xs ≡⟨ sym (insert-sorted-lemma (heap→vec-aux xs) x (≤-vec-lemma xs x x₂)) ⟩
        insert-sorted (heap→vec-aux xs) x ∎
      insert-heap→vec {n = suc n} (x ∷ xs) | gt x₂ = begin 
        peek-aux (x ∷ xs) ∷ peek-aux (x ∷ pop-aux xs) ∷ heap→vec-aux (pop-aux (x ∷ pop-aux xs)) ≡⟨ refl ⟩
        peek-aux (x ∷ xs) ∷ heap→vec-aux (x ∷ pop-aux xs) ≡⟨ cong (_∷ heap→vec-aux (x ∷ pop-aux xs)) (sym (lemma-3' (x ∷ xs) x₂)) ⟩
        peek-aux xs ∷ heap→vec-aux (x ∷ pop-aux xs) ≡⟨ cong (peek-aux xs ∷_) ((insert-heap→vec (x ∷ pop-aux xs))) ⟩
        peek-aux xs ∷ insert-sorted (heap→vec-aux (pop-aux xs)) x ≡⟨ sym (insert-sorted-tail (x ∷ xs) (≤ᵖ-total-lemma x₂)) ⟩
        insert-sorted (heap→vec-aux xs) x ∎

    ∈ʰ⇒[∈]-lemma-aux : {n : Rank} (h : Vec (Priorities × Value) n) 
                      → (pv : Priorities × Value) 
                      → pv [∈] h 
                      → pv [∈] heap→vec-aux h
    ∈ʰ⇒[∈]-lemma-aux {.(suc _)} (pv ∷ h) pv ∈-head = head-[∈]-lemma h pv
    ∈ʰ⇒[∈]-lemma-aux {.(suc _)} (x ∷ xs) pv (∈-tail p∈xs) rewrite insert-heap→vec (x ∷ xs) = [∈]-insert-sorted (heap→vec-aux xs) pv x (∈ʰ⇒[∈]-lemma-aux xs pv p∈xs)
