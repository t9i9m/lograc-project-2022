-- Record of PriorityQueue (Ranked)

module Ranked.PriorityQueue where

open import Ordering using (Priority; module ℕ-ordering)
open import VecProperties using (_[∈]_)

open import Level        renaming (zero to lzero; suc to lsuc)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Data.Vec     using (Vec; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_)


-- Rank denotes the size of a priority queue, i.e. it's just a natural number.
Rank : Set
Rank = ℕ

-- Source: https://www.twanvl.nl/blog/agda/sorting
-- x ◂ xs ≡ ys means that ys is equal to xs with x inserted somewhere
data _,_◂_≡_ {l : Level} (A : Set l) (x : A): {n : Rank} → (Vec (A) n) → (Vec (A) (suc n)) → Set l where
      here  : {n : Rank} {xs : Vec (A) n}           → A , x ◂ xs ≡ ((x ∷ xs))
      there : {n : Rank} {y : A} {xs : Vec (A) n} {xys : Vec (A) (suc n)} → (p : A , x ◂ xs ≡ xys) → A , x ◂ (y ∷ xs) ≡ ((y ∷ xys))

-- Proof that a vectors are permutation of each other by recursively inserting elements in random places
data IsPermutation {l : Level} (A : Set l) : {n : Rank} → Vec (A) n → Vec (A) n → Set l where
  []  : IsPermutation A [] []
  _∷_ : {n : Rank} {x : A} {xs : Vec (A) n} {ys : Vec (A) n} {xys : Vec (A) (suc n)}
      → (p : A , x ◂ ys ≡ xys)
      → (ps : IsPermutation A xs ys)
      → IsPermutation A (x ∷ xs) xys

-- Identity permutation
id-permutation : {l : Level} (A : Set l) {n : Rank} → (xs : Vec (A) n) → IsPermutation A xs xs
id-permutation A [] = []
id-permutation A (x ∷ xs) = here ∷ id-permutation A xs


record PriorityQueue {l₁ l₂ l₃ : Level} 
                     (Pr : Priority {l₁}) (Value : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where 
  open Priority Pr renaming (P to Priorities)
  --open insertion

  PV = Priorities × Value

  field 
    -- type of priorityQueue data (for storing priority-value pairs)
    priorityQueue : (n : Rank) → Set l₃
    -- empty priorityQueue
    emp : priorityQueue zero
    -- insert element with priority
    insert : {n : Rank} → priorityQueue n → PV → priorityQueue (suc n)
    -- peek element with priority
    peek : {n : Rank} → priorityQueue (suc n) → PV
    -- pop element with priority
    pop : {n : Rank} → priorityQueue (suc n) → priorityQueue n
  
    -- An instance of the record type should implement an ∈ relation that gives
    -- a proof that a given element is an element of the heap. 
    _∈ʰ_ : {n : Rank} → (pv : PV) → priorityQueue n → Set l₃

    -- Agda doesn't allow recursive function definitions as helper funtions,
    -- that is why there is heap→vec' defined a bit further down
    heap→vec : {n : Rank} → (h : priorityQueue n) → Vec (PV) n

    vec→heap : {n : Rank} → (xs : Vec (PV) n) → priorityQueue n

  -- Helper functions
  peekp : {n : Rank} → priorityQueue (suc n) → Priorities
  peekp h = proj₁ (peek h)

  peekv : {n : Rank} → priorityQueue (suc n) → Value
  peekv h = proj₂ (peek h)

  heap→vecp : {n : Rank} → (h : priorityQueue n) → Vec Priorities n
  heap→vecp h = Data.Vec.map proj₁ (heap→vec h)
  
  field
    -- behavioural properties
    insert₁-peek : ((p , v) : PV) → peek (insert emp (p , v)) ≡ (p , v)
    insert₁-pop : (pv : PV) → pop (insert emp pv) ≡ emp
    insert₂-peek-p₁≤p₂ : ((p₁ , v₁) (p₂ , v₂) : PV) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → peek (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ (p₁ , v₁)
    insert₂-peek-p₂≤p₁ : ((p₁ , v₁) (p₂ , v₂) : PV) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂ 
                  → peek (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ (p₂ , v₂)
    insert₂-pop-p₁≤p₂ : ((p₁ , v₁) (p₂ , v₂) : PV) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → pop (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ insert emp (p₂ , v₂)
    insert₂-pop-p₂≤p₁ : ((p₁ , v₁) (p₂ , v₂) : PV) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂
                  → pop (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ insert emp (p₁ , v₁)

    -- Consecutive peeks and pops from a heap should return elements with decreasing priorities.
    -- Note: need at least two values to peek
    pop-≤ : {n : Rank} → (h : priorityQueue (suc (suc n)))
          → peekp h ≤ᵖ (peekp (pop h))

    peek-vec◂pop-vec : {n : Rank} → (xs : Vec (PV) (suc n)) → PV , (peek (vec→heap xs)) ◂ heap→vec (pop (vec→heap xs)) ≡ xs

    vec→heap→vec-Permutation : {n : Rank} (xs : Vec (PV) n) 
                              → IsPermutation PV (heap→vec (vec→heap xs)) xs

  heap→vec' : {n : Rank} → (h : priorityQueue n) → Vec (PV) n
  heap→vec' {zero} h = []
  heap→vec' {suc n} h = peek h ∷ (heap→vec' (pop h))

  module _ where
    
    private
      variable
        m n : ℕ

    data SortedVec : Vec (PV) n → Set where
      []-sorted : SortedVec []
      [a]-sorted : {pv : PV} → SortedVec (pv ∷ [])
      [a≤b]-sorted : {rest : Vec (PV) m}
                  → {pv₁ pv₂ : PV}
                  → proj₁ pv₁ ≤ᵖ proj₁ pv₂ 
                  → SortedVec (pv₂ ∷ rest)
                  → SortedVec (pv₁ ∷ pv₂ ∷ rest)

    -- If we pop all elements from a heap into a vector, that vector will be sorted
    -- according to the priorities of the elements in the heap (thanks to pop-≤).
    heap→vec-Sorted : (h : priorityQueue n) → SortedVec (heap→vec' h)
    heap→vec-Sorted {zero} h = []-sorted
    heap→vec-Sorted {suc zero} h = [a]-sorted
    heap→vec-Sorted {suc (suc n)} h = [a≤b]-sorted (pop-≤ h) (heap→vec-Sorted (pop h))

    -- This is the ultimate goal: inserting a list of pairs and then emptying out the heap
    -- should result in a sorted list which is a permutation of the input list.
    priorityQueue-lemma : (xs : Vec (PV) n)
                        → SortedVec (heap→vec' (vec→heap xs)) × (IsPermutation PV (heap→vec (vec→heap xs)) xs)
    priorityQueue-lemma xs = (heap→vec-Sorted (vec→heap xs)) , (vec→heap→vec-Permutation xs)
