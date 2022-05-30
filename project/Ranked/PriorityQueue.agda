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


record PriorityQueue {l₁ l₂ l₃ : Level} 
                     (Pr : Priority {l₁}) (Value : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where 
  open Priority Pr renaming (P to Priorities)

  field 
    -- type of priorityQueue data (for storing priority-value pairs)
    priorityQueue : (n : Rank) → Set l₃
    -- empty priorityQueue
    emp : priorityQueue zero
    -- insert element with priority
    insert : {n : Rank} → priorityQueue n → Priorities × Value → priorityQueue (suc n)
    -- peek element with priority
    peek : {n : Rank} → priorityQueue (suc n) → Priorities × Value
    -- pop element with priority
    pop : {n : Rank} → priorityQueue (suc n) → priorityQueue n
  
    -- An instance of the record type should implement an ∈ relation that gives
    -- a proof that a given element is an element of the heap. 
    _∈ʰ_ : {n : Rank} → (pv : Priorities × Value) → priorityQueue n → Set l₃

    -- This function can be defined using just the above functions, however Agda doesn't
    -- allow us to define it here in the record? :(
    heap→vec : {n : Rank} → (h : priorityQueue n) → Vec (Priorities × Value) n
    -- Same problem as above
    vec→heap : {n : Rank} → (xs : Vec (Priorities × Value) n) → priorityQueue n

  -- Helper functions
  peekp : {n : Rank} → priorityQueue (suc n) → Priorities
  peekp h = proj₁ (peek h)

  peekv : {n : Rank} → priorityQueue (suc n) → Value
  peekv h = proj₂ (peek h)
  
  field
    -- behavioural properties
    insert₁-peek : ((p , v) : Priorities × Value) → peek (insert emp (p , v)) ≡ (p , v)
    insert₁-pop : (pv : Priorities × Value) → pop (insert emp pv) ≡ emp
    insert₂-peek-p₁≤p₂ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → peek (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ (p₁ , v₁)
    insert₂-peek-p₂≤p₁ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂ 
                  → peek (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ (p₂ , v₂)
    insert₂-pop-p₁≤p₂ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → pop (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ insert emp (p₂ , v₂)
    insert₂-pop-p₂≤p₁ : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂
                  → pop (insert (insert emp (p₁ , v₁)) (p₂ , v₂)) ≡ insert emp (p₁ , v₁)

    -- Consecutive peeks and pops from a heap should return elements with decreasing priorities.
    -- Note: need at least two values to peek
    pop-≤ : {n : Rank} → (h : priorityQueue (suc (suc n)))
          → peekp h ≤ᵖ (peekp (pop h))

    -- If we insert an element into a heap, the new heap should contain that element.
    insert-∈ : {n : Rank} → (h : priorityQueue n)
             → (pv : Priorities × Value) 
             → pv ∈ʰ (insert h pv)

    -- If we insert an element into a heap and empty the heap into a list, that 
    -- list should contain the inserted element.
    insert-[∈] : {n : Rank} → (h : priorityQueue n)
                 → (pv : Priorities × Value)
                 → pv [∈] heap→vec (insert h pv)

    -- This property proves that inserting into a heap doesn't change (remove/add) 
    -- existing elements in the heap.
    insert-preserves-∈ : {n : Rank} (h : priorityQueue n)
                       → (pv : Priorities × Value) {pv' : Priorities × Value} 
                       → pv ∈ʰ h 
                       → pv ∈ʰ insert h pv'
    
    -- If we are creating a heap from a vector and that vector contains a given item, the
    -- resulting heap will also contain that same item.
    [∈]⇒∈ʰ-lemma : {n : Rank} (xs : Vec (Priorities × Value) n)
                  → (pv : Priorities × Value)
                  → pv [∈] xs
                  → pv ∈ʰ vec→heap xs

    -- If we are popping a heap to a list and that heap contains a given item, the resulting
    -- list will also contain that same item.
    ∈ʰ⇒[∈]-lemma : {n : Rank} (h : priorityQueue n) 
                  → (pv : Priorities × Value)
                  → pv ∈ʰ h 
                  → pv [∈] heap→vec h
  
  vec→heap' : {n : Rank} → (xs : Vec (Priorities × Value) n) → priorityQueue n
  vec→heap' xs = Data.Vec.foldl priorityQueue insert emp xs

  heap→vec' : {n : Rank} → (h : priorityQueue n) → Vec (Priorities × Value) n
  heap→vec' {zero} h = []
  heap→vec' {suc n} h = peek h ∷ (heap→vec' (pop h))

  heap→vecp : {n : Rank} → (h : priorityQueue n) → Vec Priorities n
  heap→vecp h = Data.Vec.map proj₁ (heap→vec' h)

  module _ where
    private
      variable
        m n : ℕ

    data SortedVec : Vec (Priorities × Value) n → Set where
      []-sorted : SortedVec []
      [a]-sorted : {pv : Priorities × Value} → SortedVec (pv ∷ [])
      [a≤b]-sorted : {rest : Vec (Priorities × Value) m}
                  → {pv₁ pv₂ : Priorities × Value}
                  → proj₁ pv₁ ≤ᵖ proj₁ pv₂ 
                  → SortedVec (pv₂ ∷ rest)
                  → SortedVec (pv₁ ∷ pv₂ ∷ rest)

    -- If we pop all elements from a heap into a vector, that vector will be sorted
    -- according to the priorities of the elements in the heap (thanks to pop-≤).
    heap→vec-Sorted : (h : priorityQueue n) → SortedVec (heap→vec' h)
    heap→vec-Sorted {zero} h = []-sorted
    heap→vec-Sorted {suc zero} h = [a]-sorted
    heap→vec-Sorted {suc (suc n)} h = [a≤b]-sorted (pop-≤ h) (heap→vec-Sorted (pop h))

    -- x π y ⇔ x is a permutation of y, where x and y are vectors of the same lengths
    -- Adapted from: Data.List.Relation.Binary.Permutation.Propositional
    PV = Priorities × Value
    data _π_ : Vec (PV) n → Vec (PV) n → Set (l₁ ⊔ l₂) where
      refl : {xs : Vec (PV) n}               → xs π xs
      prep : {xs ys : Vec (PV) n} (x : PV)   → xs π ys → (x ∷ xs) π (x ∷ ys)
      swap : {xs ys : Vec (PV) n} (x y : PV) → xs π ys → (x ∷ y ∷ xs) π (y ∷ x ∷ ys)
      tran : {xs ys zs : Vec (PV) n}         → xs π ys → ys π zs → xs π zs

    -- Popping all elements from a heap created from a list of elements should give
    -- back a permutation of the initial list.
    postulate  -- TODO temporary postulate because of import errors
      vec→heap→vec-Permutation : (xs : Vec (Priorities × Value) n) 
                                → (heap→vec' (vec→heap xs)) π xs
      -- vec→heap→vec-Permutation xs = {!   !}

    -- This is an alternative to the Permutation π property.
    -- Proof that any given element from a vector will survive insertion and popping.
    -- Hence the output vector is a permutation of the input vector.
    vec→heap→vec-alt : (xs : Vec (Priorities × Value) n)
                      → (pv : Priorities × Value)
                      → pv [∈] xs
                      → pv [∈] (heap→vec (vec→heap xs))
    vec→heap→vec-alt xs pv q = ∈ʰ⇒[∈]-lemma (vec→heap xs) pv ([∈]⇒∈ʰ-lemma xs pv q)

    -- This is the ultimate goal: inserting a list of pairs and then emptying out the heap
    -- should result in a sorted list which is a permutation of the input list.
    priorityQueue-lemma : (xs : Vec (Priorities × Value) n)
                        → SortedVec (heap→vec' (vec→heap xs)) × (heap→vec' (vec→heap xs)) π xs
    priorityQueue-lemma xs = (heap→vec-Sorted (vec→heap xs)) , (vec→heap→vec-Permutation xs)
    

  --DONE po popu dobim ven value, ostali ap majo vsi višjo piroriteto
  --DONE element se nahaja v vrsti
  --DONE ko dam v eno vrsto elemtov pa vse ven poberem, je na tem seznamu eden izmed the elemntov
  --DONE ko se lement nahaja v priorityQueue se pozneje nahaj tudi v listu po peekih
  --TODO ko je elemnt dveh dreves v merge se nahaja pozneje v drvesu

