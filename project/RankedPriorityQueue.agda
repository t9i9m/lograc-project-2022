{-# OPTIONS --sized-types #-}

module RankedPriorityQueue where

open import Ordering using (Priority; module ℕ-ordering) -- This is our file

open import Level        renaming (zero to lzero; suc to lsuc)
open import Size
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


Rank : Set
Rank = ℕ


data Dec {l : Level} (A : Set l) : Set l where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A


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


    --TODO po popu dobim ven value, ostali ap majo vsi višjo piroriteto
    --TODO ko dam v eno vrsto elemtov pa vse ven poberem, je na tem seznamu eden izmed the elemntov
    --TODO ko je elemnt dveh dreves v merge se nahaja pozneje v drvesu
    --TODO element se nahaja v vrsti
    --TODO ko se lement nahaja v priorityQueue se pozneje nahaj tudi v listu po peekih
    
    -- insertₙ-peekₙ : (xs : List (Priorities × Value))
    --               → Unique xs
    --               → heap→list (list→heap xs) ≡ Sorted xs
  
  insertₙ : {n : ℕ} → (xs : Vec (Priorities × Value) n) → priorityQueue n
  insertₙ xs = Data.Vec.foldl priorityQueue insert emp xs

  heap→vec : {n : Rank} → (h : priorityQueue n) → Vec (Priorities × Value) n
  heap→vec {zero} h = []
  heap→vec {suc n} h = peek h ∷ (heap→vec (pop h))


module VecPriorityQueueUnordered {l₁ l₂ : Level} 
                                  (Pr : Priority {l₁}) (Value : Set l₂) where
  
  open Priority Pr renaming (P to Priorities)
  open PriorityQueue

  VecPriorityQueue : PriorityQueue Pr Value
  VecPriorityQueue = record { 
    priorityQueue = λ n → Vec (Priorities × Value) n ;
     emp = [] ;
     insert = insert-aux ;
     peek = peek-aux ;
     pop = pop-aux ;
     insert₁-peek = insert₁-peek-aux ;
     insert₁-pop = insert₁-pop-aux ; 
     insert₂-peek-p₁≤p₂ = insert₂-peek-p₁≤p₂-aux ;
     insert₂-peek-p₂≤p₁ = insert₂-peek-p₂≤p₁-aux ;
     insert₂-pop-p₁≤p₂ = insert₂-pop-p₁≤p₂-aux ;
     insert₂-pop-p₂≤p₁ = insert₂-pop-p₂≤p₁-aux }
     
    where 
      insert-aux : {n : Rank} → Vec (Priorities × Value) n → Priorities × Value → Vec (Priorities × Value) (suc n)
      insert-aux xs pv = pv ∷ xs

      peek-aux : {n : Rank} → Vec (Priorities × Value) (suc n) → Priorities × Value
      peek-aux ((p , v) ∷ []) = (p , v)
      peek-aux ((p , v) ∷ x ∷ xs) with peek-aux (x ∷ xs)
      peek-aux ((p , v) ∷ x ∷ xs) | p' , v' with cmp p p' 
      peek-aux ((p , v) ∷ x ∷ xs) | p' , v' | le _ = (p , v)
      peek-aux ((p , v) ∷ x ∷ xs) | p' , v' | gt _ = (p' , v')

      pop-aux : {n : Rank} → Vec (Priorities × Value) (suc n) → Vec (Priorities × Value) n
      pop-aux ((p , v) ∷ []) = []
      pop-aux ((p , v) ∷ x ∷ xs) with peek-aux (x ∷ xs)
      pop-aux ((p , v) ∷ x ∷ xs) | (p' , v') with cmp p p'
      pop-aux ((p , v) ∷ x ∷ xs) | p' , v' | le _ = (x ∷ xs)
      pop-aux ((p , v) ∷ x ∷ xs) | p' , v' | gt _ = (p , v) ∷ pop-aux (x ∷ xs)
      
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

-- Weight biased leftist heap
module MinHeap {l₁ l₂ l₃ : Level} 
               (Pr : Priority {l₁}) (Value : Set l₂) where
  
  open Priority Pr renaming (P to Priorities)
  open PriorityQueue      

  module _ where 
    open Data.Nat.Properties using (+-comm; +-assoc)
    open ℕ-ordering using (ℕ-priority)
    open Priority ℕ-priority renaming (cmp to ℕ-cmp)

    data Heap : Rank → Set (l₁ ⊔ l₂) where
      empty : Heap zero
      node  : {r₁ r₂ : ℕ} 
            → r₂ ≤ r₁ 
            → Priorities × Value 
            → Heap r₁ 
            → Heap r₂ 
            → Heap (suc (r₁ + r₂))  

    -- data Heap {i : Size} : Set (l₁ ⊔ l₂) where 
    --   empty : Heap
    --   node  : {i₁ i₂ : Size< i} → Rank → Priorities × Value 
    --             → (l : Heap {i₁}) → (r : Heap {i₂}) → Heap

    lemma-i≡i+0 : {i : Rank} → i ≡ (i + zero)
    lemma-i≡i+0 {i} = sym (+-comm i zero)

    lemma-i+1≡suci : {i : Rank} → (i + 1) ≡ (suc i)
    lemma-i+1≡suci {i} = +-comm i 1

    lemma-1 : (a b c d : Rank) → 
              suc (a + (b + suc (c + d))) ≡ suc (a + b + suc (c + d))
    lemma-1 a b c d = cong suc (+-assoc {! !} {!   !} {!   !})

    rank : {i : Rank} → Heap i → Rank
    rank {i} h = i

    merge : {n₁ n₂ : Rank} → (l : Heap n₁) → (r : Heap n₂) → Heap (n₁ + n₂)
    merge empty r = r
    merge l empty = subst Heap lemma-i≡i+0 l
    merge {n₁} {n₂} (node {nₗ₁} {nᵣ₁} r₁≤l₁ (p₁ , v₁) l₁ r₁) (node {nₗ₂} {nᵣ₂} r₂≤l₂ (p₂ , v₂) l₂ r₂)
      with cmp p₁ p₂ 
      | ℕ-cmp (nᵣ₁ + n₂) nₗ₁ 
      | ℕ-cmp (nᵣ₂ + n₁) nₗ₂
    ... | le p₁≤p₂ | le r₁+n₂≤n₁ | _ = subst Heap 
                                            (lemma-1 nₗ₁ nᵣ₁ nₗ₂ nᵣ₂) 
                                            (node r₁+n₂≤n₁ (p₁ , v₁) l₁ (merge r₁ (node r₂≤l₂ (p₂ , v₂) l₂ r₂)))
    ... | le p₁≤p₂ | gt r₁+n₂>n₁ | _ = {!   !}
    ... | gt x | q | r = {!   !}

          
    -- merge empty r = r
    -- merge l empty = l
    -- merge (node s₁ (p₁ , v₁) l₁ r₁) (node s₂ (p₂ , v₂) l₂ r₂) 
    --   with cmp p₁ p₂ 
    --       | ℕ-cmp (rank r₁ + s₂) (rank l₁) 
    --       | ℕ-cmp (rank r₂ + s₁) (rank l₂)
    -- ... | le _ | le _ | _    = node (s₁ + s₂) (p₁ , v₁) l₁ (merge r₁ (node s₂ (p₂ , v₂) l₂ r₂))
    -- ... | le _ | gt _ | _    = node (s₁ + s₂) (p₁ , v₁) (merge r₁ (node s₂ (p₂ , v₂) l₂ r₂)) l₁
    -- ... | gt _ | _    | le _ = node (s₁ + s₂) (p₂ , v₂) l₂ (merge r₂ (node s₁ (p₁ , v₁) l₁ r₁))
    -- ... | gt _ | _    | gt _ = node (s₁ + s₂) (p₂ , v₂) (merge r₂ (node s₁ (p₁ , v₁) l₁ r₁)) l₂

    singleton : Priorities × Value → Heap 1
    singleton pv = node z≤n pv empty empty

  MinHeapPriorityQueue : PriorityQueue Pr Value   
  MinHeapPriorityQueue = record { 
    priorityQueue = λ n → Heap n ;
    emp = empty ;
    insert = λ h pv → subst Heap lemma-i+1≡suci ((merge h (singleton pv))) ;
    peek = peek-aux ;
    pop = pop-aux ;
    insert₁-peek = insert₁-peek-aux ;
    insert₁-pop = insert₁-pop-aux ; 
    insert₂-peek-p₁≤p₂ = insert₂-peek-p₁≤p₂-aux ;
    insert₂-peek-p₂≤p₁ = insert₂-peek-p₂≤p₁-aux ;
    insert₂-pop-p₁≤p₂ = {!   !} ;
    -- insert₂-pop-p₁≤p₂-aux ;
    insert₂-pop-p₂≤p₁ = {!   !} }
    -- insert₂-pop-p₂≤p₁-aux }

    where

      peek-aux : {n : Rank} → Heap (suc n) → Priorities × Value
      peek-aux (node _ pv _ _) = pv

      pop-aux : {n : Rank} → Heap (suc n) → Heap n
      pop-aux (node _ _ l r) = merge l r

      insert₁-peek-aux : ((p , v) : Priorities × Value) →
                         peek-aux (merge empty (singleton (p , v))) ≡ (p , v)
      insert₁-peek-aux (p , v) = refl

      insert₁-pop-aux : (pv : Priorities × Value) → empty ≡ empty
      insert₁-pop-aux x = refl

      insert₂-peek-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → peek-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ (p₁ , v₁)
      insert₂-peek-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₁ p₂ 
      ... | le _ = {! refl  !}
      ... | gt p₁>p₂ = ⊥-elim (p₁>p₂ p₁≤p₂)

      insert₂-peek-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂
                  → peek-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ (p₂ , v₂)
      insert₂-peek-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₁ p₂ 
      ... | le p₁≤p₂ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
      ... | gt _ = {! refl  !}

      -- insert₂-pop-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
      --             → p₁ ≤ᵖ p₂
      --             → p₁ ≢ p₂
      --             → pop-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ node 1 (p₂ , v₂) empty empty 
      -- insert₂-pop-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ = ?
      -- with cmp p₁ p₂ 
      -- ... | le p₁≤p₂ = refl
      -- ... | gt p₂>p₁ = ⊥-elim (p₂>p₁ p₁≤p₂)

      -- insert₂-pop-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
      --             → p₂ ≤ᵖ p₁
      --             → p₁ ≢ p₂
      --             → pop-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ node 1 (p₁ , v₁) empty empty 
      -- insert₂-pop-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₁ p₂ 
      -- ... | le p₁≤p₂ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
      -- ... | gt _ = refl
 