{-# OPTIONS --sized-types #-}

module RankedPriorityQueue where

open import Ordering using (Priority; module ℕ-ordering) -- This is our file

open import Agda.Builtin.Bool using (Bool; false; true)

open import Level        renaming (zero to lzero; suc to lsuc)
open import Size
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-trans; ≤-total; suc-injective)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_; curry; uncurry)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (Vec; []; _∷_; head; tail)
open import Data.Vec.Relation.Unary.Unique.Setoid using (Unique)
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

  -- data _∈-priorityQueue_ (pv : Priorities × Value) : priorityQueue → Set where

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
  
    -- contains : {n : Rank} → priorityQueue n → Priorities × Value → Bool
    _∈-priorityQueue_ : {n : Rank} → (pv : Priorities × Value) → priorityQueue n → Set l₃

  -- Helper functions
  peekp : {n : Rank} → priorityQueue (suc n) → Priorities
  peekp h = proj₁ (peek h)

  peekv : {n : Rank} → priorityQueue (suc n) → Value
  peekv h = proj₂ (peek h)
  
  insertₙ : {n : Rank} → (xs : Vec (Priorities × Value) n) → priorityQueue n
  insertₙ xs = Data.Vec.foldl priorityQueue insert emp xs

  -- heap→vec : {n : Rank} → (h : priorityQueue n) → Vec (Priorities × Value) n
  -- heap→vec {zero} h = []
  -- heap→vec {suc n} h = peek h ∷ (heap→vec (pop h))
    
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

    -- Note: need at least two values to peek
    pop-≤ : {n : Rank} → (h : priorityQueue (suc (suc n)))
          → peekp h ≤ᵖ (peekp (pop h))

    insert-∈ : {n : Rank} → (h : priorityQueue n)
             → (pv : Priorities × Value) 
             → pv ∈-priorityQueue (insert h pv)
            -- → contains (insert h pv) pv ≡ true

    -- insert-∈-vec : {n : Rank} → (h : priorityQueue n)
    --              → (pv : Priorities × Value)
    --              → pv ∈-vec heap→vec (insert h pv)   

  --TODO po popu dobim ven value, ostali ap majo vsi višjo piroriteto
  --TODO element se nahaja v vrsti
  --TODO ko dam v eno vrsto elemtov pa vse ven poberem, je na tem seznamu eden izmed the elemntov
  --TODO ko se lement nahaja v priorityQueue se pozneje nahaj tudi v listu po peekih
  --TODO ko je elemnt dveh dreves v merge se nahaja pozneje v drvesu

  -- insertₙ-priorityQueue→vec : {n : Rank} 
  --   → (p : 1 ≤ n) 
  --   → (xs : {! Unique  !} (Vec (Priorities × Value) n)) -- Unique
  --   → priorityQueue→vec (insertₙ p xs) ≡ {!   !} -- Sorted xs


module VecPriorityQueueUnordered {l₁ l₂ : Level} 
                                  (Pr : Priority {l₁}) (Value : Set l₂) where
  
  open Priority Pr renaming (P to Priorities)
  open PriorityQueue

  data _∈_ {n : Rank} (pv : Priorities × Value) : Vec (Priorities × Value) n → Set (l₁ ⊔ l₂) where
    ∈-here  : (h : Vec (Priorities × Value) n) → pv ∈ h
    ∈-there : (h : Vec (Priorities × Value) (suc n)) → pv ∈ (tail h)

  VecPriorityQueue : PriorityQueue Pr Value
  VecPriorityQueue = record { 
    priorityQueue = priorityQueue-aux ;
     emp = [] ;
     insert = insert-aux ;
     peek = peek-aux ;
     pop = pop-aux ;
     _∈-priorityQueue_ = _∈_ ;
     insert₁-peek = insert₁-peek-aux ;
     insert₁-pop = insert₁-pop-aux ; 
     insert₂-peek-p₁≤p₂ = insert₂-peek-p₁≤p₂-aux ;
     insert₂-peek-p₂≤p₁ = insert₂-peek-p₂≤p₁-aux ;
     insert₂-pop-p₁≤p₂ = insert₂-pop-p₁≤p₂-aux ;
     insert₂-pop-p₂≤p₁ = insert₂-pop-p₂≤p₁-aux ;
     pop-≤ = pop-≤-aux ; 
     insert-∈ = insert-∈-aux}
     
    where 
      priorityQueue-aux : Rank → Set (l₁ ⊔ l₂)
      priorityQueue-aux = λ n → Vec (Priorities × Value) n

      insert-aux : {n : Rank} → Vec (Priorities × Value) n → Priorities × Value → Vec (Priorities × Value) (suc n)
      insert-aux xs pv = pv ∷ xs

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

      insert-∈-aux : {n : Rank} (h : priorityQueue-aux n)
                   → (pv : Priorities × Value) 
                   → pv ∈ insert-aux h pv
      insert-∈-aux h pv = ∈-here (insert-aux h pv)

-- Weight biased leftist heap
module MinHeap {l₁ l₂ l₃ : Level} 
               (Pr : Priority {l₁}) (Value : Set l₂) where
  
  open Priority Pr renaming (P to Priorities)
  open PriorityQueue      

  module _ where 
    open Data.Nat.Properties using (+-comm; +-assoc; +-suc)
    open Data.List using (foldl; foldr)
    open ℕ-ordering using (ℕ-priority)
    open Priority ℕ-priority renaming (cmp to ℕ-cmp; ≤ᵖ-total-lemma to ℕ-≤ᵖ-total-lemma)

    -- What follow are a bunch of trivial lemmas to assist Agda in being a proof assistant...
    -- TODO: the lemmas could be shortened by finding common patterns...
    
    lemma-i≡i+0 : {i : Rank} → i ≡ (i + zero)
    lemma-i≡i+0 {i} = sym (+-comm i zero)

    lemma-i+1≡suci : {i : Rank} → (i + 1) ≡ (suc i)
    lemma-i+1≡suci {i} = +-comm i 1

    -- lemma-+-sucₙ' is a generalization of lemma-+-sucₙ
    -- Both are a generalization of lemma-1aa to n elements
    lemma-+-sucₙ' : (a s : ℕ) → (xs : List ℕ) → a + suc (foldl _+_ s xs) ≡ suc (foldl _+_ a (s ∷ xs))
    lemma-+-sucₙ' a s [] = +-suc a s
    lemma-+-sucₙ' a s (x ∷ xs) = 
      begin 
        a + suc (foldl _+_ (s + x) xs)   ≡⟨ lemma-+-sucₙ' a (s + x) xs ⟩ 
        suc (foldl _+_ (a + (s + x)) xs) ≡⟨ cong suc (cong (λ y → foldl _+_ y xs) (sym (+-assoc a s x))) ⟩
        suc (foldl _+_ (a + s + x) xs)
        ∎

    -- This is lemma-+-sucₙ' with the additional proof that a + 0 = a 
    lemma-+-sucₙ : (a : ℕ) → (xs : List ℕ) → a + suc (foldl _+_ 0 xs) ≡ suc (foldl _+_ 0 (a ∷ xs))
    lemma-+-sucₙ a xs = 
      begin
        a + suc (foldl _+_ 0 xs)   ≡⟨ lemma-+-sucₙ' a 0 xs ⟩
        suc (foldl _+_ (a + 0) xs) ≡⟨ cong suc (cong (λ x → foldl _+_ x xs) (+-comm a 0)) ⟩
        suc (foldl _+_ a xs)
        ∎

    lemma-1aa : (b c d : Rank) → (b + suc (c + d)) ≡ suc (b + c + d)
    lemma-1aa b c d =
      begin b + suc (c + d) ≡⟨ +-suc b (c + d) ⟩ 
        suc (b + (c + d)) ≡⟨ cong suc (sym (+-assoc b c d)) ⟩
        suc (b + c + d) 
        ∎

    lemma-1a : (a b c d : Rank) → 
              (a + (b + suc (c + d))) ≡ suc (a + b + c + d)
    lemma-1a a b c d = 
      begin 
        a + (b + suc (c + d)) ≡⟨ cong (a +_) (lemma-+-sucₙ b (c ∷ d ∷ [])) ⟩ 
        a + suc (b + c + d)   ≡⟨ lemma-+-sucₙ a (b ∷ c ∷ d ∷ []) ⟩ 
        suc (a + b + c + d) 
        ∎

    lemma-1b : (a b c d : Rank) →
              (a + b + suc (c + d)) ≡ suc (a + b + c + d)
    lemma-1b a b c d = 
      begin
        a + b + suc (c + d)   ≡⟨ +-assoc a b (suc (c + d)) ⟩ 
        a + (b + suc (c + d)) ≡⟨ lemma-1a a b c d ⟩ 
        suc (a + b + c + d)
        ∎

    -- For merge case 1
    lemma-1 : (a b c d : Rank) → 
              suc (a + (b + suc (c + d))) ≡ suc (a + b + suc (c + d))
    lemma-1 a b c d = cong suc 
      (trans 
        (lemma-1a a b c d) 
        (sym 
          (lemma-1b a b c d)))

    lemma-2a : (a b c : Rank) → a + (b + suc c) ≡ suc (a + b + c)
    lemma-2a a b c = 
      begin 
        a + (b + suc c) ≡⟨ cong (a +_) (lemma-+-sucₙ b (c ∷ [])) ⟩ 
        a + suc (b + c) ≡⟨ lemma-+-sucₙ a (b ∷ c ∷ []) ⟩ 
        suc (a + b + c)
        ∎

    lemma-2b : (a b c : Rank) → a + b + suc c ≡ suc (a + b + c)
    lemma-2b a b c = 
      begin
        a + b + suc c   ≡⟨ +-assoc a b (suc c) ⟩ 
        a + (b + suc c) ≡⟨ lemma-2a a b c ⟩ 
        suc (a + b + c) 
        ∎

    -- For merge case 2
    lemma-2 : (a b c d : Rank) → 
              suc (a + suc (b + c) + d) ≡ suc (d + a + suc (b + c))
    lemma-2 a b c d = cong suc
      (begin 
        a + suc (b + c) + d ≡⟨ cong (_+ d) (lemma-1aa a b c) ⟩ 
        suc (a + b + c) + d ≡⟨ +-comm (suc (a + b + c)) d ⟩ 
        d + suc (a + b + c) ≡⟨ lemma-+-sucₙ d (a ∷ b ∷ c ∷ []) ⟩ 
        suc (d + a + b + c) ≡⟨ cong suc (+-assoc (d + a) b c) ⟩ 
        suc (d + a + (b + c)) ≡⟨ sym (lemma-2b d a (b + c)) ⟩ 
        d + a + suc (b + c)
        ∎)
        
      -- (begin
      --   a + suc b+c + d   ≡⟨ +-comm (a + suc b+c) d ⟩ 
      --   d + (a + suc b+c) ≡⟨ lemma-2a d a b+c ⟩ 
      --   suc (d + a + b+c) ≡⟨ sym (lemma-2b d a b+c) ⟩ 
      --   d + a + suc b+c
      --   ∎)

    lemma-3a : (a b c d : Rank) → a + b + c + d ≡ c + d + a + b
    lemma-3a a b c d = 
      begin
        a + b + c + d     ≡⟨ +-assoc (a + b) c d ⟩ 
        (a + b) + (c + d) ≡⟨ +-comm (a + b) (c + d) ⟩ 
        (c + d) + (a + b) ≡⟨ sym (+-assoc (c + d) a b) ⟩
        c + d + a + b
        ∎

    -- For merge case 3
    lemma-3 : (a b c d : Rank) →
              suc (a + (b + suc (c + d))) ≡ suc (c + d + suc (a + b))
    lemma-3 a b c d = cong suc 
      (begin 
        a + (b + suc (c + d)) ≡⟨ lemma-1a a b c d ⟩ 
        suc (a + b + c + d) ≡⟨ cong suc (lemma-3a a b c d) ⟩
        suc (c + d + a + b) ≡⟨ sym (lemma-1b c d a b) ⟩ 
        c + d + suc (a + b)
        ∎)

    lemma-4a : (a b c d : Rank) →
               a + suc (b + c) + d ≡ suc (a + b + c + d)
    lemma-4a a b c d = 
      begin
        a + suc (b + c) + d ≡⟨ cong (_+ d) (lemma-+-sucₙ a (b ∷ c ∷ [])) ⟩ 
        suc (a + b + c) + d ≡⟨ refl ⟩ 
        suc (a + b + c + d)
        ∎

    lemma-4b : (a b c d : Rank) →
               a + b + c + d ≡ b + c + d + a
    lemma-4b a b c d =
      begin
        a + b + c + d ≡⟨ +-assoc (a + b) c d ⟩ 
        (a + b) + (c + d) ≡⟨ +-assoc a b (c + d) ⟩ 
        a + (b + (c + d)) ≡⟨ +-comm a (b + (c + d)) ⟩ 
        (b + (c + d)) + a  ≡⟨ cong (_+ a) (sym (+-assoc b c d)) ⟩ 
        b + c + d + a
        ∎
      
    -- For merge case 4
    lemma-4 : (a b c d : Rank) → 
              suc (a + suc (b + c) + d) ≡ suc (b + c + suc (d + a))
    lemma-4 a b c d = cong suc 
      (begin 
        a + suc (b + c) + d ≡⟨ lemma-4a a b c d ⟩ 
        suc (a + b + c + d) ≡⟨ cong suc (lemma-4b a b c d) ⟩ 
        suc (b + c + d + a) ≡⟨ sym (lemma-1b b c d a) ⟩ 
        b + c + suc (d + a)
        ∎)

    lemma-a : (a b c : Rank) → a + b + c ≡ a + (b + c)
    lemma-a a b c = +-assoc a b c

    lemma-b : (a b c : Rank) → a + b + c ≡ (b + c) + a
    lemma-b a b c = 
      begin
        a + b + c ≡⟨ lemma-a a b c ⟩ 
        a + (b + c) ≡⟨ +-comm a ((b + c)) ⟩ 
        (b + c) + a
        ∎

    lemma-c : (a b c : Rank) → a + suc (b + c) ≡ suc (b + (c + a))
    lemma-c a b c = 
      begin
        a + suc (b + c) ≡⟨ lemma-1aa a b c ⟩ 
        suc (a + b + c) ≡⟨ cong suc (lemma-b a b c) ⟩
        suc (b + c + a) ≡⟨ cong suc (lemma-a b c a) ⟩ 
        suc (b + (c + a)) ∎

    lemma-d : (a b c : Rank) → a + suc (b + c) ≡ suc (c + a + b)
    lemma-d a b c =
      begin 
        a + suc (b + c) ≡⟨ lemma-c a b c ⟩ 
        suc (b + (c + a)) ≡⟨ cong suc (+-comm b (c + a)) ⟩ 
        suc (c + a + b) ∎

    data Heap {i : Size} : Rank → Set (l₁ ⊔ l₂) where
      empty : Heap zero
      node  : {i₁ i₂ : Size< i}
            {nₗ nᵣ n : ℕ} 
            → nᵣ ≤ nₗ 
            → n ≡ suc (nₗ + nᵣ)
            → Priorities × Value 
            → Heap {i₁} nₗ 
            → Heap {i₂} nᵣ 
            → Heap {i} n 
            
    rank : {i : Rank} → Heap i → Rank
    rank {i} h = i

    -- TODO: remove sized types, check ranks {n₁,...}

    -- Note: subst is needed to help Agda
    -- Note: Heap contains Size parameter because otherwise Agda complains about termination checking errors!
    --       {_} are there to eat up Size
    merge : {i j : Size} → {nₗ nᵣ : Rank} → (l : Heap {i} nₗ) → (r : Heap {j} nᵣ) → Heap (nₗ + nᵣ)
    merge empty r = r
    merge {_} {_} {suc nₗ} {zero} l empty = subst Heap (cong suc lemma-i≡i+0) l
    merge {_} {_} {nₗ} {nᵣ} 
      (node {_} {_} {nₗₗ} {nₗᵣ} {nₗ} nₗᵣ≤nₗₗ nₗ≡1+nₗₗ+nₗᵣ (p₁ , v₁) ll lr) 
      (node {_} {_} {nᵣₗ} {nᵣᵣ} {nᵣ} nᵣᵣ≤nᵣₗ nᵣ≡1+nᵣₗ+nᵣᵣ (p₂ , v₂) rl rr)
        with cmp p₁ p₂ 
          | ℕ-cmp (nₗᵣ + nᵣ) nₗₗ 
          | ℕ-cmp (nᵣᵣ + nₗ) nᵣₗ
    ... | le p₁≤p₂ | le nₗᵣ+nᵣ≤nₗ | _ rewrite nₗ≡1+nₗₗ+nₗᵣ = node nₗᵣ+nᵣ≤nₗ (cong suc (lemma-a nₗₗ nₗᵣ nᵣ)) ((p₁ , v₁)) ll (merge lr (node nᵣᵣ≤nᵣₗ nᵣ≡1+nᵣₗ+nᵣᵣ ((p₂ , v₂)) rl rr))
    ... | le p₁≤p₂ | gt nₗᵣ+nᵣ>nₗ | _ rewrite nₗ≡1+nₗₗ+nₗᵣ = node (ℕ-≤ᵖ-total-lemma nₗᵣ+nᵣ>nₗ) (cong suc (lemma-b nₗₗ nₗᵣ nᵣ)) ((p₁ , v₁)) ((merge lr (node nᵣᵣ≤nᵣₗ nᵣ≡1+nᵣₗ+nᵣᵣ ((p₂ , v₂)) rl rr))) ll
    ... | gt p₁>p₂ | _ | le n₂₂+nₗ≤nᵣₗ rewrite nᵣ≡1+nᵣₗ+nᵣᵣ = node n₂₂+nₗ≤nᵣₗ (lemma-c nₗ nᵣₗ nᵣᵣ) ((p₂ , v₂)) rl (merge rr (node nₗᵣ≤nₗₗ nₗ≡1+nₗₗ+nₗᵣ ((p₁ , v₁)) ll lr))
    ... | gt p₁>p₂ | _ | gt n₂₂+nₗ>nᵣₗ rewrite nᵣ≡1+nᵣₗ+nᵣᵣ = node (ℕ-≤ᵖ-total-lemma n₂₂+nₗ>nᵣₗ) (lemma-d nₗ nᵣₗ nᵣᵣ) ((p₂ , v₂)) ((merge rr (node nₗᵣ≤nₗₗ nₗ≡1+nₗₗ+nₗᵣ ((p₁ , v₁)) ll lr))) rl
          
    singleton : Priorities × Value → Heap 1
    singleton pv = node z≤n refl pv empty empty

    data _∈_ {n : Rank} (pv : Priorities × Value) : Heap n → Set (l₁ ⊔ l₂) where
       ∈-here  : {nₗ nᵣ : Rank} (l : Heap nₗ) (r : Heap nᵣ) (proof₁ : nᵣ ≤ nₗ) (proof₂ : n ≡ suc (nₗ + nᵣ)) → pv ∈ node proof₁ proof₂ pv l r
       ∈-left  : {nₗ nᵣ : Rank} (l : Heap nₗ) (r : Heap nᵣ) (proof₁ : nᵣ ≤ nₗ) (proof₂ : n ≡ suc (nₗ + nᵣ)) (pv₂ : Priorities × Value) → pv₂ ∈ l → pv ∈ node proof₁ proof₂ pv₂ l r
       ∈-right : {nₗ nᵣ : Rank} (l : Heap nₗ) (r : Heap nᵣ) (proof₁ : nᵣ ≤ nₗ) (proof₂ : n ≡ suc (nₗ + nᵣ)) (pv₂ : Priorities × Value) → pv₂ ∈ r → pv ∈ node proof₁ proof₂ pv₂ l r

  MinHeapPriorityQueue : PriorityQueue Pr Value   
  MinHeapPriorityQueue = record { 
    priorityQueue = priorityQueue-aux ;
    emp = empty ;
    insert = insert-aux;
    peek = peek-aux ;
    pop = pop-aux ;
    _∈-priorityQueue_ = _∈_ ;
    insert₁-peek = insert₁-peek-aux ;
    insert₁-pop = insert₁-pop-aux ; 
    insert₂-peek-p₁≤p₂ = insert₂-peek-p₁≤p₂-aux ;
    insert₂-peek-p₂≤p₁ = insert₂-peek-p₂≤p₁-aux ;
    insert₂-pop-p₁≤p₂ = insert₂-pop-p₁≤p₂-aux ;
    insert₂-pop-p₂≤p₁ = insert₂-pop-p₂≤p₁-aux ;
    pop-≤ = {!   !} ; 
    insert-∈ = insert-∈-aux}

    where
      priorityQueue-aux : Rank → Set (l₁ ⊔ l₂)
      priorityQueue-aux = λ n → Heap n

      peek-aux : {n : Rank} → Heap (suc n) → Priorities × Value
      peek-aux (node _ _ pv _ _) = pv

      pop-aux : {n : Rank} → Heap (suc n) → Heap n
      pop-aux (node _ p _ l r) = subst Heap (suc-injective (sym p)) (merge  l r)

      insert-aux : {n : Rank} → Heap n → Priorities × Value → Heap (suc n)
      insert-aux = λ h pv → subst Heap lemma-i+1≡suci ((merge  h (singleton pv)))

      insert₁-peek-aux : ((p , v) : Priorities × Value) →
                         peek-aux (merge  empty (singleton (p , v))) ≡ (p , v)
      insert₁-peek-aux (p , v) = refl

      insert₁-pop-aux : (pv : Priorities × Value) → pop-aux (insert-aux empty pv) ≡ empty
      insert₁-pop-aux x = refl

      insert₂-peek-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → peek-aux (merge  (merge  empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ (p₁ , v₁)
      insert₂-peek-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₁ p₂ 
      ... | le _ = refl
      ... | gt p₁>p₂ = ⊥-elim (p₁>p₂ p₁≤p₂)

      insert₂-peek-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂
                  → peek-aux (merge  (merge  empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ (p₂ , v₂)
      insert₂-peek-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₁ p₂ 
      ... | le p₁≤p₂ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
      ... | gt _ = refl

      insert₂-pop-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₁ ≤ᵖ p₂
                  → p₁ ≢ p₂
                  → pop-aux (merge  (merge  empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ singleton (p₂ , v₂)
      insert₂-pop-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₁ p₂ 
      ... | le p₁≤p₂ = refl
      ... | gt p₂>p₁ = ⊥-elim (p₂>p₁ p₁≤p₂)

      insert₂-pop-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                  → p₂ ≤ᵖ p₁
                  → p₁ ≢ p₂
                  → pop-aux (merge  (merge  empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ singleton (p₁ , v₁)
      insert₂-pop-p₂≤p₁-aux (p₁ , v₁) (p₂ , v₂) p₂≤p₁ p₁≢p₂ with cmp p₁ p₂ 
      ... | le p₁≤p₂ = ⊥-elim (p₁≢p₂ (≤ᵖ-antisym p₁≤p₂ p₂≤p₁))
      ... | gt _ = refl


      insert-∈-aux : {n : Rank} (h : priorityQueue-aux n)
                   → (pv : Priorities × Value) 
                   → pv ∈ insert-aux h pv
      insert-∈-aux empty pv = ∈-here empty empty z≤n refl
      insert-∈-aux (node proof₁ proof₂ (pₙ , vₙ) h h₁) (p , v) with cmp' p pₙ
      insert-∈-aux (node proof₁ proof₂ (pₙ , vₙ) h h₁) (p , v) | a<b x x₁ = {!   !}
      insert-∈-aux (node proof₁ proof₂ (pₙ , vₙ) h h₁) (p , v) | a=b p≡pₙ = {!   !}  --how to compare values ??
      insert-∈-aux (node proof₁ proof₂ (pₙ , vₙ) h h₁) (p , v) | a>b x x₁ = {!   !}
   