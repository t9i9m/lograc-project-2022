-- Weight biased leftist heap

open import Ordering using (Priority; module ℕ-ordering) -- This is our file
open import Level        renaming (zero to lzero; suc to lsuc)

module Ranked.Tree.LeftistHeap {l₁ l₂ l₃ : Level} (Pr : Priority {l₁}) (Value : Set l₂) where

open import Ranked.PriorityQueue
open import VecProperties
open import NatProperties
open Priority Pr renaming (P to Priorities)
open ℕ-ordering using (ℕ-priority)
open Priority ℕ-priority renaming (
  _≤ᵖ_ to _ℕ-≤ᵖ_; P to ℕ-P; ≤ᵖ-trans to ℕ-≤ᵖ-trans; ≤ᵖ-antisym to ℕ-≤ᵖ-antisym; ≤ᵖ-refl to ℕ-≤ᵖ-refl;
  ≤ᵖ-total-lemma to ℕ-≤ᵖ-total-lemma; ≤ᵖ-total to ℕ-≤ᵖ-total; ≤ᵖ-proj₁ to ℕ-≤ᵖ-proj₁; ≤ᵖ-proj₂ to ℕ-≤ᵖ-proj₂;
  cmp to ℕ-cmp; cmp' to ℕ-cmp')

open import Induction    using (RecStruct)
open import Induction.WellFounded using (Acc; acc; WfRec)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_; _≰_)
open import Data.Nat.Properties   using (suc-injective; +-comm; +-assoc; +-suc; 0≢1+n)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Data.Vec     using (Vec; []; _∷_)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary     using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)


data Heap : Rank → Set (l₁ ⊔ l₂) where
  empty : Heap zero
  node  : {nₗ nᵣ n : Rank} 
        → nᵣ ≤ nₗ 
        → n ≡ suc (nₗ + nᵣ)
        → Priorities × Value 
        → (Heap nₗ) × (Heap nᵣ)
        → Heap n 

data _∈_ {n : Rank} (pv : Priorities × Value) : Heap n → Set (l₁ ⊔ l₂) where
    ∈-here  : {nₗ nᵣ : Rank} (l : Heap nₗ) (r : Heap nᵣ) (proof₁ : nᵣ ≤ nₗ) (proof₂ : n ≡ suc (nₗ + nᵣ)) → pv ∈ node proof₁ proof₂ pv (l , r)
    ∈-left  : {nₗ nᵣ : Rank} (l : Heap nₗ) (r : Heap nᵣ) (proof₁ : nᵣ ≤ nₗ) (proof₂ : n ≡ suc (nₗ + nᵣ)) (pv₂ : Priorities × Value) → pv ∈ l → pv ∈ node proof₁ proof₂ pv₂ (l , r)
    ∈-right : {nₗ nᵣ : Rank} (l : Heap nₗ) (r : Heap nᵣ) (proof₁ : nᵣ ≤ nₗ) (proof₂ : n ≡ suc (nₗ + nᵣ)) (pv₂ : Priorities × Value) → pv ∈ r → pv ∈ node proof₁ proof₂ pv₂ (l , r)

rank : {i : Rank} → Heap i → Rank
rank {i} h = i

data _<'_ (m : (Rank × Rank)): (Rank × Rank) → Set l₃ where
  <'-stepsl : m <' ((suc (proj₁ m)) , proj₂ m)
  <'-stepsr : m <' (proj₁ m , (suc (proj₂ m)))
  <'-stepl  : ∀ {nₗ} (m<nₗ : m <' (nₗ , proj₂ m)) → m <' ((suc nₗ) , proj₂ m)
  <'-stepr  : ∀ {nᵣ} (m<nᵣ : m <' (proj₁ m , nᵣ)) → m <' (proj₁ m , (suc nᵣ))
  <'-step   : ∀ {nₗ nᵣ} (m<nn : m <' (nₗ , nᵣ))   → m <' ((suc nₗ) , (suc nᵣ))

Well-founded : ∀ {a} {A : Set} → Rel A a → Set a
Well-founded _<_ = ∀ x → Acc _<_ x

<'-Rec : RecStruct (Rank × Rank) l₃ _
<'-Rec = WfRec _<'_

mutual

  <'-well-founded : Well-founded _<'_
  <'-well-founded' : ∀ n → <'-Rec (Acc _<'_) n

  <'-well-founded n = acc (<'-well-founded' n)

  <'-well-founded' .(suc (proj₁ m) , proj₂ m) m <'-stepsl = <'-well-founded m
  <'-well-founded' .(proj₁ m , suc (proj₂ m)) m <'-stepsr = <'-well-founded m
  <'-well-founded' .(suc _ , proj₂ m) m (<'-stepl a) = <'-well-founded' (_ , proj₂ m) m a
  <'-well-founded' .(proj₁ m , suc _) m (<'-stepr a) = <'-well-founded' (proj₁ m , _) m a
  <'-well-founded' .(suc _ , suc _) m (<'-step a) = <'-well-founded' (_ , _) m a

lemma-l : {nₗₗ nₗᵣ nₗ nᵣ : Rank} → (nₗ ≡ (1 + nₗₗ + nₗᵣ)) → ((nₗᵣ , nᵣ) <' (nₗ , nᵣ))
lemma-l {zero} {nₗᵣ} {nₗ} {nᵣ} p rewrite p = <'-stepsl
lemma-l {suc nₗₗ} {nₗᵣ} {suc nₗ} {nᵣ} p = <'-stepl (lemma-l (suc-injective p))

lemma-r : {nᵣₗ nᵣᵣ nₗ nᵣ : Rank} → (nᵣ ≡ (1 + nᵣₗ + nᵣᵣ)) → ((nₗ , nᵣᵣ) <' (nₗ , nᵣ))
lemma-r {zero} {nᵣᵣ} {nₗ} {nᵣ} p rewrite p = <'-stepsr
lemma-r {suc nᵣₗ} {nᵣᵣ} {nₗ} {suc nᵣ} p = <'-stepr (lemma-r (suc-injective p))

merge' : ∀ {nₗ nᵣ} → (rec : Acc _<'_ (nₗ , nᵣ)) → (l : Heap nₗ) → (r : Heap nᵣ) → Heap (nₗ + nᵣ)
merge' rec empty r = r
merge' rec l empty = subst Heap lemma-i≡i+0 l
merge' (acc rec)
  (node {nₗₗ} {nₗᵣ} {nₗ} nₗᵣ≤nₗₗ nₗ≡1+nₗₗ+nₗᵣ (p₁ , v₁) (ll , lr)) 
  (node {nᵣₗ} {nᵣᵣ} {nᵣ} nᵣᵣ≤nᵣₗ nᵣ≡1+nᵣₗ+nᵣᵣ (p₂ , v₂) (rl , rr))
    with cmp p₁ p₂ 
      | ℕ-cmp (nₗᵣ + nᵣ) nₗₗ 
      | ℕ-cmp (nₗ + nᵣᵣ) nᵣₗ -- Okasaki difference (before was (nᵣᵣ + nₗ))
... | le p₁≤p₂ | le nₗᵣ+nᵣ≤nₗₗ | _ = subst Heap (lemma-e nₗₗ nₗᵣ nᵣ nₗ (sym nₗ≡1+nₗₗ+nₗᵣ)) (node nₗᵣ+nᵣ≤nₗₗ (cong suc (lemma-a nₗₗ nₗᵣ nᵣ)) (p₁ , v₁) (ll , merge' (rec (nₗᵣ , nᵣ) (lemma-l nₗ≡1+nₗₗ+nₗᵣ)) lr (node nᵣᵣ≤nᵣₗ nᵣ≡1+nᵣₗ+nᵣᵣ (p₂ , v₂) (rl , rr))))
... | le p₁≤p₂ | gt nₗᵣ+nᵣ>nₗₗ | _ = subst Heap (lemma-e nₗₗ nₗᵣ nᵣ nₗ (sym nₗ≡1+nₗₗ+nₗᵣ)) (node (ℕ-≤ᵖ-total-lemma nₗᵣ+nᵣ>nₗₗ) (cong suc (lemma-b nₗₗ nₗᵣ nᵣ)) (p₁ , v₁) ((merge' (rec (nₗᵣ , nᵣ) (lemma-l nₗ≡1+nₗₗ+nₗᵣ)) lr (node nᵣᵣ≤nᵣₗ nᵣ≡1+nᵣₗ+nᵣᵣ (p₂ , v₂) (rl , rr))) , ll))
... | gt p₁>p₂ | _ | le nₗ+nᵣᵣ≤nᵣₗ = subst Heap (lemma-f nᵣₗ nᵣᵣ nₗ nᵣ (sym nᵣ≡1+nᵣₗ+nᵣᵣ)) (node nₗ+nᵣᵣ≤nᵣₗ (lemma-c nₗ nᵣₗ nᵣᵣ) (p₂ , v₂) (rl , (merge' (rec (nₗ , nᵣᵣ) (lemma-r nᵣ≡1+nᵣₗ+nᵣᵣ)) (node nₗᵣ≤nₗₗ nₗ≡1+nₗₗ+nₗᵣ (p₁ , v₁) (ll , lr)) rr)))
... | gt p₁>p₂ | _ | gt nₗ+nᵣᵣ>nᵣₗ = subst Heap (lemma-f nᵣₗ nᵣᵣ nₗ nᵣ (sym nᵣ≡1+nᵣₗ+nᵣᵣ)) (node (ℕ-≤ᵖ-total-lemma nₗ+nᵣᵣ>nᵣₗ) (lemma-d nₗ nᵣₗ nᵣᵣ) (p₂ , v₂) ((merge' (rec (nₗ , nᵣᵣ) (lemma-r nᵣ≡1+nᵣₗ+nᵣᵣ)) (node nₗᵣ≤nₗₗ nₗ≡1+nₗₗ+nₗᵣ (p₁ , v₁) (ll , lr)) rr) , rl))

merge : {nₗ nᵣ : Rank} → (l : Heap nₗ) → (r : Heap nᵣ) → Heap (nₗ + nᵣ)
merge l r = merge' ((<'-well-founded (rank l , rank r))) l r

singleton : Priorities × Value → Heap 1
singleton pv = node z≤n refl pv (empty , empty)

MinHeapPriorityQueue : PriorityQueue Pr Value   
MinHeapPriorityQueue = record { 
  priorityQueue = priorityQueue-aux ;
  emp = empty ;
  insert = insert-aux;
  peek = peek-aux ;
  pop = pop-aux ;
  _∈ʰ_ = _∈_ ;
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
  insert-[∈] = {!insert-[∈]-aux!} ;
  insert-preserves-∈ = {!insert-preserves-∈-aux!} ;
  [∈]⇒∈ʰ-lemma = {![∈]⇒∈ʰ-lemma-aux!} ;
  ∈ʰ⇒[∈]-lemma = {!∈ʰ⇒[∈]-lemma-aux!} }

  where
    priorityQueue-aux : Rank → Set (l₁ ⊔ l₂)
    priorityQueue-aux = λ n → Heap n

    insert-aux : {n : Rank} → Heap n → Priorities × Value → Heap (suc n)
    insert-aux = λ h pv → subst Heap lemma-i+1≡suci ((merge h (singleton pv)))

    peek-aux : {n : Rank} → Heap (suc n) → Priorities × Value
    peek-aux (node _ _ pv _) = pv

    pop-aux : {n : Rank} → Heap (suc n) → Heap n
    pop-aux (node _ p _ (l , r)) = subst Heap (suc-injective (sym p)) (merge l r)

    vec→heap-aux : {n : Rank} → Vec (Priorities × Value) n → priorityQueue-aux n
    vec→heap-aux xs = Data.Vec.foldl priorityQueue-aux insert-aux empty xs

    heap→vec-aux : {n : Rank} → priorityQueue-aux n → Vec (Priorities × Value) n
    heap→vec-aux {zero} h = []
    heap→vec-aux {suc n} h = peek-aux h ∷ (heap→vec-aux (pop-aux h))

    insert₁-peek-aux : ((p , v) : Priorities × Value) →
                        peek-aux (merge empty (singleton (p , v))) ≡ (p , v)
    insert₁-peek-aux (p , v) = refl

    insert₁-pop-aux : (pv : Priorities × Value) → pop-aux (insert-aux empty pv) ≡ empty
    insert₁-pop-aux x = refl

    insert₂-peek-p₁≤p₂-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                → p₁ ≤ᵖ p₂
                → p₁ ≢ p₂
                → peek-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ (p₁ , v₁)
    insert₂-peek-p₁≤p₂-aux (p₁ , v₁) (p₂ , v₂) p₁≤p₂ p₁≢p₂ with cmp p₁ p₂ 
    ... | le _ = refl
    ... | gt p₁>p₂ = ⊥-elim (p₁>p₂ p₁≤p₂)

    insert₂-peek-p₂≤p₁-aux : ((p₁ , v₁) (p₂ , v₂) : Priorities × Value) 
                → p₂ ≤ᵖ p₁
                → p₁ ≢ p₂
                → peek-aux (merge (merge empty (singleton (p₁ , v₁))) (singleton (p₂ , v₂))) ≡ (p₂ , v₂)
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
    
    -- pop-≤ is impossible to prove because Heap doesn't contain any priority ordering information.
    -- Priority ordering is imposed by insert, but here we just have a heap.
    pop-≤-aux : {n : Rank} (h : priorityQueue-aux (suc (suc n))) 
              → proj₁ (peek-aux h) ≤ᵖ proj₁ (peek-aux (pop-aux h))
    pop-≤-aux {zero} (node nᵣ≤nₗ x₁ (p , v) (l , r)) = {!   !}
    pop-≤-aux {suc n} h = {!   !}

    -- It would be useful to prove lemmas like this one
    ∈-merge-lemmaᵣ : {nₗ nᵣ : Rank} (l : Heap nₗ) (r : Heap nᵣ) 
                  → (pv : Priorities × Value)
                  → pv ∈ r
                  → pv ∈ merge l r
    ∈-merge-lemmaᵣ {nₗ} {nᵣ} l r pv pv∈r = {!   !}

    insert-∈-aux : {n : Rank} (h : priorityQueue-aux n) (pv : Priorities × Value) 
                  → pv ∈ insert-aux h pv
    insert-∈-aux {zero} empty pv = ∈-here empty empty z≤n refl
    insert-∈-aux {suc n} (node x x₁ (p₀ , v₀) (l , r)) (p , v) with cmp p₀ p
    insert-∈-aux {suc n} (node {nₗ} {nᵣ} x x₁ (p₀ , v₀) (l , r)) (p , v) | le p₀≤p with ℕ-cmp (nᵣ + 1) nₗ | merge r (singleton (p , v))
    insert-∈-aux {suc n} (node {nₗ} {nᵣ} x x₁ (p₀ , v₀) (l , r)) (p , v) | le p₀≤p | le nᵣ+1≤nₗ | q = {! ∈-right l q nᵣ+1≤nₗ ? (p₀ , v₀) (∈-merge-lemmaᵣ r (singleton (p , v)) (p , v) (∈-here empty empty z≤n refl)) !}
    insert-∈-aux {suc n} (node {nₗ} {nᵣ} x x₁ (p₀ , v₀) (l , r)) (p , v) | le p₀≤p | gt nᵣ+1>nₗ | q = {!   !}
    insert-∈-aux {suc n} (node x x₁ (p₀ , v₀) (l , r)) (p , v) | gt p₀>p = {! ∈-here (subst Heap lemma-i≡i+0 (node x x₁ (p₀ , v₀) (l , r))) empty z≤n (lemma-d (suc n) 0 0)  !}

    -- ∈-here (subst Heap lemma-i≡i+0 (node x x₁ (p₀ , v₀) (l , r))) empty z≤n (lemma-d (suc n) 0 0)
     