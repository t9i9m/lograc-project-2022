-- WellFounded recursion used in Ranked merge

open import Level        renaming (zero to lzero; suc to lsuc)

module WellFounded {l : Level} where

open import Induction    using (RecStruct)
open import Induction.WellFounded using (Acc; acc; WfRec)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_; _≰_)
open import Data.Nat.Properties   using (suc-injective; +-comm; +-assoc; +-suc; 0≢1+n)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.Core using (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

-- Note: code from standard library adjusted for merge recursion
-- https://agda.github.io/agda-stdlib/Induction.WellFounded.html#1248
data _<'_ (m : (ℕ × ℕ)): (ℕ × ℕ) → Set l where
  <'-stepsl : m <' ((suc (proj₁ m)) , proj₂ m)
  <'-stepsr : m <' (proj₁ m , (suc (proj₂ m)))
  <'-stepl  : ∀ {nₗ} (m<nₗ : m <' (nₗ , proj₂ m)) → m <' ((suc nₗ) , proj₂ m)
  <'-stepr  : ∀ {nᵣ} (m<nᵣ : m <' (proj₁ m , nᵣ)) → m <' (proj₁ m , (suc nᵣ))
  <'-step   : ∀ {nₗ nᵣ} (m<nn : m <' (nₗ , nᵣ))   → m <' ((suc nₗ) , (suc nᵣ))

Well-founded : ∀ {a} {A : Set} → Rel A a → Set a
Well-founded _<_ = ∀ x → Acc _<_ x

<'-Rec : RecStruct (ℕ × ℕ) l _
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

-- Lemma proving that the left subtree is smaller than the whole tree 
lemma-l : {nₗₗ nₗᵣ nₗ nᵣ : ℕ} → (nₗ ≡ (1 + nₗₗ + nₗᵣ)) → ((nₗᵣ , nᵣ) <' (nₗ , nᵣ))
lemma-l {zero} {nₗᵣ} {nₗ} {nᵣ} p rewrite p = <'-stepsl
lemma-l {suc nₗₗ} {nₗᵣ} {suc nₗ} {nᵣ} p = <'-stepl (lemma-l (suc-injective p))

-- Lemma proving that the right subtree is smaller than the whole tree 
lemma-r : {nᵣₗ nᵣᵣ nₗ nᵣ : ℕ} → (nᵣ ≡ (1 + nᵣₗ + nᵣᵣ)) → ((nₗ , nᵣᵣ) <' (nₗ , nᵣ))
lemma-r {zero} {nᵣᵣ} {nₗ} {nᵣ} p rewrite p = <'-stepsr
lemma-r {suc nᵣₗ} {nᵣᵣ} {nₗ} {suc nᵣ} p = <'-stepr (lemma-r (suc-injective p))
