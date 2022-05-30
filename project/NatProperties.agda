module NatProperties where

open import Data.List    using (List; []; _∷_; foldl; foldr)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_; _≰_)
open import Data.Nat.Properties   using (suc-injective; +-comm; +-assoc; +-suc; 0≢1+n)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)


-- What follow are a bunch of trivial lemmas to assist Agda in being a proof assistant...
-- TODO: the lemmas could be shortened by finding common patterns...

lemma-i≡i+0 : {i : ℕ} → i ≡ (i + zero)
lemma-i≡i+0 {i} = sym (+-comm i zero)

lemma-i+1≡suci : {i : ℕ} → (i + 1) ≡ (suc i)
lemma-i+1≡suci {i} = +-comm i 1

-- lemma-+-sucₙ' is a generalization of lemma-+-sucₙ
-- Both are a generalization of lemma-1aa to n elements
lemma-+-sucₙ' : (a s : ℕ) → (xs : List ℕ) → a + suc (foldl _+_ s xs) ≡ suc (foldl _+_ a (s ∷ xs))
lemma-+-sucₙ' a s [] = +-suc a s
lemma-+-sucₙ' a s (x ∷ xs) = begin 
    a + suc (foldl _+_ (s + x) xs)   ≡⟨ lemma-+-sucₙ' a (s + x) xs ⟩ 
    suc (foldl _+_ (a + (s + x)) xs) ≡⟨ cong suc (cong (λ y → foldl _+_ y xs) (sym (+-assoc a s x))) ⟩
    suc (foldl _+_ (a + s + x) xs)
    ∎

-- This is lemma-+-sucₙ' with the additional proof that a + 0 = a 
lemma-+-sucₙ : (a : ℕ) → (xs : List ℕ) → a + suc (foldl _+_ 0 xs) ≡ suc (foldl _+_ 0 (a ∷ xs))
lemma-+-sucₙ a xs = begin
    a + suc (foldl _+_ 0 xs)   ≡⟨ lemma-+-sucₙ' a 0 xs ⟩
    suc (foldl _+_ (a + 0) xs) ≡⟨ cong suc (cong (λ x → foldl _+_ x xs) (+-comm a 0)) ⟩
    suc (foldl _+_ a xs)
    ∎

lemma-1aa : (b c d : ℕ) → (b + suc (c + d)) ≡ suc (b + c + d)
lemma-1aa b c d =
    begin b + suc (c + d) ≡⟨ +-suc b (c + d) ⟩ 
    suc (b + (c + d)) ≡⟨ cong suc (sym (+-assoc b c d)) ⟩
    suc (b + c + d) 
    ∎

lemma-1a : (a b c d : ℕ) → 
            (a + (b + suc (c + d))) ≡ suc (a + b + c + d)
lemma-1a a b c d = 
    begin 
    a + (b + suc (c + d)) ≡⟨ cong (a +_) (lemma-+-sucₙ b (c ∷ d ∷ [])) ⟩ 
    a + suc (b + c + d)   ≡⟨ lemma-+-sucₙ a (b ∷ c ∷ d ∷ []) ⟩ 
    suc (a + b + c + d) 
    ∎

lemma-1b : (a b c d : ℕ) →
            (a + b + suc (c + d)) ≡ suc (a + b + c + d)
lemma-1b a b c d = 
    begin
    a + b + suc (c + d)   ≡⟨ +-assoc a b (suc (c + d)) ⟩ 
    a + (b + suc (c + d)) ≡⟨ lemma-1a a b c d ⟩ 
    suc (a + b + c + d)
    ∎

-- For merge case 1
lemma-1 : (a b c d : ℕ) → 
            suc (a + (b + suc (c + d))) ≡ suc (a + b + suc (c + d))
lemma-1 a b c d = cong suc 
    (trans 
    (lemma-1a a b c d) 
    (sym 
        (lemma-1b a b c d)))

lemma-2a : (a b c : ℕ) → a + (b + suc c) ≡ suc (a + b + c)
lemma-2a a b c = 
    begin 
    a + (b + suc c) ≡⟨ cong (a +_) (lemma-+-sucₙ b (c ∷ [])) ⟩ 
    a + suc (b + c) ≡⟨ lemma-+-sucₙ a (b ∷ c ∷ []) ⟩ 
    suc (a + b + c)
    ∎

lemma-2b : (a b c : ℕ) → a + b + suc c ≡ suc (a + b + c)
lemma-2b a b c = 
    begin
    a + b + suc c   ≡⟨ +-assoc a b (suc c) ⟩ 
    a + (b + suc c) ≡⟨ lemma-2a a b c ⟩ 
    suc (a + b + c) 
    ∎

-- For merge case 2
lemma-2 : (a b c d : ℕ) → 
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

lemma-3a : (a b c d : ℕ) → a + b + c + d ≡ c + d + a + b
lemma-3a a b c d = 
    begin
    a + b + c + d     ≡⟨ +-assoc (a + b) c d ⟩ 
    (a + b) + (c + d) ≡⟨ +-comm (a + b) (c + d) ⟩ 
    (c + d) + (a + b) ≡⟨ sym (+-assoc (c + d) a b) ⟩
    c + d + a + b
    ∎

-- For merge case 3
lemma-3 : (a b c d : ℕ) →
            suc (a + (b + suc (c + d))) ≡ suc (c + d + suc (a + b))
lemma-3 a b c d = cong suc 
    (begin 
    a + (b + suc (c + d)) ≡⟨ lemma-1a a b c d ⟩ 
    suc (a + b + c + d) ≡⟨ cong suc (lemma-3a a b c d) ⟩
    suc (c + d + a + b) ≡⟨ sym (lemma-1b c d a b) ⟩ 
    c + d + suc (a + b)
    ∎)

lemma-4a : (a b c d : ℕ) →
            a + suc (b + c) + d ≡ suc (a + b + c + d)
lemma-4a a b c d = 
    begin
    a + suc (b + c) + d ≡⟨ cong (_+ d) (lemma-+-sucₙ a (b ∷ c ∷ [])) ⟩ 
    suc (a + b + c) + d ≡⟨ refl ⟩ 
    suc (a + b + c + d)
    ∎

lemma-4b : (a b c d : ℕ) →
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
lemma-4 : (a b c d : ℕ) → 
            suc (a + suc (b + c) + d) ≡ suc (b + c + suc (d + a))
lemma-4 a b c d = cong suc 
    (begin 
    a + suc (b + c) + d ≡⟨ lemma-4a a b c d ⟩ 
    suc (a + b + c + d) ≡⟨ cong suc (lemma-4b a b c d) ⟩ 
    suc (b + c + d + a) ≡⟨ sym (lemma-1b b c d a) ⟩ 
    b + c + suc (d + a)
    ∎)

a≡a : (a : ℕ) → a ≡ a
a≡a a = refl

lemma-a : (a b c : ℕ) → a + b + c ≡ a + (b + c)
lemma-a a b c = +-assoc a b c

lemma-b : (a b c : ℕ) → a + b + c ≡ (b + c) + a
lemma-b a b c = 
    begin
    a + b + c ≡⟨ lemma-a a b c ⟩ 
    a + (b + c) ≡⟨ +-comm a ((b + c)) ⟩ 
    (b + c) + a
    ∎

lemma-cc : (a b c : ℕ) → a + b + c ≡ b + a + c
lemma-cc a b c =
    begin
    a + b + c ≡⟨ cong₂ (_+_) (+-comm a b) refl ⟩
    b + a + c
    ∎

lemma-c : (a b c : ℕ) → a + suc (b + c) ≡ suc (b + (a + c))
lemma-c a b c = 
    begin
    a + suc (b + c) ≡⟨ lemma-1aa a b c ⟩
    suc (a + b + c) ≡⟨ cong suc (lemma-cc a b c) ⟩
    suc (b + a + c) ≡⟨ cong suc (lemma-a b a c) ⟩
    suc (b + (a + c)) ∎

lemma-d : (a b c : ℕ) → a + suc (b + c) ≡ suc (a + c + b)
lemma-d a b c =
    begin 
    a + suc (b + c) ≡⟨ lemma-c a b c ⟩
    suc (b + (a + c)) ≡⟨ cong suc (+-comm b (a + c)) ⟩
    suc (a + c + b) ∎

lemma-e : (a b c d : ℕ) → suc (a + b) ≡ d → suc (a + b + c) ≡ d + c
lemma-e a b c .(suc (a + b)) refl = refl

lemma-f : (a b c d : ℕ) → suc (a + b) ≡ d → c + suc (a + b) ≡ c + d
lemma-f a b c .(suc (a + b)) refl = refl
