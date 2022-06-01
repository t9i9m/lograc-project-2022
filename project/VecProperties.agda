-- A bunch of properties about reversing vectors and ∈

module VecProperties where

open import Level        renaming (zero to lzero; suc to lsuc)
open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; _×_)
open import Data.Vec     using (Vec; []; _∷_; head; tail)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Vec using (reverse; _∷ʳ_; _++_; initLast; last; init)

-- Can't import other useful properties because of old Agda version... :(
-- open import Data.Vec.Properties using (reverse-∷)

-- Note: using `variable n : ℕ` makes is easy to work with vector sizes.
private
  variable
    a : Level
    A : Set a
    m n : ℕ

-- An inductive relation that specifies that a Vector contains a given element.
-- `a [∈] b` is read as "a in vector b"
data _[∈]_ {A : Set a} (x : A) : Vec A n → Set a where
  ∈-head : {h : Vec A n} → x [∈] (x ∷ h)
  ∈-tail : {h : Vec A n} {y : A} → x [∈] h → x [∈] (y ∷ h)

private
  postulate 
    -- This is already proven in a newer version of Data.Vec.Properties
    reverse-∷ : ∀ x (xs : Vec A n) → reverse (x ∷ xs) ≡ reverse xs ∷ʳ x

  reverse-∷ʳ : ∀ y (ys : Vec A n) → reverse (ys ∷ʳ y) ≡ y ∷ reverse ys
  reverse-∷ʳ y [] = refl
  reverse-∷ʳ y (y' ∷ ys) = begin 
    reverse ((y' ∷ ys) ∷ʳ y) ≡⟨ refl ⟩
    reverse (y' ∷ (ys ∷ʳ y)) ≡⟨ reverse-∷ y' (ys ∷ʳ y) ⟩
    reverse (ys ∷ʳ y) ∷ʳ y'  ≡⟨ cong (_∷ʳ y') (reverse-∷ʳ y ys) ⟩
    (y ∷ (reverse ys)) ∷ʳ y' ≡⟨ refl ⟩
    y ∷ ((reverse ys) ∷ʳ y') ≡⟨ cong (y ∷_) (sym (reverse-∷ y' ys)) ⟩
    y ∷ (reverse (y' ∷ ys)) ∎

  -- This is the same functionality as Data.Vec.last without with |
  last' : Vec A (1 + n) → A
  last' (x ∷ []) = x
  last' (_ ∷ x ∷ xs) = last' (x ∷ xs)

  -- This is the same functionality as Data.Vec.init without with |
  dropLast : (xs : Vec A (1 + n)) → Vec A n
  dropLast (x ∷ []) = []
  dropLast (x ∷ x₁ ∷ xs) = x ∷ (dropLast (x₁ ∷ xs))
  
  dropLast-lemma : (y : A) (ys : Vec A n) → dropLast (ys ∷ʳ y) ≡ ys
  dropLast-lemma y [] = refl
  dropLast-lemma y (x ∷ []) = refl
  dropLast-lemma y (x ∷ x₁ ∷ ys) = cong (x ∷_) (dropLast-lemma y (x₁ ∷ ys))

  dropLast-id : (xs : Vec A (1 + n)) → dropLast xs ∷ʳ last' xs ≡ xs
  dropLast-id (x ∷ []) = refl
  dropLast-id (x ∷ x₁ ∷ xs) = cong (x ∷_) (dropLast-id (x₁ ∷ xs))

  reverse-dropLast-id : (xs : Vec A (1 + n)) 
                      → reverse (dropLast xs ∷ʳ last' xs) ≡ reverse xs
  reverse-dropLast-id xs = cong reverse (dropLast-id xs)

  dropFirst : Vec A (1 + n) → Vec A n
  dropFirst (x ∷ xs) = xs

  reverse-first-last : (xs : Vec A (1 + n))
                      → reverse (dropLast xs) ≡ dropFirst (reverse xs)
  reverse-first-last xs with initLast xs
  ... | (ys , y , refl) rewrite reverse-∷ʳ y ys | dropLast-lemma y ys = refl

  dropLast-reverse : (xs : Vec A (1 + n)) → reverse xs ≡ last' xs ∷ (reverse (dropLast xs))
  dropLast-reverse xs rewrite sym (reverse-dropLast-id xs) = reverse-∷ʳ (last' xs) (dropLast xs)

  ∈-concat : {p : A} {xs : Vec A n} (ys : Vec A m)
            → p [∈] xs → p [∈] (xs ++ ys)
  ∈-concat {xs = x ∷ []} ys ∈-head = ∈-head
  ∈-concat {xs = x ∷ x₁ ∷ xs} ys ∈-head = ∈-head
  ∈-concat {xs = x ∷ x₁ ∷ xs} ys (∈-tail q) = ∈-tail (∈-concat ys q)

  ∈-append : {p : A} {xs : Vec A n} (y : A)
            → p [∈] xs → p [∈] (xs ∷ʳ y)
  ∈-append {p = .x} {xs = x ∷ xs} y ∈-head = ∈-head
  ∈-append {p = p} {xs = x ∷ xs} y (∈-tail q) = ∈-tail (∈-append y q)

  ∈-head-rev : {p : A} (xs : Vec A n)
            → p [∈] (p ∷ xs)
            → p [∈] reverse (p ∷ xs)
  ∈-head-rev [] q = ∈-head
  ∈-head-rev {p = p} (x ∷ xs) q rewrite (dropLast-reverse (p ∷ x ∷ xs)) = ∈-tail (∈-head-rev (dropLast (x ∷ xs)) ∈-head)

-- If a vector contains an element, the element is contained also in the reversed vector.
[∈]-rev : {p : A} (xs : Vec A n)
        → p [∈] xs 
        → p [∈] reverse xs
[∈]-rev (p ∷ xs) ∈-head = ∈-head-rev xs ∈-head
[∈]-rev (x ∷ xs) (∈-tail p∈xs) rewrite (reverse-∷ x xs) = ∈-append x ([∈]-rev xs p∈xs)

