{-# OPTIONS --without-K #-}

module Sep02Ex01 where

open import Data.Nat
open import Level as L using (Level)
open import Data.Product public
  using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map₁; map₂)


T1 :
  (A : Set) →
  (B : A -> Set)
  (C : (∀ (x : A) → B x → Set)) →
  Set
T1 A B C =
  (∀ (x : A) → Σ (B x) (λ y → C x y))

T2 :
  (A : Set) →
  (B : A -> Set)
  (C : (∀ (x : A) → B x → Set)) →
  Set
T2 A B C =
  (Σ (∀ (x : A) → (B x)) (λ k → (∀ (x : A) → C x (k x))))

conv₁₂′ :
     (A : Set) →
     (B : A -> Set)
     (C : (∀ (x : A) → B x → Set)) →
     (T1 A B C → T2 A B C)
conv₁₂′ A B C t₁ = (λ x → proj₁ (t₁ x)) , λ x → proj₂ (t₁ x)

conv₂₁′ : (A : Set) →
     (B : A -> Set)
     (C : (∀ (x : A) → B x → Set)) →
     (T2 A B C → T1 A B C)
conv₂₁′ A B C t₂ = λ x → (proj₁ t₂ x) , (proj₂ t₂ x)

conv₁₂ : (A : Set) →
     (B : A -> Set)
     (C : (∀ (x : A) → B x → Set)) →
     ((∀ (x : A) → Σ (B x) (λ y → C x y)) →
      (Σ (∀ (x : A) → (B x)) (λ k → (∀ (x : A) → C x (k x)))))
conv₁₂ A B C t₁ = (λ x → proj₁ (t₁ x)) , λ x → proj₂ (t₁ x)

conv₂₁ : (A : Set) →
     (B : A -> Set)
     (C : (∀ (x : A) → B x → Set)) →
     ((Σ (∀ (x : A) → (B x)) (λ k → (∀ (x : A) → C x (k x)))) →
      (∀ (x : A) → Σ (B x) (λ y → C x y)))
conv₂₁ A B C t₂ = λ x → (proj₁ t₂ x) , (proj₂ t₂ x)
