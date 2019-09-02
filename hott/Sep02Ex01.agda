{-# OPTIONS --without-K #-}

module Sep02Ex01 where

open import Data.Nat
open import Level as L using (Level)
open import Data.Product public
  using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map₁; map₂)


-- T1 : ∀ {𝓁 : Level} → Set (L.suc 𝓁)
-- T1 {𝓁} = (A : Set 𝓁) →
--       (B : A -> Set 𝓁)
--       (C : (∀ (x : A) → B x → Set 𝓁 )) →
--       (∀ (x : A) → B x → Set 𝓁)

-- T2 : ∀ {𝓁 : Level} → Set (L.suc 𝓁)
-- T2 {𝓁} = (A : Set 𝓁) →
--      (B : A -> Set 𝓁)
--      (C : (∀ (x : A) → B x → Set 𝓁)) →
--      (Σ (∀ (x : A) → (B x)) (λ k → (∀ (x : A) → C x (k x))))

-- f₁ : ∀ {𝓁} →
--      (A : Set 𝓁) →
--      (B : A -> Set 𝓁)
--      (C : (∀ (x : A) → B x → Set 𝓁)) →
--      ((T1 {𝓁} A B C) → (T2 {𝓁} A B C))
-- f₁ = {!!}

-- T1 : (A : Set) →
--      (B : A -> Set)
--      (C : (∀ (x : A) → B x → Set)) →
--      (∀ (x : A) → B x → Set)
-- T1 A B C = {!!}

-- T2 : (A : Set) →
--      (B : A -> Set)
--      (C : (∀ (x : A) → B x → Set)) →
--      (Σ (∀ (x : A) → (B x)) (λ k → (∀ (x : A) → C x (k x)))) →
--      Set
-- T2 A B C = {!!}

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
