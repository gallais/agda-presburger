module Product where

infixr 4 _,_

data Σ (A : Set) (B : (a : A) → Set) : Set where
  _,_ : ∀ (a : A) (b : B a) → Σ A B

∃ : {A : Set} (B : (a : A) → Set) → Set
∃ {A} B = Σ A B

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

proj₁ : ∀ {A B} (π : Σ A B) → A
proj₁ (a , _) = a

proj₂ : ∀ {A B} (π : Σ A B) → B (proj₁ π)
proj₂ (_ , b) = b


infix 1 Given_compute_by_andprove_assuming_by_

Given_compute_by_andprove_assuming_by_ : ∀ (A C : Set) (f : A → C)
  (D : (c : C) → Set) (B : (a : A) → Set)
  (g : (a : A) (b : B a) → D (f a)) → Σ A B → Σ C D
Given A compute C by f andprove D assuming B by g = λ { (a , b) → f a , g a b }