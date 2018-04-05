module List-tools where

open import Data.List as L
open import Data.Sum
open import Data.Product
open import Equivalence
open import Function

open import Relation.Binary.PropositionalEquality

data _∈_ {A : Set} (a : A) : List A → Set where
  here! : ∀ {xs} → a ∈ (a ∷ xs)
  there : ∀ {x xs} (path : a ∈ xs) → a ∈ (x ∷ xs) 

abstract

  ∈-++-l : ∀ {A : Set} {b : A} {l₂} (path : b ∈ l₂) (l₁ : List A) → b ∈ (l₁ ++ l₂)
  ∈-++-l path [] = path
  ∈-++-l path (x ∷ xs) = there (∈-++-l path xs)

  ∈-++-r : ∀ {A : Set} {b : A} {l₁} (path : b ∈ l₁) (l₂ : List A) → b ∈ (l₁ ++ l₂)
  ∈-++-r here! l₂ = here!
  ∈-++-r (there path) l₂ = there (∈-++-r path l₂)

  ∈[]-elim : ∀ {A P : Set} {b : A} (path : b ∈ []) → P
  ∈[]-elim ()

  ∈[x]-elim : ∀ {A : Set} {b x : A} (path : b ∈ (x ∷ [])) → b ≡ x
  ∈[x]-elim here! = refl
  ∈[x]-elim (there ())

  ∈L-elim : ∀ {A : Set} {b x : A} {xs : List A} (path : b ∈ (x ∷ xs)) → b ≡ x ⊎ b ∈ xs
  ∈L-elim here! = inj₁ refl
  ∈L-elim (there path) = inj₂ path

  ∈Lmap-elim : ∀ {A B : Set} {b : B} (f : A → B) (L : List A) →
                b ∈ (L.map f L) → ∃ (λ u → u ∈ L × f u ≡ b)
  ∈Lmap-elim f [] ()
  ∈Lmap-elim f (x ∷ xs) here! = x , here! , refl
  ∈Lmap-elim f (x ∷ xs) (there y) with ∈Lmap-elim f xs y
  ... | u , u∈L , Heq = u , there u∈L , Heq

  ∈Lmap : ∀ {A B : Set} {b : A} (f : A → B) {L : List A} (path : b ∈ L) → (f b) ∈ (L.map f L)
  ∈Lmap f here! = here!
  ∈Lmap f (there path) = there (∈Lmap f path)

  ∈Lmap-compat-l : ∀ {A B : Set} (P : B → Set) (f : A → B) (L : List A) →
                   ∃ (λ b → b ∈ L × P (f b)) → ∃ (λ b → b ∈ (L.map f L) × P b)
  ∈Lmap-compat-l P f [] (_ , () , _)
  ∈Lmap-compat-l P f (x ∷ xs) (.x , here! , Pfb) = f x , here! , Pfb
  ∈Lmap-compat-l P f (x ∷ xs) (b , there path , Pfb) with ∈Lmap-compat-l P f xs (b , path , Pfb)
  ... | v , path₂ , Pv = v , there path₂ , Pv

  ∈Lmap-compat-r : ∀ {A B : Set} (P : B → Set) (f : A → B) (L : List A) →
                   ∃ (λ b → b ∈ L × P (f b)) ← ∃ (λ b → b ∈ (L.map f L) × P b)
  ∈Lmap-compat-r P f [] (_ , () , _)
  ∈Lmap-compat-r P f (x ∷ xs) (.(f x) , here! , Pb) = x , here! , Pb
  ∈Lmap-compat-r P f (x ∷ xs) (b , there path , Pb) with ∈Lmap-compat-r P f xs (b , path , Pb)
  ... | v , path₂ , Pv = v , there path₂ , Pv