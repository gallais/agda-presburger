module Fin-prop where

open import Data.Product
open import Data.Sum
open import Data.Vec renaming (map to Vmap)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)
open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_)

open import Equivalence

open import Function
open import Relation.Binary.PropositionalEquality

abstract

  elim-Fin0 : ∀ {P : Set} → Fin 0 → P
  elim-Fin0 ()

  elim-Fin1 : (P : Fin 1 → Set) → Σ (Fin 1) P → P zero
  elim-Fin1 _ (zero , H) = H
  elim-Fin1 _ (Fs () , _) 

  elim-Finℕsn : ∀ {n} → (p : Fin (ℕs n)) → (p ≡ zero) ⊎ (∃ (λ i → p ≡ Fs i))
  elim-Finℕsn zero = inj₁ refl
  elim-Finℕsn (Fs i) = inj₂ (i , refl)

  toℕ-fromℕ-rev : ∀ n → toℕ (fromℕ n) ≡ n
  toℕ-fromℕ-rev zero = refl
  toℕ-fromℕ-rev (ℕs n) = cong ℕs (toℕ-fromℕ-rev n)

  toℕ-inject₁ : ∀ {n} (p : Fin n) → toℕ (inject₁ p) ≡ toℕ p
  toℕ-inject₁ zero = refl
  toℕ-inject₁ (Fs i) = cong ℕs (toℕ-inject₁ i)

  Fin-inv : {n : ℕ} → Fin n → Fin n
  Fin-inv {zero} ()
  Fin-inv {ℕs n} zero = fromℕ n
  Fin-inv {ℕs n} (Fs i) = inject₁ (Fin-inv i)

  Fin-inv-invol₁ : ∀ {n} (p : Fin n) → Fin-inv (inject₁ p) ≡ Fs (Fin-inv p)
  Fin-inv-invol₁ zero = refl
  Fin-inv-invol₁ (Fs i) with Fin-inv-invol₁ i
  ... | H = subst (λ u → inject₁ u ≡ Fs (inject₁ (Fin-inv i))) (sym H) refl

  Fin-inv-invol : ∀ {n} (p : Fin n) → Fin-inv (Fin-inv p) ≡ p
  Fin-inv-invol (zero {zero}) = refl
  Fin-inv-invol (zero {ℕs n}) with Fin-inv-invol (zero {n})
  ... | H = subst (λ u → inject₁ u ≡ zero) (sym H) refl
  Fin-inv-invol (Fs i) with Fin-inv-invol i
  ... | H = subst (λ u → u ≡ Fs i) (sym (Fin-inv-invol₁ (Fin-inv i))) (cong Fs H)

  Fin-inv-sem : ∀ {n} → (p : Fin n) → + toℕ (Fin-inv p) ≡ n ⊖ (toℕ (Fs p))
  Fin-inv-sem {zero} ()
  Fin-inv-sem zero = cong (λ x → + x) (toℕ-fromℕ-rev _)
  Fin-inv-sem {ℕs n} (Fs i) = subst (λ u → + toℕ (inject₁ (Fin-inv i)) ≡ u) (Fin-inv-sem i) (cong (λ u → + u) (toℕ-inject₁ _))

  Fin-Vmap-compat : ∀ {n : ℕ} {A B : Set} (f : A → B) (L : Vec A n) →
                    ∀ k → f (lookup k L) ≡  lookup k (Vmap f L)
  Fin-Vmap-compat f [] ()
  Fin-Vmap-compat f (x ∷ xs) zero = refl
  Fin-Vmap-compat f (x ∷ xs) (Fs i) = Fin-Vmap-compat f xs i

  lookup-tabulate : ∀ {n a} {A : Set a} (f : Fin n → A) (i : Fin n) →
                    lookup i (tabulate f) ≡ f i
  lookup-tabulate f zero = refl
  lookup-tabulate f (Fs i) = lookup-tabulate (f ∘ Fs) i

  allFin-inv : ∀ {n} (k : Fin n) → lookup k (allFin n) ≡ k
  allFin-inv k = lookup-tabulate id k