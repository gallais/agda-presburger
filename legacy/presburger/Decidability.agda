module Decidability where

open import Representation
open import Properties
open import Semantics

open import Fin-prop
open import Integer.Basic-Properties
open import Integer.Divisibility
import Integer.Structures as IntProp

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_ ; _≤?_ to _ℕ≤?_ ; _≟_ to _ℕ≟_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_ ; _≤?_ to _ℤ≤?_ ; _≟_ to _ℤ≟_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

open import Data.Empty
open import Data.Unit
open import Product
import Data.Product as P
open import Data.Sum
open import Data.Vec
open import Data.Nat.Divisibility using (divides)
open import Data.Integer.Divisibility

open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Algebra.Structures

private module ℤr = IsCommutativeRing IntProp.isCommutativeRing

Nnf-dec : ∀ {n} (φ : Nnf n) (ρ : Vec ℤ n) → Dec ([| proj₁ φ |] ρ)
Nnf-dec (.T , T-isnnf) ρ = yes _
Nnf-dec (.F , F-isnnf) ρ = no id
Nnf-dec {n} (.(t₁ le t₂) , le-isnnf {t₁} {t₂}) ρ = ([| t₁ |]e ρ) ℤ≤? [| t₂ |]e ρ
Nnf-dec {n} (.(t₁ eq t₂) , eq-isnnf {t₁} {t₂}) ρ = ([| t₁ |]e ρ) ℤ≟ [| t₂ |]e ρ
Nnf-dec {n} (.(not (t₁ eq t₂)) , neq-isnnf {t₁} {t₂}) ρ with ([| t₁ |]e ρ) ℤ≟ [| t₂ |]e ρ
... | yes P = no (λ hf → hf P)
... | no ¬P = yes ¬P
Nnf-dec {n} (.(k dvd t₁) , dvd-isnnf {k} {t₁}) ρ with k ∣? ([| t₁ |]e ρ)
... | yes (divides q Heq) with div-elim k ([| t₁ |]e ρ) (divides q Heq)
... | P._,_ h Hh = yes (P._,_ h (subst (λ u → [| t₁ |]e ρ ≡ u) (ℤr.*-comm h k) Hh))
Nnf-dec {n} (.(k dvd t₁) , dvd-isnnf {k} {t₁}) ρ | no ¬P = no (λ hf → ¬P (divides ∣ P.proj₁ hf ∣ (subst (λ u → ∣ [| t₁ |]e ρ ∣ ≡ u) (abs-distr-ℤ* (P.proj₁ hf) k) (subst (λ u → ∣ [| t₁ |]e ρ ∣ ≡ ∣ u ∣) (ℤr.*-comm k (P.proj₁ hf)) (cong ∣_∣ (P.proj₂ hf))))))
Nnf-dec {n} (.(not (k dvd t₁)) , ndvd-isnnf {k} {t₁}) ρ with k ∣? ([| t₁ |]e ρ)
... | yes (divides q Heq) with div-elim k ([| t₁ |]e ρ) (divides q Heq)
... | P._,_ h Hh = no (λ hf → hf (P._,_ h (subst (λ u → [| t₁ |]e ρ ≡ u) (ℤr.*-comm h k) Hh)))
Nnf-dec (.(not (k dvd t₁)) , ndvd-isnnf {k} {t₁}) ρ | no ¬P = yes (λ hf → ¬P (divides ∣ P.proj₁ hf ∣ (subst (λ u → ∣ [| t₁ |]e ρ ∣ ≡ u) (abs-distr-ℤ* (P.proj₁ hf) k) (subst (λ u → ∣ [| t₁ |]e ρ ∣ ≡ ∣ u ∣) (ℤr.*-comm k (P.proj₁ hf)) (cong ∣_∣ (P.proj₂ hf))))))
Nnf-dec {n} (.(φ₁ and φ₂) , and-isnnf {φ₁} {φ₂} y y') ρ with Nnf-dec (φ₁ , y) ρ | Nnf-dec (φ₂ , y') ρ
... | yes P₁ | yes P₂ = yes (P._,_ P₁ P₂)
... | no ¬P₁ | _ = no (λ hf → ¬P₁ (P.proj₁ hf))
... | _ | no ¬P₂ = no (λ hf → ¬P₂ (P.proj₂ hf))
Nnf-dec {n} (.(φ₁ or φ₂) , or-isnnf {φ₁} {φ₂} y y') ρ with Nnf-dec (φ₁ , y) ρ | Nnf-dec (φ₂ , y') ρ
... | no ¬P₁ | no ¬P₂ = no ([ ¬P₁ , ¬P₂ ]′)
... | yes P₁ | _ = yes (inj₁ P₁)
... | _ | yes P₂ = yes (inj₂ P₂)

lookup-dec : ∀ {k} {A : Set} {P : A → Set} (L : Vec A k) (Pr : ∀ a → Dec (P a)) → Dec (P.∃ (λ x → P (lookup x L)))
lookup-dec [] P⊎¬P = no (λ hf → elim-Fin0 (P.proj₁ hf))
lookup-dec {ℕs k} {A} {P} (x ∷ xs) P⊎¬P with (P⊎¬P x) | lookup-dec xs P⊎¬P
... | yes P₁ | _ = yes (P._,_ zero P₁)
... | _ | yes (P._,_ n₂ P₂) = yes (P._,_ (Fs n₂) P₂)
... | no ¬P₁ | no ¬P₂ = no (λ hf → [ (λ h → ¬P₁ (subst (λ u → P (lookup u (x ∷ xs))) h (P.proj₂ hf))) , (λ h → ¬P₂ (P._,_ (P.proj₁ h) (subst (λ u → P (lookup u (x ∷ xs))) (P.proj₂ h) (P.proj₂ hf)))) ]′ (elim-Finℕsn (P.proj₁ hf)))

Fin-dec : ∀ {k} {P : ∀ {n} → Fin n → Set} (Pr : ∀ {n} (a : Fin n) → Dec (P a)) → Dec (P.∃ (λ (x : Fin k) → P x))
Fin-dec {zero} Pr = no (λ hf → elim-Fin0 (P.proj₁ hf))
Fin-dec {ℕs n} {P} Pr with Pr (zero {n}) | Fin-dec {n} (λ a → Pr (Fs a))
... | yes P₁ | _ = yes (P._,_ zero P₁)
... | _ | yes (P._,_ n₂ P₂) = yes (P._,_ (Fs n₂) P₂)
... | no ¬P₁ | no ¬P₂ = no (λ hf → [ (λ h → ¬P₁ (subst (λ u → P u) h (P.proj₂ hf))) , (λ h → ¬P₂ (P._,_ (P.proj₁ h) (subst (λ u → P u) (P.proj₂ h) (P.proj₂ hf)))) ]′ (elim-Finℕsn (P.proj₁ hf)))