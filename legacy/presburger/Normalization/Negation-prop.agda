module Normalization.Negation-prop where

open import Representation
open import Properties
open import Semantics
open import Equivalence
open import Function
open import Normalization.Negation

open import Integer.Order-Properties
open import Integer.Divisibility
open import Comparisons

open import Product
open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

import Data.Product as P
open import Data.Vec
open import Data.Sum
open import Data.Empty
open import Data.Unit

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

postulate believeme : ∀ (P : Set) → P

private module ℤ≤ = DecTotalOrder Int.decTotalOrder

abstract
  Nnf-dec : ∀ {n} (φ : Nnf n) (ρ : Vec ℤ n) → Dec ([| proj₁ φ |] ρ)
  Nnf-dec (.T , T-isnnf) ρ = yes tt
  Nnf-dec (.F , F-isnnf) ρ = no id
  Nnf-dec (.(t₁ le t₂) , le-isnnf {t₁} {t₂}) ρ = ℤ≤._≤?_ _ _
  Nnf-dec (.(t₁ eq t₂) , eq-isnnf {t₁} {t₂}) ρ = ℤ≡-dec ([| t₁ |]e ρ) ([| t₂ |]e ρ)
  Nnf-dec (.(not (t₁ eq t₂)) , neq-isnnf {t₁} {t₂}) ρ with ℤ≡-dec ([| t₁ |]e ρ) ([| t₂ |]e ρ)
  ... | yes P = no (λ hf → hf P)
  ... | no ¬P = yes ¬P
  Nnf-dec (.(k dvd t₁) , dvd-isnnf {k} {t₁}) ρ = believeme _ --k ∣? ([| t₁ |]e ρ)
  Nnf-dec (.(not (k dvd t₁)) , ndvd-isnnf {k} {t₁}) ρ = believeme _
  Nnf-dec (.(φ₁ and φ₂) , and-isnnf {φ₁} {φ₂} pr₁ pr₂) ρ with Nnf-dec (φ₁ , pr₁) ρ | Nnf-dec (φ₂ , pr₂) ρ
  ... | no ¬P₁ | _ = no (λ hf → ¬P₁ (P.proj₁ hf))
  ... | _ | no ¬P₂ = no (λ hf → ¬P₂ (P.proj₂ hf))
  ... | yes P₁ | yes P₂ = yes (P._,_ P₁ P₂)
  Nnf-dec (.(φ₁ or φ₂) , or-isnnf {φ₁} {φ₂} pr₁ pr₂) ρ with Nnf-dec (φ₁ , pr₁) ρ | Nnf-dec (φ₂ , pr₂) ρ
  ... | yes P₁ | _ = yes (inj₁ P₁)
  ... | _ | yes P₂ = yes (inj₂ P₂)
  ... | no ¬P₁ | no ¬P₂ = no [ ¬P₁ , ¬P₂ ]′

  neg-sem : ∀ {n} (φ : Nnf n) → not (proj₁ φ) ⇔ proj₁ (neg φ)
  neg-sem (.T , T-isnnf) ρ = P._,_ (λ x → x tt) (λ x x' → x)
  neg-sem (.F , F-isnnf) ρ = P._,_ (λ x → tt) (λ x x' → x')
  neg-sem (.(t₁ le t₂) , le-isnnf {t₁} {t₂}) ρ = P._,_ ¬ℤ≤-is-ℤ> (λ hlt hle → ℤ<-irrefl ([| t₂ |]e ρ) (ℤ≤.trans hlt hle))
  neg-sem (.(t₁ eq t₂) , eq-isnnf {t₁} {t₂}) ρ = P._,_ id id
  neg-sem (.(not (t₁ eq t₂)) , neq-isnnf {t₁} {t₂}) ρ with ℤ≡-dec ([| t₁ |]e ρ) ([| t₂ |]e ρ)
  ... | yes p = P._,_ (λ x → p) (λ x x' → x' x)
  ... | no ¬p = P._,_ (λ hf → ⊥-elim (hf ¬p)) (λ x x' → x' x)
  neg-sem (.(k dvd t₁) , dvd-isnnf {k} {t₁}) ρ = P._,_ id id
  neg-sem (.(not (k dvd t₁)) , ndvd-isnnf {k} {t₁}) ρ with Nnf-dec (k dvd t₁ , dvd-isnnf) ρ
  ... | no ¬P = P._,_ (λ hf → ⊥-elim (hf ¬P)) (λ x x' → x' x)
  ... | yes P = P._,_ (λ _ → P) (λ x x' → x' x)
  neg-sem (.(φ₁ and φ₂) , and-isnnf {φ₁} {φ₂} pr₁ pr₂) ρ with neg (φ₁ , pr₁) | neg (φ₂ , pr₂) | neg-sem (φ₁ , pr₁) ρ | neg-sem (φ₂ , pr₂) ρ | Nnf-dec (φ₁ , pr₁) ρ | Nnf-dec (φ₂ , pr₂) ρ
  ... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ | no ¬H₁ | _ = P._,_ (λ _ → inj₁ (P₁ ¬H₁)) [ (λ hf₁ hf₂ → Q₁ hf₁ (P.proj₁ hf₂)) , (λ hf₁ hf₂ → Q₂ hf₁ (P.proj₂ hf₂)) ]′
  ... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ | _ | no ¬H₂ = P._,_ (λ _ → inj₂ (P₂ ¬H₂)) [ (λ hf₁ hf₂ → Q₁ hf₁ (P.proj₁ hf₂)) , (λ hf₁ hf₂ → Q₂ hf₁ (P.proj₂ hf₂)) ]′
  ... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ | yes H₁ | yes H₂ = P._,_ (λ hf → ⊥-elim (hf (P._,_ H₁ H₂))) [ (λ hf₁ hf₂ → Q₁ hf₁ (P.proj₁ hf₂)) , (λ hf₁ hf₂ → Q₂ hf₁ (P.proj₂ hf₂)) ]′
  neg-sem (.(φ₁ or φ₂) , or-isnnf {φ₁} {φ₂} pr₁ pr₂) ρ with neg (φ₁ , pr₁) | neg (φ₂ , pr₂) | neg-sem (φ₁ , pr₁) ρ | neg-sem (φ₂ , pr₂) ρ | Nnf-dec (φ₁ , pr₁) ρ | Nnf-dec (φ₂ , pr₂) ρ
  ... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ | yes H₁ | _ = P._,_ (λ hf → ⊥-elim (hf (inj₁ H₁))) (λ hf₁ → [ Q₁ (P.proj₁ hf₁) , Q₂ (P.proj₂ hf₁) ]′)
  ... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ | _ | yes H₂ = P._,_ (λ hf → ⊥-elim (hf (inj₂ H₂))) (λ hf₁ → [ Q₁ (P.proj₁ hf₁) , Q₂ (P.proj₂ hf₁) ]′)
  ... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ | no ¬H₁ | no ¬H₂ = P._,_ (λ _ → P._,_ (P₁ ¬H₁) (P₂ ¬H₂)) (λ hf₁ → [ Q₁ (P.proj₁ hf₁) , Q₂ (P.proj₂ hf₁) ]′)

  nnf-sem : ∀ {n} (φ : Qfree n) → proj₁ φ ⇔ proj₁ (nnf φ)
  nnf-sem (.T , T-isqfree) ρ = P._,_ id id
  nnf-sem (.F , F-isqfree) ρ = P._,_ id id
  nnf-sem (.(t₁ lt t₂) , lt-isqfree {t₁} {t₂}) ρ = P._,_ id id
  nnf-sem (.(t₁ gt t₂) , gt-isqfree {t₁} {t₂}) ρ = P._,_ id id
  nnf-sem (.(t₁ le t₂) , le-isqfree {t₁} {t₂}) ρ = P._,_ id id
  nnf-sem (.(t₁ ge t₂) , ge-isqfree {t₁} {t₂}) ρ = P._,_ id id
  nnf-sem (.(t₁ eq t₂) , eq-isqfree {t₁} {t₂}) ρ = P._,_ id id
  nnf-sem (.(k dvd t₁) , dvd-isqfree {k} {t₁}) ρ = P._,_ id id
  nnf-sem (.(not φ) , not-isqfree {φ} y) ρ with nnf-sem (φ , y) ρ | neg-sem (nnf (φ , y)) ρ
  ... | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ = P._,_ (λ x → P₂ (λ x' → x (Q₁ x'))) (λ x x' → Q₂ x (P₁ x'))
  nnf-sem (.(φ₁ and φ₂) , and-isqfree {φ₁} {φ₂} y y') ρ with nnf (φ₁ , y) | nnf (φ₂ , y') | nnf-sem (φ₁ , y) ρ | nnf-sem (φ₂ , y') ρ
  ... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ = P._,_ (λ H → P._,_ (P₁ (P.proj₁ H)) (P₂ (P.proj₂ H))) (λ H → P._,_ (Q₁ (P.proj₁ H)) (Q₂ (P.proj₂ H)))
  nnf-sem (.(φ₁ or φ₂) , or-isqfree {φ₁} {φ₂} y y') ρ with nnf (φ₁ , y) | nnf (φ₂ , y') | nnf-sem (φ₁ , y) ρ | nnf-sem (φ₂ , y') ρ
  ... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ = P._,_ [ inj₁ ∘ P₁ , inj₂ ∘ P₂ ]′ [ inj₁ ∘ Q₁ , inj₂ ∘ Q₂ ]′
  nnf-sem (.(φ₁ ⇀ φ₂) , ⇀-isqfree {φ₁} {φ₂} y y') ρ with nnf (φ₁ , y) | nnf (φ₂ , y') | nnf-sem (φ₁ , y) ρ | nnf-sem (φ₂ , y') ρ
  ... | φ₃ , Hφ₃ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ with neg (φ₃ , Hφ₃) | neg-sem (φ₃ , Hφ₃) ρ
  ... | ψ₁ , Hψ₁ | P._,_ P₃ Q₃ with Nnf-dec (φ₃ , Hφ₃) ρ
  ... | yes P = P._,_ (λ h → inj₂ (P₂ (h (Q₁ P)))) [ (λ hf₁ hf₂ → ⊥-elim (Q₃ hf₁ (P₁ hf₂))) , (λ x x' → Q₂ x) ]′
  ... | no ¬P = P._,_ (λ h → inj₁ (P₃ ¬P)) [ (λ hf₁ hf₂ → ⊥-elim (Q₃ hf₁ (P₁ hf₂))) , (λ x x' → Q₂ x) ]′