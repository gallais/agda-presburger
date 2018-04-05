module Normalization.Qelimination-prop where

open import Representation
open import Properties
open import Properties-prop
open import Semantics
open import Equivalence
open import Product
open import Function

open import Data.Sum
open import Data.Empty
open import Data.Unit

open import Integer.Order-Properties

import Data.Product as P

open import Normalization.Qelimination
open import Normalization.Negation
open import Normalization.Negation-prop

-- About ≡ and Dec
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Datatypes
open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)
open import Data.Vec


private module ℤ≤ = DecTotalOrder Int.decTotalOrder


Qfree-dec : ∀ {n} (φ : Qfree n) ρ → Dec ([| proj₁ φ |] ρ)
Qfree-dec φ ρ with nnf-sem φ ρ | Nnf-dec (nnf φ) ρ
... | P._,_ P Q | yes H = yes (Q H)
... | P._,_ P Q | no ¬H = no (λ x → ¬H (P x))

postulate QfreeCooper : ∀ {n} (φ : Qfree (ℕs n)) → ex (proj₁ φ) ⇔ proj₁ (qelim φ)

qneg-sem : ∀ {n} (φ : Qfree n) → not (proj₁ φ) ⇔ proj₁ (qneg φ)
qneg-sem (.T , T-isqfree) ρ = P._,_ (λ x → x tt) (λ x x' → x)
qneg-sem (.F , F-isqfree) ρ = P._,_ (λ x → tt) (λ x x' → x')
qneg-sem (.(t₁ lt t₂) , lt-isqfree {t₁} {t₂}) ρ = believeme _
qneg-sem (.(t₁ gt t₂) , gt-isqfree {t₁} {t₂}) ρ = believeme _
qneg-sem (.(t₁ le t₂) , le-isqfree {t₁} {t₂}) ρ =  P._,_ ¬ℤ≤-is-ℤ> (λ hlt hle → ℤ<-irrefl ([| t₂ |]e ρ) (ℤ≤.trans hlt hle))
qneg-sem (.(t₁ ge t₂) , ge-isqfree {t₁} {t₂}) ρ = believeme _
qneg-sem (.(t₁ eq t₂) , eq-isqfree {t₁} {t₂}) ρ = P._,_ id id
qneg-sem (.(k dvd t₁) , dvd-isqfree {k} {t₁}) ρ = P._,_ id id
qneg-sem (.(not φ) , not-isqfree {φ} y) ρ with Qfree-dec (φ , y) ρ
... | yes P = P._,_ (λ x → P) (λ x x' → x' x)
... | no ¬P = P._,_ (λ x → ⊥-elim (x ¬P)) (λ x x' → x' x)
qneg-sem (.(φ₁ and φ₂) , and-isqfree {φ₁} {φ₂} y y') ρ with qneg (φ₁ , y) | qneg (φ₂ , y') | qneg-sem (φ₁ , y) ρ | qneg-sem (φ₂ , y') ρ
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ with Qfree-dec (φ₁ , y) ρ | Qfree-dec (φ₂ , y') ρ
... | no ¬H₁ | _ = P._,_ (λ _ → (inj₁ ∘ P₁) ¬H₁) (λ _ H → ¬H₁ (P.proj₁ H))
... | _ | no ¬H₂ = P._,_ (λ _ → (inj₂ ∘ P₂) ¬H₂) (λ _ H → ¬H₂ (P.proj₂ H))
... | yes H₁ | yes H₂ = P._,_ (λ H → ⊥-elim (H (P._,_ H₁ H₂))) [ (λ H _ → Q₁ H H₁) , (λ H _ → Q₂ H H₂) ]′
qneg-sem (.(φ₁ or φ₂) , or-isqfree {φ₁} {φ₂} y y') ρ with qneg (φ₁ , y) | qneg (φ₂ , y') | qneg-sem (φ₁ , y) ρ | qneg-sem (φ₂ , y') ρ
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ with Qfree-dec (φ₁ , y) ρ | Qfree-dec (φ₂ , y') ρ
... | yes H₁ | _ = P._,_ (λ H → ⊥-elim ((H ∘ inj₁) H₁)) (λ H _ → ⊥-elim (Q₁ (P.proj₁ H) H₁))
... | _ | yes H₂ = P._,_ (λ H → ⊥-elim ((H ∘ inj₂) H₂)) (λ H _ → ⊥-elim (Q₂ (P.proj₂ H) H₂))
... | no ¬H₁ | no ¬H₂ = P._,_ (λ _ → P._,_ (P₁ ¬H₁) (P₂ ¬H₂)) (λ _ → [ ¬H₁ , ¬H₂ ]′)
qneg-sem (.(φ₁ ⇀ φ₂) , ⇀-isqfree {φ₁} {φ₂} y y') ρ with qneg (φ₂ , y') | qneg-sem (φ₂ , y') ρ | Qfree-dec (φ₁ , y) ρ
... | ψ₂ , Hψ₂ | P._,_ P Q | yes H₁ = P._,_ (λ H → P._,_ H₁ (P (λ H₂ → H (λ _ → H₂)))) (λ x x' → Q (P.proj₂ x) (x' (P.proj₁ x)))
... | ψ₂ , Hψ₂ | P._,_ P Q | no ¬H₁ = P._,_ (λ H → ⊥-elim (H (λ H₁ → ⊥-elim (¬H₁ H₁)))) (λ x x' → Q (P.proj₂ x) (x' (P.proj₁ x)))

Qfree-EM : ∀ {n} (φ : Qfree n) (ρ : Vec ℤ n) → [| proj₁ φ |] ρ ⊎ [| not (proj₁ φ) |] ρ
Qfree-EM φ ρ with Qfree-dec φ ρ
... | yes P = inj₁ P
... | no ¬P = inj₂ ¬P

qfree-sem : ∀ {n} (φ : form n) → φ ⇔ proj₁ (qfree φ)
qfree-sem T ρ = P._,_ id id
qfree-sem F ρ = P._,_ id id
qfree-sem (k dvd e) ρ = P._,_ id id
qfree-sem (e₁ lt e₂) ρ = P._,_ id id
qfree-sem (e₁ gt e₂) ρ = P._,_ id id
qfree-sem (e₁ le e₂) ρ = P._,_ id id
qfree-sem (e₁ ge e₂) ρ = P._,_ id id
qfree-sem (e₁ eq e₂) ρ = P._,_ id id
qfree-sem (not φ) ρ with qfree φ | qfree-sem φ ρ
... | ψ , Hψ | P._,_ P Q = P._,_ (λ x x' → x (Q x')) (λ x x' → x (P x'))
qfree-sem (ex φ) ρ  with qfree φ | qfree-sem φ
... | ψ , Hψ | λPQ = P._,_ (λ H → P.proj₁ (QfreeCooper (ψ , Hψ) ρ) (P._,_ (P.proj₁ H) (P.proj₁ (λPQ ((P.proj₁ H) ∷ ρ)) (P.proj₂ H)))) (λ H → P._,_ (P.proj₁ (P.proj₂ (QfreeCooper (ψ , Hψ) ρ) H)) (P.proj₂ (λPQ (_ ∷ ρ)) (P.proj₂ (P.proj₂ (QfreeCooper (ψ , Hψ) ρ) H))))
qfree-sem (all φ) ρ with qfree-sem φ | qneg-sem (qfree φ) | QfreeCooper (qneg (qfree φ)) ρ | qneg-sem (qelim (qneg (qfree φ))) ρ
... | λPQ₁ | λPQ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ = P._,_ (λ ∀φ → P₂ (λ H → P.proj₂ (λPQ₂ ((P.proj₁ (Q₁ H)) ∷ ρ)) (P.proj₂ (Q₁ H)) (P.proj₁ (λPQ₁ (P.proj₁ (Q₁ H) ∷ ρ)) (∀φ (P.proj₁ (Q₁ H)))))) (λ H x → [ P.proj₂ (λPQ₁ (x ∷ ρ)) , (λ ¬qfφ → ⊥-elim (Q₂ H (P₁ (P._,_ x (P.proj₁ (λPQ₂ (x ∷ ρ)) ¬qfφ))))) ]′ (Qfree-EM (qfree φ) (x ∷ ρ)))
qfree-sem (φ₁ and φ₂) ρ with qfree φ₁ | qfree φ₂ | qfree-sem φ₁ ρ | qfree-sem φ₂ ρ
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ = P._,_ (λ H → P._,_ (P₁ (P.proj₁ H)) (P₂ (P.proj₂ H))) (λ H → P._,_ (Q₁ (P.proj₁ H)) (Q₂ (P.proj₂ H)))
qfree-sem (φ₁ or φ₂) ρ with qfree φ₁ | qfree φ₂ | qfree-sem φ₁ ρ | qfree-sem φ₂ ρ
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ = P._,_ [ inj₁ ∘ P₁ , inj₂ ∘ P₂ ]′ [ inj₁ ∘ Q₁ , inj₂ ∘ Q₂ ]′
qfree-sem (φ₁ ⇀ φ₂) ρ with qfree φ₁ | qfree φ₂ | qfree-sem φ₁ ρ | qfree-sem φ₂ ρ
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ = P._,_ (λ x x' → P₂ (x (Q₁ x'))) (λ x x' → Q₂ (x (P₁ x')))