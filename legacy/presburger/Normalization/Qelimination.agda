module Normalization.Qelimination where

open import Representation
open import Properties
open import Properties-prop
open import Product
open import Function

-- About ≡ and Dec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- Datatypes
open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)


postulate qelim : ∀ {n} (φ : Qfree (ℕs n)) → Qfree n

qneg : ∀ {n} (φ : Qfree n) → Qfree n
qneg (.T , T-isqfree) = F , F-isqfree
qneg (.F , F-isqfree) = T , T-isqfree
qneg (.(t₁ lt t₂) , lt-isqfree {t₁} {t₂}) = t₁ ge t₂ , ge-isqfree
qneg (.(t₁ gt t₂) , gt-isqfree {t₁} {t₂}) = t₁ le t₂ , le-isqfree
qneg (.(t₁ le t₂) , le-isqfree {t₁} {t₂}) = t₁ gt t₂ , gt-isqfree
qneg (.(t₁ ge t₂) , ge-isqfree {t₁} {t₂}) = t₁ lt t₂ , lt-isqfree
qneg (.(t₁ eq t₂) , eq-isqfree {t₁} {t₂}) = not (t₁ eq t₂) , not-isqfree eq-isqfree
qneg (.(k dvd t₁) , dvd-isqfree {k} {t₁}) = not (k dvd t₁) , not-isqfree dvd-isqfree
qneg (.(not φ) , not-isqfree {φ} y) = (φ , y)
qneg (.(φ₁ and φ₂) , and-isqfree {φ₁} {φ₂} y y') with qneg (φ₁ , y) | qneg (φ₂ , y')
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ or ψ₂ , or-isqfree Hψ₁ Hψ₂
qneg (.(φ₁ or φ₂) , or-isqfree {φ₁} {φ₂} y y') with qneg (φ₁ , y) | qneg (φ₂ , y')
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ and ψ₂ , and-isqfree Hψ₁ Hψ₂
qneg (.(φ₁ ⇀ φ₂) , ⇀-isqfree {φ₁} {φ₂} y y') with qneg (φ₂ , y')
... | ψ₂ , Hψ₂ = φ₁ and ψ₂ , and-isqfree y Hψ₂

qfree : ∀ {n} (φ : form n) → Qfree n
qfree T = T , T-isqfree
qfree F = F , F-isqfree
qfree (k dvd e) = k dvd e , dvd-isqfree
qfree (e₁ lt e₂) = e₁ lt e₂ , lt-isqfree
qfree (e₁ gt e₂) = e₁ gt e₂ , gt-isqfree
qfree (e₁ le e₂) = e₁ le e₂ , le-isqfree
qfree (e₁ ge e₂) = e₁ ge e₂ , ge-isqfree
qfree (e₁ eq e₂) = e₁ eq e₂ , eq-isqfree
qfree (not φ) with qfree φ
... | ψ , Hψ = not ψ , not-isqfree Hψ
qfree (ex φ) = qelim (qfree φ)
qfree (all φ) = (qneg ∘ qelim ∘ qneg) (qfree φ)
qfree (φ₁ and φ₂) with qfree φ₁ | qfree φ₂
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ and ψ₂ , and-isqfree Hψ₁ Hψ₂
qfree (φ₁ or φ₂) with qfree φ₁ | qfree φ₂
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ or ψ₂ , or-isqfree Hψ₁ Hψ₂
qfree (φ₁ ⇀ φ₂) with qfree φ₁ | qfree φ₂
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ ⇀ ψ₂ , ⇀-isqfree Hψ₁ Hψ₂