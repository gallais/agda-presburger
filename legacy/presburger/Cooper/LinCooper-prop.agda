module Cooper.LinCooper-prop where

import Cooper.LinCooper as LC
import Cooper.UnfCooper-prop as UC
open import Representation
open import Properties
open import Semantics
open import Equivalence using (_⇔_)
import Normalization.Unitarization as Uni
import Normalization.Unitarization-prop as Unip

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_ ; _≤?_ to _ℕ≤?_ ; _≟_ to _ℕ≟_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_ ; _≤?_ to _ℤ≤?_ ; _≟_ to _ℤ≟_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

import Integer.Structures as IntStruct using (isCommutativeSemiring ; ℤ+-isGroup)

import Data.Product as P
open import Product
import Data.Vec as V

open import Relation.Binary.PropositionalEquality
import Algebra.Structures as Struct

private module ℤ+g = Struct.IsGroup IntStruct.ℤ+-isGroup
private module ℤsr = Struct.IsCommutativeSemiring IntStruct.isCommutativeSemiring
private module ℤ*m = Struct.IsCommutativeMonoid ℤsr.*-isCommutativeMonoid

abstract
  Lin-cooper : ∀ {n} (φ : Lin (ℕs n)) → ex (proj₁ φ) ⇔ proj₁ (LC.Lin-qelim φ)
  Lin-cooper φ ρ with Uni.lcmφ φ | Uni.unitarise φ | Unip.unitarise-sem φ ρ
  ... | P._,_ (l , neq) Hl | ψ , Hψ | P._,_ P₁ Q₁ with UC.Unf-cooper (((l dvd (((+ 1) :* var zero) :+ val (+ 0))) and ψ) , and-isunitary (dvd-isunitary neq (var0-isunit refl val-islinn-i)) Hψ) ρ
  ... | P._,_ P₂ Q₂ = P._,_ (λ h → P₂ (P._,_ (P.proj₁ (P₁ h)) (P._,_ (P._,_ (P.proj₁ (P.proj₁ (P.proj₂ (P₁ h)))) (subst (λ u → u ≡ l ℤ* (P.proj₁ (P.proj₁ (P.proj₂ (P₁ h))))) (sym ((P.proj₂ (ℤ+g.identity)) (sign (P.proj₁ (P₁ h)) ◃ ∣ P.proj₁ (P₁ h) ∣ ℕ+ 0))) (subst (λ u → u ≡ l ℤ* (P.proj₁ (P.proj₁ (P.proj₂ (P₁ h))))) (sym (ℤ*m.identityˡ (P.proj₁ (P₁ h)))) (P.proj₂ (P.proj₁ (P.proj₂ (P₁ h))))))) (P.proj₂ (P.proj₂ (P₁ h)))))) (λ h → Q₁ ((P._,_ (P.proj₁ (Q₂ h)) (P._,_ (P._,_ (P.proj₁ (P.proj₁ (P.proj₂ (Q₂ h)))) (subst (λ u → u ≡ l ℤ* (P.proj₁ (P.proj₁ (P.proj₂ (Q₂ h))))) (ℤ*m.identityˡ (P.proj₁ (Q₂ h))) (subst (λ u → u ≡ l ℤ* (P.proj₁ (P.proj₁ (P.proj₂ (Q₂ h))))) ((P.proj₂ (ℤ+g.identity)) (sign (P.proj₁ (Q₂ h)) ◃ ∣ P.proj₁ (Q₂ h) ∣ ℕ+ 0)) (P.proj₂ (P.proj₁ (P.proj₂ (Q₂ h))))))) (P.proj₂ (P.proj₂ (Q₂ h)))))))