module Cooper.LinCooper-prop where

open import Representation
open import Properties
open import Semantics
open import Semantics-prop
open import Equivalence
open import Normalization.LCMReduction
open import Normalization.Unitarization
open import Normalization.Unitarization-prop
open import Cooper.LinCooper
open import Cooper.UnfCooper-prop

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ZProp
open import Data.Integer.Divisibility.Signed
open import Data.Fin as Fin using (Fin)

open import Data.Product
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as VP
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.Reasoning.MultiSetoid

abstract

  private
    module LocalDefs {n : ℕ} {f2 : form (ℕ.suc n)} (φ : Lin {ℕ.suc n} f2) (ρ : Vec ℤ n) where
      f        = toForm Lin φ
      σ∣φ      = div φ
      σ∧≠0     = proj₁ σ∣φ
      σ        = proj₁ σ∧≠0
      σ≠0      = proj₂ σ∧≠0
      divφ     = proj₂ σ∣φ
      g∧ψ      = unit divφ
      g        = proj₁ g∧ψ
      ⟦g∧ψ⟧    = ⟦unit divφ ⟧ ρ
      ψ        = proj₂ g∧ψ
      σ∣var0   : form (ℕ.suc n)
      σ∣var0   = σ :| :+1 :* var Fin.zero :+ val (ℤ.+ 0)
      σ∣var0-u : Unit σ∣var0
      σ∣var0-u = σ≠0 :| :+1 [ ∣+1∣ ]*var0+ val (ℤ.+ 0)

      σ∣σ*x : ∀ x → σ ∣ x ↔ ⟦ σ∣var0 ⟧ (x ∷ ρ)
      σ∣σ*x x = begin⟨ ↔-setoid ⟩
        σ ∣ x                   ≡⟨ cong (σ ∣_) (P.sym (ZProp.*-identityˡ x)) ⟩
        σ ∣ :+1 ℤ.* x           ≡⟨ cong (σ ∣_) (P.sym (ZProp.+-identityʳ (:+1 ℤ.* x))) ⟩
        σ ∣ :+1 ℤ.* x ℤ.+ ℤ.+ 0 ∎

      forward : ⟦ :∃ f ⟧ ρ → ⟦ :∃ σ∣var0 :∧ g ⟧ ρ
      forward (x , pr) = σ ℤ.* x
                       , proj₁ (σ∣σ*x (σ ℤ.* x)) (∣m⇒∣m*n x ∣-refl)
                       , proj₁ ⟦g∧ψ⟧ pr

      backward : ⟦ :∃ σ∣var0 :∧ g ⟧ ρ → ⟦ :∃ f ⟧ ρ
      backward (x , σ∣var0 , pr) = k , proj₂ ⟦g∧ψ⟧ (⟦ g ⟧-ext₁ x≡σ*k pr) where

        σ|x   = proj₂ (σ∣σ*x x) σ∣var0
        k     = quotient σ|x
        x≡σ*k = P.trans (_∣_.equality σ|x) (ZProp.*-comm k σ)

  ⟦Lin-qelim_⟧ : ∀ {n f} (φ : Lin {ℕ.suc n} f) → :∃ f ⇔ proj₁ (Lin-qelim φ)
  ⟦Lin-qelim φ ⟧ ρ = begin⟨ ↔-setoid ⟩
    ⟦ :∃ f ⟧ ρ                ≈⟨ forward , backward ⟩
    ⟦ :∃ σ∣var0 :∧ g ⟧ ρ      ≈⟨ ⟦Unf-qelim (σ∣var0-u :∧ ψ) ⟧ ρ ⟩
    ⟦ proj₁ (Lin-qelim φ) ⟧ ρ ∎ where
    open LocalDefs φ ρ
