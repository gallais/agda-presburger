module Cooper.UnfCooper-prop where

open import Representation
open import Properties
open import Properties-prop
open import Semantics
open import Semantics-prop
open import Equivalence
open import AllmostFree-prop
open import Minusinf
open import Disjunction
open import Disjunction-prop
open import Cooper
open import Cooper.UnfCooper
open import Bset
open import Normalization.Linearisation
open import Normalization.Linearisation-prop

import Data.List as List
open import Data.List.Any as LAny using (Any; here; there)
import Data.List.Membership.Propositional as LMem
import Data.List.Any.Properties as LAnyProp
import Data.Vec.Any as VAny
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Any.Properties as VAnyProp
open import Data.Vec.Relation.Pointwise.Inductive as VecEq using (_∷_)

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FProp

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.SetoidReasoning as SR

⟦Unf-qelim-l₁_⟧ : ∀ {n f} (φ : Unit {ℕ.suc n} f) ρ →
    ⟦ :∃ f ⟧ ρ ↔ ((∃ λ (j : Fin (jset φ)) → ⟦ proj₁ (Unf-qelim-l₁ φ j) ⟧ ρ)
               ⊎ ⟦ :∃ (proj₁ (var0⟶-∞ φ)) ⟧ ρ)
⟦Unf-qelim-l₁ φ ⟧ ρ = forward , backward where

  f = toForm Unit φ

  ⟦_⟧ρ : ∃ Lin → Set
  ⟦ φ ⟧ρ = ⟦ proj₁ φ ⟧ ρ

  _+Fin_ : ∀ {n} (e : ∃ (Lin-E {n} 1)) (j : Fin (jset φ)) → ∃ (Lin-E {n} 1)
  e +Fin j = proj₂ e +E val (ℤ.+ Fin.toℕ j)

  ⟨_/0⟩φ : (e : ∃ (Lin-E 1)) → ∃ Lin
  ⟨ e /0⟩φ = ⟨ proj₂ e /0⟩ Unit-Lin φ

  φs : (j : Fin (jset φ)) → Vec (∃ Lin) _
  φs j = Vec.fromList
       $ List.map ⟨_/0⟩φ
       $ List.map (_+Fin j)
       $ bset φ

  ⟦_⟧+Fin : ∃ (Lin-E 1) → Fin _ → ℤ
  ⟦ b ⟧+Fin j = ⟦ proj₁ b ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ Fin.toℕ j

  equiv : ∀ j → ⟦ proj₁ (Unf-qelim-l₁ φ j) ⟧ ρ
        ↔ Any (λ b → ⟦ f ⟧ (⟦ b ⟧+Fin j ∷ ρ)) (bset φ)
  equiv j = begin⟨ ↔-setoid ⟩
    ⟦ proj₁ (Unf-qelim-l₁ φ j) ⟧ ρ
      ≈⟨ ⟦⋁ φs j ⟧ ρ ⟩
    VAny.Any ⟦_⟧ρ (φs j)
      ≈⟨ VAnyProp.fromList⁻ , VAnyProp.fromList⁺ ⟩
    Any ⟦_⟧ρ (List.map ⟨_/0⟩φ (List.map (_+Fin j) (bset φ)))
      ≈⟨ LAnyProp.map⁻ , LAnyProp.map⁺ ⟩
    Any (⟦_⟧ρ ∘ ⟨_/0⟩φ) (List.map (_+Fin j) (bset φ))
      ≈⟨ LAnyProp.map⁻ , LAnyProp.map⁺ ⟩
    Any (⟦_⟧ρ ∘ ⟨_/0⟩φ ∘ (_+Fin j)) (bset φ)
      ≈⟨ LAny.map (proj₂ (⟦⟨ _ /0⟩ Unit-Lin φ ⟧ ρ))
       , LAny.map (proj₁ (⟦⟨ _ /0⟩ Unit-Lin φ ⟧ ρ)) ⟩
    Any (λ z → ⟦ f ⟧ ((⟦ (z +Fin j) .proj₁ ⟧e (:+0 ∷ ρ)) ∷ ρ)) (bset φ)
      ≈⟨ LAny.map (λ {b} → ⟦ f ⟧-ext₁ (sym $ val-eq b))
       , LAny.map (λ {b} → ⟦ f ⟧-ext₁ (val-eq b)) ⟩
    Any (λ b → ⟦ f ⟧ (⟦ b ⟧+Fin j ∷ ρ)) (bset φ) ∎ where

      open SR

      val-eq : ∀ t → ⟦ t ⟧+Fin j ≡ ⟦ proj₁ (t +Fin j) ⟧e (:+0 ∷ ρ)
      val-eq t = ⟦ proj₂ t ⟧+E⟦ val (ℤ.+ Fin.toℕ j) ⟧ (:+0 ∷ ρ)

  forward : ⟦ :∃ f ⟧ ρ → ∃ (λ j → ⟦ proj₁ (Unf-qelim-l₁ φ j) ⟧ ρ)
                       ⊎ ⟦ :∃ proj₁ (var0⟶-∞ φ) ⟧ ρ
  forward pr with FProp.any? (λ j → NNF? (Lin-NNF (proj₂ (Unf-qelim-l₁ φ j))) ρ)
  ... | yes p = inj₁ p
  ... | no ¬p = inj₂ (cooper₁-simpl φ (proj₂ divφ) ρ aux (proj₁ pr) (proj₂ pr)) where

      aux = uncurry λ j pr → ¬p $′ (j ,_) $′ proj₂ (equiv j) pr
      divφ = lcm-:∣ (proj₂ $ var0⟶-∞ φ)

  backward : ∃ (λ j → ⟦ proj₁ (Unf-qelim-l₁ φ j) ⟧ ρ)
           ⊎ ⟦ :∃ proj₁ (var0⟶-∞ φ) ⟧ ρ → ⟦ :∃ f ⟧ ρ
  backward = [ (uncurry λ j pr → -, proj₂ (proj₂ (LMem.find (proj₁ (equiv j) pr))))
             , ⟦var0⟶-∞ φ ⟧ ρ ∘ proj₂ ]′ where

⟦Unf-qelim-l_⟧ : ∀ {n f} (φ : Unit {ℕ.suc n} f) →
                 :∃ f ⇔ (proj₁ (Unf-qelim-l φ) :∨ (:∃ proj₁ (var0⟶-∞ φ)))
⟦Unf-qelim-l φ ⟧ ρ =
  Sum.map₁ (proj₂ (⟦⋁[k< _ ] Unf-qelim-l₁ φ ⟧ ρ)) ∘′ proj₁ (⟦Unf-qelim-l₁ φ ⟧ ρ)
  , [ proj₂ (⟦Unf-qelim-l₁ φ ⟧ ρ) ∘′ inj₁ ∘′ proj₁ (⟦⋁[k< _ ] Unf-qelim-l₁ φ ⟧ ρ)
    , proj₂ (⟦Unf-qelim-l₁ φ ⟧ ρ) ∘′ inj₂ ]′

abstract

  ⟦Unf-qelim_⟧ : ∀ {n f} (φ : Unit {ℕ.suc n} f) → :∃ f ⇔ proj₁ (Unf-qelim φ)
  ⟦Unf-qelim φ ⟧ ρ =
    let (f^-∞ , φ^-∞) = var0⟶-∞ φ
        (σ , divφ^-∞) = lcm-:∣ φ^-∞
        (p₁ , q₁) = ⟦⋁ φ^-∞ when σ :| divφ^-∞ ⟧ ρ
        (p₂ , q₂) = ⟦Unf-qelim-l φ ⟧ ρ
    in Sum.map₂ p₁ ∘′ p₂
     , [ q₂ ∘′ inj₁ , q₂ ∘′ inj₂ ∘′ q₁ ]′
