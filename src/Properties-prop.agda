module Properties-prop where

open import Representation
open import Properties
open import Semantics

open import Data.Nat as ℕ
open import Data.Nat.Properties
import Data.Nat.Divisibility as Ndiv

open import Data.Integer as ℤ
import Data.Integer.Properties as ZProp
open import Data.Integer.Divisibility as Zdiv
open import Data.Integer.Divisibility.Properties as ZdivProp

open import Data.Fin as F
open import Data.Empty
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Binary

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Product
open import Relation.Nullary.Sum

abstract

-----
-- Implications
-----

  NNF-QFree : ∀ {n} {φ : form n} → NNF φ → QFree φ
  NNF-QFree T          = T
  NNF-QFree F          = F
  NNF-QFree (t₁ :≤ t₂) = t₁ :≤ t₂
  NNF-QFree (t₁ :≡ t₂) = t₁ :≡ t₂
  NNF-QFree (t₁ :≢ t₂) = :¬ (t₁ :≡ t₂)
  NNF-QFree (k :| t)   = k :| t
  NNF-QFree (k :|̸ t)   = :¬ (k :| t)
  NNF-QFree (p :∧ q)   = NNF-QFree p :∧ NNF-QFree q
  NNF-QFree (p :∨ q)   = NNF-QFree p :∨ NNF-QFree q

  Lin-NNF : ∀ {n} {φ : form n} → Lin φ → NNF φ
  Lin-NNF T        = T
  Lin-NNF F        = F
  Lin-NNF (t :≤0)  = _ :≤ val (+ zero)
  Lin-NNF (t :≡0)  = _ :≡ val (+ zero)
  Lin-NNF (t :≢0)  = _ :≢ val (+ zero)
  Lin-NNF (k :| t) = _ :| _
  Lin-NNF (k :|̸ t) = _ :|̸ _
  Lin-NNF (p :∧ q) = Lin-NNF p :∧ Lin-NNF q
  Lin-NNF (p :∨ q) = Lin-NNF p :∨ Lin-NNF q

  Unit-≠0 : ∀ {k} → ∣ k ∣≡1 → k ≠0
  Unit-≠0 ∣+1∣ = +[1+ zero ]
  Unit-≠0 ∣-1∣ = -[1+ zero ]

  Lin-E^wk : ∀ {n p₁ p₂} {e : exp n} → p₂ ℕ.≤ p₁ → Lin-E p₁ e → Lin-E p₂ e
  Lin-E^wk p₂≤p₁ (val k)               = val k
  Lin-E^wk p₂≤p₁ (k *var p [ prf ]+ e) = k *var p [ prf′ ]+ e
    where prf′ = ≤-trans p₂≤p₁ prf

  Unit-Lin-E : ∀ {n} {e : exp n} → Unit-E e → Lin-E 0 e
  Unit-Lin-E (val k)             = val k
  Unit-Lin-E (varn p + e)        = Lin-E^wk z≤n e
  Unit-Lin-E (k [ prf ]*var0+ e) = Unit-≠0 prf *var zero [ z≤n ]+ e

  Lin-Unit-E : ∀ {n p} {e : exp n} → Lin-E (ℕ.suc p) e → Unit-E e
  Lin-Unit-E (val k)               = val k
  Lin-Unit-E e@(_ *var _ [ _ ]+ _) = varn _ + e

  Unit-Lin : ∀ {n} {φ : form n} → Unit φ → Lin φ
  Unit-Lin T        = T
  Unit-Lin F        = F
  Unit-Lin (t :≤0)  = Unit-Lin-E t :≤0
  Unit-Lin (t :≡0)  = Unit-Lin-E t :≡0
  Unit-Lin (t :≢0)  = Unit-Lin-E t :≢0
  Unit-Lin (k :| t) = k :| Unit-Lin-E t
  Unit-Lin (k :|̸ t) = k :|̸ Unit-Lin-E t
  Unit-Lin (p :∧ q) = Unit-Lin p :∧ Unit-Lin q
  Unit-Lin (p :∨ q) = Unit-Lin p :∨ Unit-Lin q

  Free0-Unit-E : ∀ {n} {e : exp n} → Free0-E e → Unit-E e
  Free0-Unit-E (val k)      = val k
  Free0-Unit-E (varn p + e) = varn p + e

  Free0-Lin-E : ∀ {n e} → Free0-E {ℕ.suc n} e → ∃ λ p → Lin-E (ℕ.suc p) e
  Free0-Lin-E (val k)      = 1 , val k
  Free0-Lin-E (varn p + e) = p , e

  Free0-Unit : ∀ {n} {φ : form n} → Free0 φ → Unit φ
  Free0-Unit T        = T
  Free0-Unit F        = F
  Free0-Unit (e :≤0)  = Free0-Unit-E e :≤0
  Free0-Unit (e :≡0)  = Free0-Unit-E e :≡0
  Free0-Unit (e :≢0)  = Free0-Unit-E e :≢0
  Free0-Unit (k :| e) = k :| e
  Free0-Unit (k :|̸ e) = k :|̸ e
  Free0-Unit (p :∧ q) = Free0-Unit p :∧ Free0-Unit q
  Free0-Unit (p :∨ q) = Free0-Unit p :∨ Free0-Unit q

  Free0-Lin : ∀ {n φ} → Free0 {ℕ.suc n} φ → Lin φ
  Free0-Lin = Unit-Lin ∘′ Free0-Unit

-----
-- Lifting
-----

  infixl 2 _∣-Div-E_
  _∣-Div-E_ : ∀ {n σ τ e} → (proj₁ σ) ∣′ (proj₁ τ) → Div-E σ {n} e → Div-E τ e
  σ∣τ ∣-Div-E val k             = val k
  σ∣τ ∣-Div-E c*varn p + e      = c*varn p + e
  σ∣τ ∣-Div-E k [ k∣σ ]*var0+ e = k [ ∣′-trans k∣σ σ∣τ ]*var0+ e

  _∣-Div_ : ∀ {n σ τ φ} → (proj₁ σ) ∣′ (proj₁ τ) → Div {n} σ φ → Div τ φ
  σ∣τ ∣-Div T        = T
  σ∣τ ∣-Div F        = F
  σ∣τ ∣-Div (e :≤0)  = (σ∣τ ∣-Div-E e) :≤0
  σ∣τ ∣-Div (e :≡0)  = (σ∣τ ∣-Div-E e) :≡0
  σ∣τ ∣-Div (e :≢0)  = (σ∣τ ∣-Div-E e) :≢0
  σ∣τ ∣-Div (k :| e) = k :| (σ∣τ ∣-Div-E e)
  σ∣τ ∣-Div (k :|̸ e) = k :|̸ (σ∣τ ∣-Div-E e)
  σ∣τ ∣-Div (p :∧ q) = (σ∣τ ∣-Div p) :∧ (σ∣τ ∣-Div q)
  σ∣τ ∣-Div (p :∨ q) = (σ∣τ ∣-Div p) :∨ (σ∣τ ∣-Div q)

  _∣′-All∣′_ : ∀ {n σ τ φ} → (proj₁ σ) ∣′ (proj₁ τ) → All∣′ {n} σ φ → All∣′ τ φ
  σ∣′τ ∣′-All∣′ T               = T
  σ∣′τ ∣′-All∣′ F               = F
  σ∣′τ ∣′-All∣′ (t :≤0)         = t :≤0
  σ∣′τ ∣′-All∣′ (t :≡0)         = t :≡0
  σ∣′τ ∣′-All∣′ (t :≢0)         = t :≢0
  σ∣′τ ∣′-All∣′ (k∣′σ [ k ]:| t) = ∣′-trans k∣′σ σ∣′τ [ k ]:| t
  σ∣′τ ∣′-All∣′ (k∣′σ [ k ]:|̸ t) = ∣′-trans k∣′σ σ∣′τ [ k ]:|̸ t
  σ∣′τ ∣′-All∣′ (p :∧ q)        = (σ∣′τ ∣′-All∣′ p) :∧ (σ∣′τ ∣′-All∣′ q)
  σ∣′τ ∣′-All∣′ (p :∨ q)        = (σ∣′τ ∣′-All∣′ p) :∨ (σ∣′τ ∣′-All∣′ q)

  ∣_∣-All∣′ : ∀ {n σ φ} → All∣′ {n} σ φ → All∣′ ∣ σ ∣≠0 φ
  ∣ p ∣-All∣′ = m∣′∣m∣ ∣′-All∣′ p

-----
-- Decidability
-----

NNF? : ∀ {n f} (φ : NNF {n} f) ρ → Dec (⟦ f ⟧ ρ)
NNF? T        ρ = yes _
NNF? F        ρ = no λ ()
NNF? (t :≤ u) ρ = _ ZProp.≤? _
NNF? (t :≡ u) ρ = _ ZProp.≟ _
NNF? (t :≢ u) ρ = ¬? (_ ZProp.≟ _)
NNF? (k :| t) ρ = _ ZdivProp.∣′? _
NNF? (k :|̸ t) ρ = ¬? (_ ZdivProp.∣′? _)
NNF? (φ :∧ ψ) ρ = NNF? φ ρ ×-dec NNF? ψ ρ
NNF? (φ :∨ ψ) ρ = NNF? φ ρ ⊎-dec NNF? ψ ρ
