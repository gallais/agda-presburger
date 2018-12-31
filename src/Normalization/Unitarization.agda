module Normalization.Unitarization where

-- Things specific to the solver
open import Properties
open import Normalization.Linearisation

-- Datatypes
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Divisibility as Ndiv

open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ZProp
open import Data.Integer.Divisibility.Signed

open import Data.Product as Prod
open import Data.Empty
import Data.Sign as S

open import Function
open import Relation.Binary.PropositionalEquality

-- The common factor we are using

unit-k : ∀ {σ n e} → Div-E σ {n} e → ℕ
unit-k (val k)             = 1
unit-k (c*varn p + e)      = 1
unit-k (k [ k∣σ ]*var0+ e) = Ndiv.quotient (∣⇒∣ᵤ k∣σ)

unit-k-pos : ∀ {σ n t} (e : Div-E σ {n} t) → unit-k e ≡ ℕ.suc (ℕ.pred (unit-k e))
unit-k-pos (val k)             = refl
unit-k-pos (c*varn p + e)      = refl
unit-k-pos {σ} (k [ k∣σ ]*var0+ e)
  with Ndiv.quotient (∣⇒∣ᵤ k∣σ)
     | Ndiv._∣_.equality (∣⇒∣ᵤ k∣σ)
... | ℕ.zero  | eq = ⊥-elim (to≢0 (proj₂ σ) (ZProp.∣n∣≡0⇒n≡0 eq))
... | ℕ.suc p | eq = refl

unit-k≠0 : ∀ {σ n t} (e : Div-E σ {n} t) → ℤ.+ (unit-k e) ≠0
unit-k≠0 e = from≢0 (subst (λ k → ℤ.+ k ≢ ℤ.+ 0) (sym (unit-k-pos e)) λ ())

-- Unitarization itself

unit-E : ∀ {σ n e} → Div-E σ e → ∃ (Unit-E {n})
unit-E (val k)                = -, val k
unit-E (c*varn p + e)         = -, varn p + e
unit-E {σ , σ≠0} (k [ k∣σ ]*var0+ e) =
  let s = ℤ.sign k S.* ℤ.sign σ
      q = Ndiv.quotient (∣⇒∣ᵤ k∣σ)
  in -, (s ℤ.◃ 1) [ fromAbs (ZProp.abs-◃ s 1) ]*var0+ proj₂ ((ℤ.+ q) *E e)

unit : ∀ {σ n φ} → Div {n} σ φ → ∃ (Unit {n})
unit T        = -, T
unit F        = -, F
unit (e :≤0)  = -, proj₂ (unit-E e) :≤0
unit (e :≡0)  = -, proj₂ (unit-E e) :≡0
unit (e :≢0)  = -, proj₂ (unit-E e) :≢0
unit (k :| e) = -, [ unit-k≠0 e * k ≠0] :| proj₂ (unit-E e)
unit (k :|̸ e) = -, [ unit-k≠0 e * k ≠0] :|̸ proj₂ (unit-E e)
unit (p :∧ q) = -, proj₂ (unit p) :∧ proj₂ (unit q)
unit (p :∨ q) = -, proj₂ (unit p) :∨ proj₂ (unit q)
