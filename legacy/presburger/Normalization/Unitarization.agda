module Normalization.Unitarization where

-- Things specific to the solver
open import Properties
open import Normalization.Linearisation

-- Datatypes
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ZProp
import Data.Nat.Divisibility as Ndiv
open import Data.Product as Prod
import Data.Sign as S

unit-E : ∀ {σ n e} → Div-E σ e → ∃ (Unit-E {n})
unit-E (val k)                = -, val k
unit-E (c*varn p + e)         = -, varn p + e
unit-E {σ , σ≠0} (k [ k∣σ ]*var0+ e) =
  let s = ℤ.sign k S.* ℤ.sign σ
      q = Ndiv.quotient k∣σ
  in -, (s ℤ.◃ 1) [ ZProp.abs-◃ s 1 ]*var0+ proj₂ ((ℤ.+ q) *E e)

unit : ∀ {σ n φ} → Div {n} σ φ → ∃ (Unit {n})
unit T        = -, T
unit F        = -, F
unit (e :≤0)  = -, proj₂ (unit-E e) :≤0
unit (e :≡0)  = -, proj₂ (unit-E e) :≡0
unit (e :≢0)  = -, proj₂ (unit-E e) :≢0
unit (k :| e) = -, k :| proj₂ (unit-E e)
unit (k :|̸ e) = -, k :|̸ proj₂ (unit-E e)
unit (p :∧ q) = -, proj₂ (unit p) :∧ proj₂ (unit q)
unit (p :∨ q) = -, proj₂ (unit p) :∨ proj₂ (unit q)
