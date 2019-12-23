module Normalization.LCMReduction where

-- Things specific to the solver
open import Properties
open import Properties-prop

-- Datatypes
import Data.Nat.Properties as NProp
import Data.Nat.LCM as LCM
open import Data.Integer as ℤ using (ℤ)
open import Data.Integer.Divisibility.Signed
open import Data.Fin as Fin using (Fin)
import Data.Nat.Divisibility as Ndiv
open import Data.Product as Prod


div-E : ∀ {n n₀ e} → Lin-E {n} n₀ e → ∃ λ σ → Div-E σ e
div-E (val k)                       = 1≠0 , val k
div-E (k *var Fin.zero  [ prf ]+ e) = (-, k) , _ [ ∣-refl ]*var0+ e
div-E (k *var Fin.suc p [ prf ]+ e) =
  1≠0 , c*varn Fin.toℕ p + (k *var Fin.suc p [ NProp.≤-refl ]+ e)

div : ∀ {n φ} → Lin {n} φ → ∃ λ σ → Div σ φ
div T        = 1≠0 , T
div F        = 1≠0 , F
div (e :≤0)  = Prod.map₂ _:≤0 (div-E e)
div (e :≡0)  = Prod.map₂ _:≡0 (div-E e)
div (e :≢0)  = Prod.map₂ _:≢0 (div-E e)
div (k :| e) = Prod.map₂ (k :|_) (div-E e)
div (k :|̸ e) = Prod.map₂ (k :|̸_) (div-E e)
div (p :∧ q) =
  let (k , p')      = div p; (l , q') = div q
      (d , prf)     = LCM.mkLCM ℤ.∣ proj₁ k ∣ ℤ.∣ proj₁ l ∣
      (prfk , prfl) = LCM.LCM.commonMultiple prf
  in (ℤ.+ d , lcm≠0 (proj₂ k) (proj₂ l))
   , (∣ᵤ⇒∣ prfk ∣-Div p') :∧ (∣ᵤ⇒∣ prfl ∣-Div q')
div (p :∨ q) =
  let (k , p') = div p; (l , q') = div q
      (d , prf) = LCM.mkLCM ℤ.∣ proj₁ k ∣ ℤ.∣ proj₁ l ∣
      (prfk , prfl) = LCM.LCM.commonMultiple prf
  in (ℤ.+ d , lcm≠0 (proj₂ k) (proj₂ l))
   , (∣ᵤ⇒∣ prfk ∣-Div p') :∨ (∣ᵤ⇒∣ prfl ∣-Div q')
