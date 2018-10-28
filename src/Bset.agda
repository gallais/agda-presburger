module Bset where

open import Representation
open import Properties
open import Properties-prop
open import Normalization.Linearisation
open import Minusinf
open import AllmostFree-prop

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)
open import Data.Product as Product
open import Data.List as List
open import Function

open import Relation.Binary.PropositionalEquality hiding ([_])

bset : ∀ {n φ} → Unit {n} φ → List (∃ (Lin-E {n} 1))
bset (:-1 [ prf ]*var0+ e :≤0) = [ e            +E val :-1 ]
bset (:+1 [ prf ]*var0+ e :≡0) = [ proj₂ (-E e) +E val :-1 ]
bset (:-1 [ prf ]*var0+ e :≡0) = [ e            +E val :-1 ]
bset (:+1 [ prf ]*var0+ e :≢0) = [ -E e                    ]
bset (:-1 [ prf ]*var0+ e :≢0) = [ -, e                    ]
bset (e :∧ f) = bset e ++ bset f
bset (e :∨ f) = bset e ++ bset f
bset _ = []

bjset : ∀ {n p φ} → Unit {n} φ → Fin p → List (∃ (Lin-E {n} 1))
bjset φ j = List.map ((_+E val (ℤ.+ Fin.toℕ j)) ∘ proj₂) (bset φ)

jset : ∀ {n f} → Unit {n} f → ℕ
jset φ = ℕ.suc ℤ.∣ proj₁ (proj₁ $ lcm-:∣′ (proj₂ $ var0⟶-∞ φ)) ∣
