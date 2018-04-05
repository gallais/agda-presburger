module Semantics-prop where

open import Data.Nat renaming (suc to ℕs ; pred to P ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_)
open import Data.Integer renaming (suc to ℤs ; _+_ to _ℤ+_ ; _-_ to _ℤ-_ ; _*_ to _ℤ*_ ; _≤_ to _ℤ≤_)
open import Data.Fin renaming (suc to Fs)

open import Relation.Binary.PropositionalEquality

open import Product
open import Data.Vec

open import Representation
open import Properties
open import Semantics

abstract

  context-simpl : ∀ {n p} (e : Lin′ (ℕs n) (ℕs p)) x₁ x₂ ρ →
                  ⟦ proj₁ e ⟧e (x₁ ∷ ρ) ≡ ⟦ proj₁ e ⟧e (x₂ ∷ ρ)
  context-simpl {n} {p} (.(val k) , val-islinn-i {.(ℕs p)} {k}) x₁ x₂ ρ = refl
  context-simpl {n} {p} (.((k :* var zero) :+ r) ,
    var-islinn-i {.(ℕs p)} {k} {zero} {r} k≠0 () pr) x₁ x₂ ρ
  context-simpl {n} {p} (.((k :* var (Fs i)) :+ r) ,
    var-islinn-i {.(ℕs p)} {k} {Fs i} {r} k≠0 n₀≤p pr) x₁ x₂ ρ =
    subst (λ e → ⟦ k :* var i ⟧e ρ ℤ+ ⟦ r ⟧e (x₁ ∷ ρ) ≡ ⟦ k :* var i ⟧e ρ ℤ+ e)
          (context-simpl (r , pr) x₁ x₂ ρ) refl