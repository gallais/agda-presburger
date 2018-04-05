module Integer.Modulo where

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_)
open import Data.Integer as Int hiding (_≟_) renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

open import Data.Sign hiding (_≟_) renaming (- to S- ; + to S+ ; _*_ to _S*_)
open import Data.Nat.Divisibility renaming (_∣_ to _ℕdiv_)
open import Data.Nat.Properties as NatProp
open import Data.Empty
open import Data.Product

open import Comparisons

open import Fin-prop
open import Integer.DivMod
open import Integer.Basic-Properties
open import Integer.Order-Properties

open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (isEquivalence)

open import Algebra.Structures
import Integer.Structures as IntProp
private module ℕr = IsCommutativeSemiring NatProp.isCommutativeSemiring
private module ℤr = IsCommutativeRing IntProp.isCommutativeRing

_≈_[_] : (x y : ℤ) (k : ℕ) → Set
x ≈ y [ k ] = k ℕdiv ∣ x ℤ- y ∣

abstract

  ≈-refl : ∀ {k x} → x ≈ x [ k ]
  ≈-refl {k} {x} = divides 0 (subst (λ u → ∣ u ∣ ≡ 0) (sym (unfold-ℤ- x x)) (subst (λ u → ∣ u ∣ ≡ 0) (sym (ℤ+-opp-r x)) refl))

  ≈-sym : ∀ {k i j} → i ≈ j [ k ] → j ≈ i [ k ]
  ≈-sym {k} {i} {j} (divides q eq) = divides q (subst (λ u → ∣ u ℤ- i ∣ ≡ q ℕ* k) (opp-invol j) (subst (λ u → ∣ u ∣ ≡ q ℕ* k) (-distr-ℤ+' (- j) i) (subst (λ u → u ≡ q ℕ* k) (sym (abs-opp-simpl (- j ℤ+ i))) (subst (λ u → ∣ u ∣ ≡ q ℕ* k) (ℤr.+-comm i (- j)) (subst (λ u → ∣ u ∣ ≡ q ℕ* k) (unfold-ℤ- i j) eq)))))

  ≈-trans : ∀ {k i j l} → i ≈ j [ k ] → j ≈ l [ k ] → i ≈ l [ k ]
  ≈-trans {k} {i} {j} {l} h₁ h₂ with div-elim (+ k) (i ℤ- j) h₁ | div-elim (+ k) (j ℤ- l) h₂
  ... | H₁ | H₂ = divides ∣ (proj₁ H₁) ℤ+ (proj₁ H₂) ∣ (subst (λ u → ∣ i ℤ- l ∣ ≡ u) (abs-distr-ℤ* (proj₁ H₁ ℤ+ (proj₁ H₂)) (+ k)) (subst (λ u → ∣ i ℤ- l ∣ ≡ ∣ u ∣) (sym (proj₂ ℤr.distrib (+ k) (proj₁ H₁) (proj₁ H₂))) (subst₂ (λ u v → ∣ i ℤ- l ∣ ≡ ∣ u ℤ+ v ∣) (proj₂ H₁) (proj₂ H₂) (subst₂ (λ u v → ∣ i ℤ- l ∣ ≡ ∣ u ℤ+ v ∣) (sym (unfold-ℤ- i j)) (sym (unfold-ℤ- j l)) (subst₂ (λ u v → ∣ u ∣ ≡ ∣ v ∣) (sym (unfold-ℤ- i l)) (sym (ℤr.+-assoc i (- j) (j ℤ+ - l))) (subst (λ u → ∣ i ℤ+ - l ∣ ≡ ∣ i ℤ+ u ∣) (ℤr.+-assoc (- j) j (- l)) (subst₂ (λ u v → ∣ i ℤ+ u ∣ ≡ ∣ i ℤ+ (v ℤ+ - l) ∣) (proj₁ ℤr.+-identity (- l)) (sym (ℤ+-opp-l j)) refl)))))))

  isEquivalence : ∀ {k} → IsEquivalence (λ x y → x ≈ y [ k ])
  isEquivalence {k} = record {
                refl = λ {x} → ≈-refl {k} {x} ;
                sym = λ {i} {j} → ≈-sym {k} {i} {j} ;
                trans = λ {i} {j} {l} → ≈-trans {k} {i} {j} {l} }

  ℤmod-≈ : ∀ p k {≠0 : k ≡ 0 → ⊥} → p ≈ + toℕ ((p ℤmod k) {≠0}) [ k ]
  ℤmod-≈ p k {≠0}with ℤmod-ℤdiv-correction p k {≠0}
  ... | H = divides ∣ (p ℤdiv k) {≠0} ∣ (subst₂ (λ u v → ∣ u ℤ- + toℕ ((p ℤmod k) {≠0}) ∣  ≡ v) (sym H) (abs-distr-ℤ* ((p ℤdiv k) {≠0}) (+ k)) (subst (λ u → ∣ u ∣ ≡ ∣ ((p ℤdiv k) {≠0}) ℤ* (+ k) ∣) (sym (unfold-ℤ- ((((p ℤdiv k) {≠0}) ℤ* (+ k)) ℤ+ (+ toℕ ((p ℤmod k) {≠0}))) (+ toℕ ((p ℤmod k) {≠0})))) (subst (λ u → ∣ u ∣ ≡ ∣ ((p ℤdiv k) {≠0}) ℤ* (+ k) ∣) (sym (ℤr.+-assoc (((p ℤdiv k) {≠0}) ℤ* (+ k)) (+ toℕ ((p ℤmod k) {≠0})) (- (+ toℕ ((p ℤmod k) {≠0}))))) (subst₂ (λ u v → ∣ ((p ℤdiv k) {≠0}) ℤ* (+ k) ℤ+ u ∣ ≡ ∣ v ∣) (sym (ℤ+-opp-r (+ toℕ (p ℤmod k)))) (proj₂ ℤr.+-identity (((p ℤdiv k) {≠0}) ℤ* (+ k))) refl))))