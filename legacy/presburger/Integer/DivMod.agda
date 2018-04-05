module Integer.DivMod where

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_)
open import Data.Integer as Int hiding (_≟_) renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

open import Data.Sign hiding (_≟_) renaming (- to S- ; + to S+ ; _*_ to _S*_)
open import Data.Nat.Divisibility renaming (_∣_ to _ℕdiv_)
open import Data.Nat.DivMod
open import Data.Nat.Properties as NatProp
open import Data.Empty
open import Data.Product

open import Fin-prop
open import Integer.Basic-Properties
open import Integer.Order-Properties

open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (isEquivalence)

open import Algebra.Structures
import Integer.Structures as IntProp
private module ℕr = IsCommutativeSemiring NatProp.isCommutativeSemiring
private module ℤr = IsCommutativeRing IntProp.isCommutativeRing

_ℤdiv_ : ∀ (dividend : ℤ) (divisor : ℕ) {≠0 : divisor ≡ 0 → ⊥} → ℤ
(_ ℤdiv zero) {H} = ⊥-elim (H refl)
-[1+ n ] ℤdiv (ℕs k) with (ℕs n) divMod' (ℕs k)
-[1+ n ] ℤdiv ℕs k | result q zero eq = - (+ q)
-[1+ n ] ℤdiv ℕs k | result q (Fs i) eq = -[1+ q ]
((+ n) ℤdiv (ℕs k)) with n divMod' (ℕs k)
(+ n) ℤdiv ℕs k | result q r eq = + q

_ℤmod_ : ∀ (dividend : ℤ) (divisor : ℕ) {≠0 : divisor ≡ 0 → ⊥} → Fin divisor
(_ ℤmod zero) {H} = ⊥-elim (H refl)
-[1+ n ] ℤmod ℕs k with (ℕs n) divMod' (ℕs k)
-[1+ n ] ℤmod ℕs k | result q zero eq = zero
-[1+ n ] ℤmod ℕs k | result q (Fs i) eq = Fin-inv (inject₁ i)
(+ n) ℤmod ℕs k with n divMod' (ℕs k)
(+ n) ℤmod ℕs k | result q r eq = r

abstract

  ℤmod-correct-neg : ∀ (n q k : ℕ) (r : Fin q) → ℕs n ≡ k ℕ* q ℕ+ (toℕ r) → -[1+ n ] ≡ (- (+ k)) ℤ* (+ q) ℤ+ (- (+ toℕ r))
  ℤmod-correct-neg n q k r H = subst (λ u → - (+ ℕs n) ≡ u ℤ+ - (+ toℕ r)) (-distr-ℤ*-l (+ k) (+ q)) (subst₂ (λ u v → - (+ u) ≡ v) (sym H) (-distr-ℤ+ (+ k ℤ* + q) (+ toℕ r)) (subst (λ u → - (+ (k ℕ* q ℕ+ toℕ r)) ≡ - (u ℤ+ + toℕ r)) (ℕ*-ℤ* k q) refl))

  ℤmod-ℤdiv-correction : ∀ p k {≠0 : k ≡ 0 → ⊥} → p ≡ (p ℤdiv k) {≠0} ℤ* (+ k) ℤ+ (+ (toℕ ((p ℤmod k) {≠0})))
  ℤmod-ℤdiv-correction p zero {H} = ⊥-elim (H refl)
  ℤmod-ℤdiv-correction -[1+ n ] (ℕs k) with (ℕs n) divMod' (ℕs k)
  ℤmod-ℤdiv-correction -[1+ n ] (ℕs k) | result q zero eq = ℤmod-correct-neg n (ℕs k) q zero (subst (λ u → ℕs n ≡ u) (sym (proj₂ ℕr.+-identity (q ℕ* ℕs k))) eq)
  ℤmod-ℤdiv-correction -[1+ n ] (ℕs k) | result q (Fs i) eq with ℕs (toℕ i ℕ+ q ℕ* ℕs k) | ℕr.+-comm (toℕ (Fs i)) (q ℕ* ℕs k)
  ... | .(q ℕ* ℕs k ℕ+ (toℕ (Fs i))) | refl = subst₂ (λ u v → - (+ ℕs n) ≡ - (+ u) ℤ+ v) (ℕr.+-comm (q ℕ* ℕs k) (ℕs k)) (opp-invol (+ toℕ (Fin-inv (inject₁ i)))) (subst (λ u → - (+ ℕs n) ≡ u) (-distr-ℤ+ (+ (q ℕ* ℕs k ℕ+ ℕs k)) (- (+ toℕ ((Fin-inv (inject₁ i)))))) (cong {_} {_} {_} {_} (λ x → - x) {+ ℕs n} {+ (q ℕ* (ℕs k) ℕ+ ℕs k) ℤ+ - (+ toℕ (Fin-inv (inject₁ i)))} (subst (λ u → + ℕs n ≡ + (q ℕ* ℕs k ℕ+ ℕs k) ℤ+ - u) (sym (Fin-inv-sem (inject₁ i))) (subst (λ u → + ℕs n ≡ + (q ℕ* ℕs k ℕ+ ℕs k) ℤ+ u) (sym (-⊖-compat k (toℕ (inject₁ i)))) (subst₂ (λ u v → + u ≡ v) (sym eq) (sym (ℤr.+-assoc (+ (q ℕ* ℕs k)) (+ ℕs k) ((ℕs (toℕ (inject₁ i))) ⊖ (ℕs k)))) (ℤ+-left {+ (q ℕ* ℕs k)} ((subst₂ (λ u v → + ℕs u ≡ + ℕs k ℤ+ v) (toℕ-inject₁ i) (ℤr.+-comm (- (+ ℕs k)) (+ ℕs (toℕ (inject₁ i)))) (subst (λ u → + ℕs (toℕ (inject₁ i)) ≡ u) (ℤr.+-assoc (+ ℕs k) (- (+ ℕs k)) (+ ℕs (toℕ (inject₁ i)))) (subst (λ u → + ℕs (toℕ (inject₁ i)) ≡ u ℤ+ + ℕs (toℕ (inject₁ i))) (sym (n⊖n k)) refl))))))))))
  ℤmod-ℤdiv-correction (+ n) (ℕs k) with n divMod' (ℕs k)
  ℤmod-ℤdiv-correction (+ .(toℕ r ℕ+ q ℕ* ℕs k)) (ℕs k) | result q r refl = subst₂ (λ u v → + u ≡ v ℤ+ + toℕ r) (ℕr.+-comm (q ℕ* ℕs k) (toℕ r)) (ℕ*-ℤ* q (ℕs k)) refl
