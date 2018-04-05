module Properties-prop where

open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Fin as F
open import Data.Empty
open import Product

open import Data.Nat.Divisibility as Div renaming (_∣_ to _ℕdiv_)
open import Data.Integer.Divisibility renaming (_∣_ to _ℤdiv_)

open import Relation.Binary.PropositionalEquality

open import Relation.Binary
private module Pos = Poset Div.poset
private module ℕ≤ = DecTotalOrder ℕ.decTotalOrder

open import Representation
open import Properties

abstract

-----
-- Implications
-----

  isnnf-isqfree : ∀ {n} {φ : form n} → isnnf φ → isqfree φ
  isnnf-isqfree T-isnnf = T-isqfree
  isnnf-isqfree F-isnnf = F-isqfree
  isnnf-isqfree :≤-isnnf = :≤-isqfree
  isnnf-isqfree :≡-isnnf = :≡-isqfree
  isnnf-isqfree :≢-isnnf = :¬-isqfree :≡-isqfree
  isnnf-isqfree :|-isnnf = :|-isqfree
  isnnf-isqfree :|̸-isnnf = :¬-isqfree :|-isqfree
  isnnf-isqfree (:∧-isnnf pr₁ pr₂) = :∧-isqfree (isnnf-isqfree pr₁) (isnnf-isqfree pr₂)
  isnnf-isqfree (:∨-isnnf pr₁ pr₂) = :∨-isqfree (isnnf-isqfree pr₁) (isnnf-isqfree pr₂)

  islin-isnnf : ∀ {n} {φ : form n} → islin φ → isnnf φ
  islin-isnnf T-islin = T-isnnf
  islin-isnnf F-islin = F-isnnf
  islin-isnnf (:≤-islin pr) = :≤-isnnf
  islin-isnnf (:≡-islin pr) = :≡-isnnf
  islin-isnnf (:≢-islin pr) = :≢-isnnf
  islin-isnnf (:|-islin k≠0 pr) = :|-isnnf
  islin-isnnf (:|̸-islin k≠0 pr) = :|̸-isnnf
  islin-isnnf (:∧-islin pr₁ pr₂) = :∧-isnnf (islin-isnnf pr₁) (islin-isnnf pr₂)
  islin-isnnf (:∨-islin pr₁ pr₂) = :∨-isnnf (islin-isnnf pr₁) (islin-isnnf pr₂)

  unitary-≠0 : ∀ {k} → ∣ k ∣ ≡ 1 → ≠0 k
  unitary-≠0 () refl

  islinn-i-weakening : ∀ {n p₁ p₂} {e : exp n} → p₂ ℕ.≤ p₁ → islinn-i p₁ e → islinn-i p₂ e
  islinn-i-weakening H≤ val-islinn-i = val-islinn-i
  islinn-i-weakening H≤ (var-islinn-i k≠0 n₀≤p pr) = var-islinn-i k≠0 (ℕ≤.trans H≤ n₀≤p) pr

  isunit-islinn-i : ∀ {n} {e : exp n} → isunit e → islinn-i 0 e
  isunit-islinn-i val-isunit = val-islinn-i
  isunit-islinn-i (varn-isunit pr) = islinn-i-weakening z≤n pr
  isunit-islinn-i (var0-isunit k1 pr) = var-islinn-i (unitary-≠0 k1) z≤n pr

  islinn-i-isunit : ∀ {n p} {e : exp n} → islinn-i (ℕ.suc p) e → isunit e
  islinn-i-isunit val-islinn-i = val-isunit
  islinn-i-isunit (var-islinn-i k≠0 n₀≤p pr) = varn-isunit (var-islinn-i k≠0 n₀≤p pr)

  isunitary-islin : ∀ {n} {φ : form n} → isunitary φ → islin φ
  isunitary-islin T-isunitary = T-islin
  isunitary-islin F-isunitary = F-islin
  isunitary-islin (:≤-isunitary pr) = :≤-islin (isunit-islinn-i pr)
  isunitary-islin (:≡-isunitary pr) = :≡-islin (isunit-islinn-i pr)
  isunitary-islin (:≢-isunitary pr) = :≢-islin (isunit-islinn-i pr)
  isunitary-islin (:|-isunitary k≠0 pr) = :|-islin k≠0 (isunit-islinn-i pr)
  isunitary-islin (:|̸-isunitary k≠0 pr) = :|̸-islin k≠0 (isunit-islinn-i pr)
  isunitary-islin (:∧-isunitary pr₁ pr₂) = :∧-islin (isunitary-islin pr₁) (isunitary-islin pr₂)
  isunitary-islin (:∨-isunitary pr₁ pr₂) = :∨-islin (isunitary-islin pr₁) (isunitary-islin pr₂)
  
  free0-exp-isunit : ∀ {n} {e : exp n} → free0-exp e → isunit e
  free0-exp-isunit val-free0 = val-isunit
  free0-exp-isunit (varn-free0 pr) = varn-isunit pr

  allmost-free0-isunitary : ∀ {n} {φ : form n} → allmost-free0 φ → isunitary φ
  allmost-free0-isunitary T-allmost = T-isunitary
  allmost-free0-isunitary F-allmost = F-isunitary
  allmost-free0-isunitary (:≤-allmost pr) = :≤-isunitary (free0-exp-isunit pr)
  allmost-free0-isunitary (:≡-allmost pr) = :≡-isunitary (free0-exp-isunit pr)
  allmost-free0-isunitary (:≢-allmost pr) = :≢-isunitary (free0-exp-isunit pr)
  allmost-free0-isunitary (:|-allmost k≠0 pr) = :|-isunitary k≠0 pr
  allmost-free0-isunitary (:|̸-allmost k≠0 pr) = :|̸-isunitary k≠0 pr
  allmost-free0-isunitary (:∧-allmost pr₁ pr₂) =
    :∧-isunitary (allmost-free0-isunitary pr₁) (allmost-free0-isunitary pr₂)
  allmost-free0-isunitary (:∨-allmost pr₁ pr₂) =
    :∨-isunitary (allmost-free0-isunitary pr₁) (allmost-free0-isunitary pr₂)

-----
-- Lifting
-----

  div-exp-ext : ∀ {n} {m : Notnull} {e : exp n} (pr : div-exp m e) →
                ∀ (p : Notnull) (Hdiv : (proj₁ m) ℤdiv (proj₁ p)) → div-exp p e
  div-exp-ext val-div-exp p H| = val-div-exp
  div-exp-ext (varn-div-exp pr) p' H| = varn-div-exp pr
  div-exp-ext (var0-div-exp k∣ pr) p H| = var0-div-exp (Pos.trans k∣ H|) pr

  divall-ext : ∀ {n} {m : Notnull} {φ : form n} (pr : divall m φ) →
               ∀ (p : Notnull) → (proj₁ m) ℤdiv (proj₁ p) → divall p φ
  divall-ext T-divall p H| = T-divall
  divall-ext F-divall p H| = F-divall
  divall-ext (:≤-divall pr) p H| = :≤-divall (div-exp-ext pr p H|)
  divall-ext (:≡-divall pr) p H| = :≡-divall (div-exp-ext pr p H|)
  divall-ext (:≢-divall pr) p H| = :≢-divall (div-exp-ext pr p H|)
  divall-ext (:|-divall k≠0 pr) p H| = :|-divall k≠0 (div-exp-ext pr p H|)
  divall-ext (:|̸-divall k≠0 pr) p H| = :|̸-divall k≠0 (div-exp-ext pr p H|)
  divall-ext (:∧-divall pr₁ pr₂) p H| = :∧-divall (divall-ext pr₁ p H|) (divall-ext pr₂ p H|)
  divall-ext (:∨-divall pr₁ pr₂) p H| = :∨-divall (divall-ext pr₁ p H|) (divall-ext pr₂ p H|)

  alldvd-ext : ∀ {n} {m : Notnull} {φ : form n} (pr : alldvd m φ) →
               ∀ (p : Notnull) → (proj₁ m) ℤdiv (proj₁ p) → alldvd p φ
  alldvd-ext T-alldvd p H| = T-alldvd
  alldvd-ext F-alldvd p H| = F-alldvd
  alldvd-ext :≤-alldvd p H| = :≤-alldvd
  alldvd-ext :≡-alldvd p H| = :≡-alldvd
  alldvd-ext :≢-alldvd p H| = :≢-alldvd
  alldvd-ext (:|-alldvd k≠0 pr) p H| = :|-alldvd k≠0 (Pos.trans pr H|)
  alldvd-ext (:|̸-alldvd k≠0 pr) p H| = :|̸-alldvd k≠0 (Pos.trans pr H|)
  alldvd-ext (:∧-alldvd pr₁ pr₂) p H| = :∧-alldvd (alldvd-ext pr₁ p H|) (alldvd-ext pr₂ p H|)
  alldvd-ext (:∨-alldvd pr₁ pr₂) p H| = :∨-alldvd (alldvd-ext pr₁ p H|) (alldvd-ext pr₂ p H|)

  alldvd-abs : ∀ {n} {m : Notnull} {φ : form n} → alldvd m φ → alldvd ∣ m ∣≠ φ
  alldvd-abs {n} {m , Hm} pr = alldvd-ext pr ∣ m , Hm ∣≠ Pos.refl