module problem.properties-prop where

open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Fin as F

open import Data.Empty
open import Data.Product

open import Data.Nat.Divisibility as ℕ∣
open import Data.Integer.Divisibility as ℤ∣

open import Relation.Binary.PropositionalEquality

open import Relation.Binary
private module Pos = Poset ℕ∣.poset
private module ℕ≤ = DecTotalOrder ℕ.decTotalOrder

open import problem.definition
open import problem.properties

abstract

-----
-- Inclusion of some subsets in others
-----

  nnf-qfree : ∀ {n} {φ : form n} → nnf φ → qfree φ
  nnf-qfree :≤-nnf = :≤-qf
  nnf-qfree :≡-nnf = :≡-qf
  nnf-qfree :≢-nnf = :¬-qf :≡-qf
  nnf-qfree :|-nnf = :|-qf
  nnf-qfree :|̸-nnf = :¬-qf :|-qf
  nnf-qfree (:∧-nnf pr₁ pr₂) = :∧-qf (nnf-qfree pr₁) (nnf-qfree pr₂)
  nnf-qfree (:∨-nnf pr₁ pr₂) = :∨-qf (nnf-qfree pr₁) (nnf-qfree pr₂)

  lin-nnf : ∀ {n} {φ : form n} → lin φ → nnf φ
  lin-nnf (:≤-lin pr) = :≤-nnf
  lin-nnf (:≡-lin pr) = :≡-nnf
  lin-nnf (:≢-lin pr) = :≢-nnf
  lin-nnf (:|-lin k≠0 pr) = :|-nnf
  lin-nnf (:|̸-lin k≠0 pr) = :|̸-nnf
  lin-nnf (:∧-lin pr₁ pr₂) = :∧-nnf (lin-nnf pr₁) (lin-nnf pr₂)
  lin-nnf (:∨-lin pr₁ pr₂) = :∨-nnf (lin-nnf pr₁) (lin-nnf pr₂)

  uni-≠0 : ∀ {k} → ∣ k ∣ ≡ 1 → ≠0 k
  uni-≠0 () refl

  elin-weakening : ∀ {n p₁ p₂} {e : exp n} → p₂ ℕ.≤ p₁ → elin p₁ e → elin p₂ e
  elin-weakening H≤ val-elin = val-elin
  elin-weakening H≤ (var-elin k≠0 n₀≤p pr) = var-elin k≠0 (ℕ≤.trans H≤ n₀≤p) pr

  euni-elin : ∀ {n} {e : exp n} → euni e → elin 0 e
  euni-elin val-euni = val-elin
  euni-elin (varn-euni pr) = elin-weakening z≤n pr
  euni-elin (var0-euni k1 pr) = var-elin (uni-≠0 k1) z≤n pr

  elin-euni : ∀ {n p} {e : exp n} → elin (ℕ.suc p) e → euni e
  elin-euni val-elin = val-euni
  elin-euni (var-elin k≠0 n₀≤p pr) = varn-euni (var-elin k≠0 n₀≤p pr)

  uni-lin : ∀ {n} {φ : form n} → uni φ → lin φ
  uni-lin (:≤-uni pr) = :≤-lin (euni-elin pr)
  uni-lin (:≡-uni pr) = :≡-lin (euni-elin pr)
  uni-lin (:≢-uni pr) = :≢-lin (euni-elin pr)
  uni-lin (:|-uni k≠0 pr) = :|-lin k≠0 (euni-elin pr)
  uni-lin (:|̸-uni k≠0 pr) = :|̸-lin k≠0 (euni-elin pr)
  uni-lin (:∧-uni pr₁ pr₂) = :∧-lin (uni-lin pr₁) (uni-lin pr₂)
  uni-lin (:∨-uni pr₁ pr₂) = :∨-lin (uni-lin pr₁) (uni-lin pr₂)
  
  eaf0-euni : ∀ {n} {e : exp n} → eaf0 e → euni e
  eaf0-euni val-eaf0 = val-euni
  eaf0-euni (var-eaf0 pr) = varn-euni pr

  af0-uni : ∀ {n} {φ : form n} → af0 φ → uni φ
  af0-uni (:≤-af0 pr) = :≤-uni (eaf0-euni pr)
  af0-uni (:≡-af0 pr) = :≡-uni (eaf0-euni pr)
  af0-uni (:≢-af0 pr) = :≢-uni (eaf0-euni pr)
  af0-uni (:|-af0 k≠0 pr) = :|-uni k≠0 pr
  af0-uni (:|̸-af0 k≠0 pr) = :|̸-uni k≠0 pr
  af0-uni (:∧-af0 pr₁ pr₂) = :∧-uni (af0-uni pr₁) (af0-uni pr₂)
  af0-uni (:∨-af0 pr₁ pr₂) = :∨-uni (af0-uni pr₁) (af0-uni pr₂)

-----
-- Lifting
-----

  ediv-ext : ∀ {n} {m : Notnull} {e : exp n} (pr : ediv m e) →
                ∀ (p : Notnull) (Hdiv : (proj₁ m) ℤ∣.∣ (proj₁ p)) → ediv p e
  ediv-ext val-ediv p H| = val-ediv
  ediv-ext (varn-ediv pr) p' H| = varn-ediv pr
  ediv-ext (var0-ediv k∣ pr) p H| = var0-ediv (Pos.trans k∣ H|) pr

  div-ext : ∀ {n} {m : Notnull} {φ : form n} (pr : div m φ) →
               ∀ (p : Notnull) → (proj₁ m) ℤ∣.∣ (proj₁ p) → div p φ
  div-ext (:≤-div pr) p H| = :≤-div (ediv-ext pr p H|)
  div-ext (:≡-div pr) p H| = :≡-div (ediv-ext pr p H|)
  div-ext (:≢-div pr) p H| = :≢-div (ediv-ext pr p H|)
  div-ext (:|-div k≠0 pr) p H| = :|-div k≠0 (ediv-ext pr p H|)
  div-ext (:|̸-div k≠0 pr) p H| = :|̸-div k≠0 (ediv-ext pr p H|)
  div-ext (:∧-div pr₁ pr₂) p H| = :∧-div (div-ext pr₁ p H|) (div-ext pr₂ p H|)
  div-ext (:∨-div pr₁ pr₂) p H| = :∨-div (div-ext pr₁ p H|) (div-ext pr₂ p H|)

  adv-ext : ∀ {n} {m : Notnull} {φ : form n} (pr : adv m φ) →
               ∀ (p : Notnull) → (proj₁ m) ℤ∣.∣ (proj₁ p) → adv p φ
  adv-ext :≤-adv p H| = :≤-adv
  adv-ext :≡-adv p H| = :≡-adv
  adv-ext :≢-adv p H| = :≢-adv
  adv-ext (:|-adv k≠0 pr) p H| = :|-adv k≠0 (Pos.trans pr H|)
  adv-ext (:|̸-adv k≠0 pr) p H| = :|̸-adv k≠0 (Pos.trans pr H|)
  adv-ext (:∧-adv pr₁ pr₂) p H| = :∧-adv (adv-ext pr₁ p H|) (adv-ext pr₂ p H|)
  adv-ext (:∨-adv pr₁ pr₂) p H| = :∨-adv (adv-ext pr₁ p H|) (adv-ext pr₂ p H|)

  adv-abs : ∀ {n} {m : Notnull} {φ : form n} → adv m φ → adv ∣ m ∣≠ φ
  adv-abs {n} {m , Hm} pr = adv-ext pr ∣ m , Hm ∣≠ Pos.refl