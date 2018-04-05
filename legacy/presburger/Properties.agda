module Properties where

open import Data.Nat as ℕ
open import Data.Integer as ℤ 
open import Data.Fin as F
open import Data.Empty
open import Product
open import Data.Sum
open import Data.Vec

open import Data.Integer.Divisibility

open import Relation.Binary.PropositionalEquality

open import Representation
open import Comparisons

-----
-- Notations
-----

≠0 : ℤ → Set
≠0 k = k ≡ + 0 → ⊥

≠0-abs : ∀ {k : ℤ} → ≠0 k → ≠0 (+ ∣ k ∣)
≠0-abs {+ .0} pr refl = pr refl
≠0-abs { -[1+ n ]} pr ()

Notnull : Set
Notnull = Σ ℤ ≠0

∣_∣≠ : Notnull → Notnull
∣ σ , Hσ ∣≠ = + ∣ σ ∣ , ≠0-abs Hσ

:0 : {n : ℕ} → exp n
:0 {n} = val {n} (+ 0)

:1 : {n : ℕ} → exp n
:1 {n} = val {n} (+ 1)

-----
-- To be quantifier free
-----

data isqfree {n : ℕ} : form n → Set where
  T-isqfree : isqfree T
  F-isqfree : isqfree F
  :<-isqfree : ∀ {t₁ t₂ : exp n} → isqfree (t₁ :< t₂)
  :>-isqfree : ∀ {t₁ t₂ : exp n} → isqfree (t₁ :> t₂)
  :≤-isqfree : ∀ {t₁ t₂ : exp n} → isqfree (t₁ :≤ t₂)
  :≥-isqfree : ∀ {t₁ t₂ : exp n} → isqfree (t₁ :≥ t₂)
  :≡-isqfree : ∀ {t₁ t₂ : exp n} → isqfree (t₁ :≡ t₂)
  :|-isqfree : ∀ {k : ℤ} {t₁ : exp n} → isqfree (k :| t₁)
  :¬-isqfree : ∀ {φ : form n} (pr : isqfree φ) → isqfree (:¬ φ)
  :∧-isqfree : ∀ {φ₁ φ₂ : form n} (pr₁ : isqfree φ₁) (pr₂ : isqfree φ₂) → isqfree (φ₁ :∧ φ₂)
  :∨-isqfree : ∀ {φ₁ φ₂ : form n} (pr₁ : isqfree φ₁) (pr₂ : isqfree φ₂) → isqfree (φ₁ :∨ φ₂)
  :→-isqfree : ∀ {φ₁ φ₂ : form n} (pr₁ : isqfree φ₁) (pr₂ : isqfree φ₂) → isqfree (φ₁ :→ φ₂)

-----
-- To be in negation normal form
-----

data isnnf {n : ℕ} : form n → Set where
  T-isnnf : isnnf (T {n})
  F-isnnf : isnnf (F {n})
  :≤-isnnf : ∀ {t₁ t₂ : exp n} → isnnf (t₁ :≤ t₂)
  :≡-isnnf : ∀ {t₁ t₂ : exp n} → isnnf (t₁ :≡ t₂)
  :≢-isnnf : ∀ {t₁ t₂ : exp n} → isnnf (:¬ (t₁ :≡ t₂))
  :|-isnnf : ∀ {k : ℤ} {t₁ : exp n} → isnnf (k :| t₁)
  :|̸-isnnf : ∀ {k : ℤ} {t₁ : exp n} → isnnf (:¬ (k :| t₁))
  :∧-isnnf : ∀ {φ₁ φ₂ : form n} (pr₁ : isnnf φ₁) (pr₂ : isnnf φ₂) → isnnf (φ₁ :∧ φ₂)
  :∨-isnnf : ∀ {φ₁ φ₂ : form n} (pr₁ : isnnf φ₁) (pr₂ : isnnf φ₂) → isnnf (φ₁ :∨ φ₂)

-----
-- To be linear
-----

data islinn-i {n : ℕ} : ∀ (n₀ : ℕ) (e : exp n) → Set where
  val-islinn-i : ∀ {n₀} {k : ℤ} → islinn-i n₀ (val {n} k)
  var-islinn-i : ∀ {n₀} {k : ℤ} {p : Fin n} {r : exp n} (k≠0 : ≠0 k)
                 (n₀≤p : n₀ ℕ.≤ toℕ p) (pr : islinn-i (ℕ.suc (toℕ p)) r) →
                  islinn-i n₀ ((k :* var p) :+  r)

data islin {n : ℕ} : form n → Set where
  T-islin : islin T
  F-islin : islin F
  :≤-islin : ∀ {t₁ : exp n} (pr : islinn-i zero t₁) → islin (t₁ :≤ :0)
  :≡-islin : ∀ {t₁ : exp n} (pr : islinn-i zero t₁) → islin (t₁ :≡ :0)
  :≢-islin : ∀ {t₁ : exp n} (pr : islinn-i zero t₁) → islin (:¬ (t₁ :≡ :0))
  :|-islin : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : islinn-i zero t₁) → islin (k :| t₁)
  :|̸-islin : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : islinn-i zero t₁) → islin (:¬ (k :| t₁))
  :∧-islin : ∀ {φ₁ φ₂ : form n} (pr₁ : islin φ₁) (pr₂ : islin φ₂) → islin (φ₁ :∧ φ₂)
  :∨-islin : ∀ {φ₁ φ₂ : form n} (pr₁ : islin φ₁) (pr₂ : islin φ₂) → islin (φ₁ :∨ φ₂)

-----
-- To be unitary
-----

data div-exp   : ∀ {n : ℕ} (σ : Notnull) (e : exp n) → Set where
  val-div-exp  : ∀ {n k σ} → div-exp {n} σ (val k)
  varn-div-exp : ∀ {n σ} {t : exp n} {p : ℕ} (pr : islinn-i (ℕ.suc p) t) → div-exp σ t
  var0-div-exp : ∀ {n σ} {t : exp (ℕ.suc n)} {k} (k∣ : k ∣ (proj₁ σ)) (pr : islinn-i 1 t) →
                 div-exp σ ((k :* (var zero)) :+ t)

data divall {n : ℕ} (σ : Notnull) : form n → Set where
  T-divall : divall σ T
  F-divall : divall σ F
  :≤-divall : ∀ {t₁ : exp n} (pr : div-exp σ t₁) → divall σ (t₁ :≤ :0)
  :≡-divall : ∀ {t₁ : exp n} (pr : div-exp σ t₁) → divall σ (t₁ :≡ :0)
  :≢-divall : ∀ {t₁ : exp n} (pr : div-exp σ t₁) → divall σ (:¬ (t₁ :≡ :0))
  :|-divall : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : div-exp σ t₁) → divall σ (k :| t₁)
  :|̸-divall : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : div-exp σ t₁) → divall σ (:¬ (k :| t₁))
  :∧-divall : ∀ {φ₁ φ₂ : form n} (pr₁ : divall σ φ₁) (pr₂ : divall σ φ₂) → divall σ (φ₁ :∧ φ₂)
  :∨-divall : ∀ {φ₁ φ₂ : form n} (pr₁ : divall σ φ₁) (pr₂ : divall σ φ₂) → divall σ (φ₁ :∨ φ₂)

data isunit : {n : ℕ} → exp n → Set where
  val-isunit :  ∀ {n k} → isunit (val {n} k)
  varn-isunit : ∀ {n} {t : exp n} {p : ℕ} (pr : islinn-i (ℕ.suc p) t) → isunit t
  var0-isunit : ∀ {n} {t : exp (ℕ.suc n)} {k} (k1 : ∣ k ∣ ≡ 1) (pr : islinn-i 1 t) →
                isunit ((k :* (var zero)) :+ t)

data isunitary {n : ℕ} : form n → Set where
  T-isunitary : isunitary (T {n})
  F-isunitary : isunitary (F {n})
  :≤-isunitary : ∀ {t₁} (pr : isunit t₁) → isunitary (t₁ :≤ :0)
  :≡-isunitary : ∀ {t₁} (pr : isunit t₁) → isunitary (t₁ :≡ :0)
  :≢-isunitary : ∀ {t₁ : exp n} (pr : isunit t₁) → isunitary (:¬ (t₁ :≡ :0))
  :|-isunitary : ∀ {k : ℤ} {t₁ : exp n} (k≠0 : ≠0 k) (pr : isunit t₁) → isunitary (k :| t₁)
  :|̸-isunitary : ∀ {k : ℤ} {t₁ : exp n} (k≠0 : ≠0 k) (pr : isunit t₁) → isunitary (:¬ (k :| t₁))
  :∧-isunitary : ∀ {φ₁ φ₂ : form n} (pr₁ : isunitary φ₁) (pr₂ : isunitary φ₂) → isunitary (φ₁ :∧ φ₂)
  :∨-isunitary : ∀ {φ₁ φ₂ : form n} (pr₁ : isunitary φ₁) (pr₂ : isunitary φ₂) → isunitary (φ₁ :∨ φ₂)

data contains0-exp : {n : ℕ} → exp n → Set where
  var0-contains0 : ∀ {n} {t : exp (ℕ.suc n)} {k : ℤ} → islinn-i 1 t →
                   contains0-exp ((k :* (var zero)) :+ t)

data contains0 {n : ℕ} : form n → Set where
  :≤-contains0 : ∀ {t₁ : exp n} → contains0-exp t₁ → contains0 (t₁ :≤ :0)
  :≡-isunitary : ∀ {t₁ : exp n} → contains0-exp t₁ → contains0 (t₁ :≡ :0)
  :≢-isunitary : ∀ {t₁ : exp n} → contains0-exp t₁ → contains0 (:¬ (t₁ :≡ :0))
  :|-isunitary : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) → contains0-exp t₁ → contains0 (k :| t₁)
  :|̸-isunitary : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) → contains0-exp t₁ → contains0 (:¬ (k :| t₁))
  :∧-isunitary : ∀ {φ₁ φ₂ : form n} (pr : contains0 φ₁ ⊎ contains0 φ₂) → contains0 (φ₁ :∧ φ₂)
  :∨-isunitary : ∀ {φ₁ φ₂ : form n} (pr : contains0 φ₁ ⊎ contains0 φ₂) → contains0 (φ₁ :∨ φ₂)

-----
-- Almost free from (var zero)
-----

data free0-exp {n : ℕ} : exp n → Set where
  val-free0 : ∀ {k} → free0-exp (val {n} k)
  varn-free0 : ∀ {t : exp n} {p : ℕ} (pr : islinn-i (ℕ.suc p) t) → free0-exp t

data allmost-free0 {n : ℕ} : form n → Set where
  T-allmost : allmost-free0 (T {n})
  F-allmost : allmost-free0 (F {n})
  :≤-allmost : ∀ {t₁ : exp n} (pr : free0-exp t₁) → allmost-free0 (t₁ :≤ :0)
  :≡-allmost : ∀ {t₁ : exp n} (pr : free0-exp t₁) → allmost-free0 (t₁ :≡ :0)
  :≢-allmost : ∀ {t₁ : exp n} (pr : free0-exp t₁) → allmost-free0 (:¬ (t₁ :≡ :0))
  :|-allmost : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : isunit t₁) → allmost-free0 (k :| t₁)
  :|̸-allmost : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : isunit t₁) → allmost-free0 (:¬ (k :| t₁))
  :∧-allmost : ∀ {φ₁ φ₂ : form n} (pr₁ : allmost-free0 φ₁) (pr₂ : allmost-free0 φ₂) →
               allmost-free0 (φ₁ :∧ φ₂)
  :∨-allmost : ∀ {φ₁ φ₂ : form n} (pr₁ : allmost-free0 φ₁) (pr₂ : allmost-free0 φ₂) →
               allmost-free0 (φ₁ :∨ φ₂)

-----
-- 
-----

data alldvd {n : ℕ} (σ : Notnull) : form n → Set where
  T-alldvd : alldvd σ (T {n})
  F-alldvd : alldvd σ (F {n})
  :≤-alldvd : ∀ {t₁ : exp n} → alldvd σ (t₁ :≤ :0)
  :≡-alldvd : ∀ {t₁ : exp n} → alldvd σ (t₁ :≡ :0)
  :≢-alldvd : ∀ {t₁ : exp n} → alldvd σ (:¬ (t₁ :≡ :0))
  :|-alldvd : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : k ∣ (proj₁ σ)) → alldvd σ (k :| t₁)
  :|̸-alldvd : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : k ∣ (proj₁ σ)) → alldvd σ (:¬ (k :| t₁))
  :∧-alldvd : ∀ {φ₁ φ₂ : form n} (pr₁ : alldvd σ φ₁) (pr₂ : alldvd σ φ₂) → alldvd σ (φ₁ :∧ φ₂)
  :∨-alldvd : ∀ {φ₁ φ₂ : form n} (pr₁ : alldvd σ φ₁) (pr₂ : alldvd σ φ₂) → alldvd σ (φ₁ :∨ φ₂)

-----
-- Data structures
-----

Qfree : ℕ → Set
Qfree n = Σ (form n) isqfree

Nnf : ℕ → Set
Nnf n = Σ (form n) isnnf

Lin′ : ℕ → ℕ → Set
Lin′ n p =  Σ (exp n) (islinn-i p)

Lin : ℕ → Set
Lin n = Σ (form n) islin

Une : ℕ → Set
Une n = Σ (exp n) isunit

Unf : ℕ → Set
Unf n = Σ (form n) isunitary

Af0 : ℕ → Set
Af0 n = Σ (form n) allmost-free0

Zfe : ℕ → Set
Zfe n = Σ (exp n) free0-exp

Dall : {n : ℕ} → form n → Set
Dall φ = Σ Notnull (λ σ → alldvd σ φ)
