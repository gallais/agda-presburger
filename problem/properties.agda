module problem.properties where

{- The procedure works by successive transformation of problems
   into constrained subsets. Each transformation leads towards
   simpler problems.
   These properties describe the different subset used. -}

open import Data.Nat as ℕ
open import Data.Integer as ℤ 
open import Data.Fin as F
open import Data.Vec

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Integer.Divisibility

open import Relation.Binary.PropositionalEquality

open import problem.definition

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

_*v0 : (k : ℤ) {n : ℕ} → exp (ℕ.suc n)
k *v0 = k :* var zero

-----
-- To be quantifier free
-----

data qfree {n : ℕ} : form n → Set where
  :<-qf : ∀ {t₁ t₂ : exp n} → qfree (t₁ :< t₂)
  :>-qf : ∀ {t₁ t₂ : exp n} → qfree (t₁ :> t₂)
  :≤-qf : ∀ {t₁ t₂ : exp n} → qfree (t₁ :≤ t₂)
  :≥-qf : ∀ {t₁ t₂ : exp n} → qfree (t₁ :≥ t₂)
  :≡-qf : ∀ {t₁ t₂ : exp n} → qfree (t₁ :≡ t₂)
  :|-qf : ∀ {k : ℤ} {t₁ : exp n} → qfree (k :| t₁)
  :¬-qf : ∀ {φ : form n} (pr : qfree φ) → qfree (:¬ φ)
  :∧-qf : ∀ {φ₁ φ₂ : form n} (pr₁ : qfree φ₁) (pr₂ : qfree φ₂) → qfree (φ₁ :∧ φ₂)
  :∨-qf : ∀ {φ₁ φ₂ : form n} (pr₁ : qfree φ₁) (pr₂ : qfree φ₂) → qfree (φ₁ :∨ φ₂)
  :→-qf : ∀ {φ₁ φ₂ : form n} (pr₁ : qfree φ₁) (pr₂ : qfree φ₂) → qfree (φ₁ :→ φ₂)

-----
-- To be in negation normal form
-----

data nnf {n : ℕ} : form n → Set where
  :≤-nnf : ∀ {t₁ t₂ : exp n} → nnf (t₁ :≤ t₂)
  :≡-nnf : ∀ {t₁ t₂ : exp n} → nnf (t₁ :≡ t₂)
  :≢-nnf : ∀ {t₁ t₂ : exp n} → nnf (:¬ (t₁ :≡ t₂))
  :|-nnf : ∀ {k : ℤ} {t₁ : exp n} → nnf (k :| t₁)
  :|̸-nnf : ∀ {k : ℤ} {t₁ : exp n} → nnf (:¬ (k :| t₁))
  :∧-nnf : ∀ {φ₁ φ₂ : form n} (pr₁ : nnf φ₁) (pr₂ : nnf φ₂) → nnf (φ₁ :∧ φ₂)
  :∨-nnf : ∀ {φ₁ φ₂ : form n} (pr₁ : nnf φ₁) (pr₂ : nnf φ₂) → nnf (φ₁ :∨ φ₂)

-----
-- To be linear
-----

data elin {n : ℕ} : ∀ (n₀ : ℕ) (e : exp n) → Set where
  val-elin : ∀ {n₀} {k : ℤ} → elin n₀ (val {n} k)
  var-elin : ∀ {n₀} {k : ℤ} {p : Fin n} {r : exp n} (k≠0 : ≠0 k)
                 (n₀≤p : n₀ ℕ.≤ toℕ p) (pr : elin (ℕ.suc (toℕ p)) r) →
                  elin n₀ ((k :* var p) :+  r)

data lin {n : ℕ} : form n → Set where
  :≤-lin : ∀ {t₁ : exp n} (pr : elin zero t₁) → lin (t₁ :≤ :0)
  :≡-lin : ∀ {t₁ : exp n} (pr : elin zero t₁) → lin (t₁ :≡ :0)
  :≢-lin : ∀ {t₁ : exp n} (pr : elin zero t₁) → lin (:¬ (t₁ :≡ :0))
  :|-lin : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : elin zero t₁) → lin (k :| t₁)
  :|̸-lin : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : elin zero t₁) → lin (:¬ (k :| t₁))
  :∧-lin : ∀ {φ₁ φ₂ : form n} (pr₁ : lin φ₁) (pr₂ : lin φ₂) → lin (φ₁ :∧ φ₂)
  :∨-lin : ∀ {φ₁ φ₂ : form n} (pr₁ : lin φ₁) (pr₂ : lin φ₂) → lin (φ₁ :∨ φ₂)

-----
-- To be a common multiple of all the [var 0] coefficients
-----

data ediv   : ∀ {n : ℕ} (σ : Notnull) (e : exp n) → Set where
  val-ediv  : ∀ {n k σ} → ediv {n} σ (val k)
  varn-ediv : ∀ {n σ} {t : exp n} {p : ℕ} (pr : elin (ℕ.suc p) t) → ediv σ t
  var0-ediv : ∀ {n σ} {t : exp (ℕ.suc n)} {k} (k∣ : k ∣ (proj₁ σ)) (pr : elin 1 t) →
                 ediv σ (k *v0 :+ t)

data div {n : ℕ} (σ : Notnull) : form n → Set where
  :≤-div : ∀ {t₁ : exp n} (pr : ediv σ t₁) → div σ (t₁ :≤ :0)
  :≡-div : ∀ {t₁ : exp n} (pr : ediv σ t₁) → div σ (t₁ :≡ :0)
  :≢-div : ∀ {t₁ : exp n} (pr : ediv σ t₁) → div σ (:¬ (t₁ :≡ :0))
  :|-div : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : ediv σ t₁) → div σ (k :| t₁)
  :|̸-div : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : ediv σ t₁) → div σ (:¬ (k :| t₁))
  :∧-div : ∀ {φ₁ φ₂ : form n} (pr₁ : div σ φ₁) (pr₂ : div σ φ₂) → div σ (φ₁ :∧ φ₂)
  :∨-div : ∀ {φ₁ φ₂ : form n} (pr₁ : div σ φ₁) (pr₂ : div σ φ₂) → div σ (φ₁ :∨ φ₂)

-----
-- To be unitary
-----

data euni : {n : ℕ} → exp n → Set where
  val-euni :  ∀ {n k} → euni (val {n} k)
  varn-euni : ∀ {n} {t : exp n} {p : ℕ} (pr : elin (ℕ.suc p) t) → euni t
  var0-euni : ∀ {n} {t : exp (ℕ.suc n)} {k} (k1 : ∣ k ∣ ≡ 1) (pr : elin 1 t) →
                euni (k *v0 :+ t)

data uni {n : ℕ} : form n → Set where
  :≤-uni : ∀ {t₁} (pr : euni t₁) → uni (t₁ :≤ :0)
  :≡-uni : ∀ {t₁} (pr : euni t₁) → uni (t₁ :≡ :0)
  :≢-uni : ∀ {t₁ : exp n} (pr : euni t₁) → uni (:¬ (t₁ :≡ :0))
  :|-uni : ∀ {k : ℤ} {t₁ : exp n} (k≠0 : ≠0 k) (pr : euni t₁) → uni (k :| t₁)
  :|̸-uni : ∀ {k : ℤ} {t₁ : exp n} (k≠0 : ≠0 k) (pr : euni t₁) → uni (:¬ (k :| t₁))
  :∧-uni : ∀ {φ₁ φ₂ : form n} (pr₁ : uni φ₁) (pr₂ : uni φ₂) → uni (φ₁ :∧ φ₂)
  :∨-uni : ∀ {φ₁ φ₂ : form n} (pr₁ : uni φ₁) (pr₂ : uni φ₂) → uni (φ₁ :∨ φ₂)

-----
-- To be containing at least one [var 0]
-----

data einc0 : {n : ℕ} → exp n → Set where
  var0 : ∀ {n} {t : exp (ℕ.suc n)} {k : ℤ} → elin 1 t → einc0 (k *v0 :+ t)

data inc0 {n : ℕ} : form n → Set where
  :≤-inc0 : ∀ {t₁ : exp n} → einc0 t₁ → inc0 (t₁ :≤ :0)
  :≡-inc0 : ∀ {t₁ : exp n} → einc0 t₁ → inc0 (t₁ :≡ :0)
  :≢-inc0 : ∀ {t₁ : exp n} → einc0 t₁ → inc0 (:¬ (t₁ :≡ :0))
  :|-inc0 : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) → einc0 t₁ → inc0 (k :| t₁)
  :|̸-inc0 : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) → einc0 t₁ → inc0 (:¬ (k :| t₁))
  :∧-inc0 : ∀ {φ₁ φ₂ : form n} (pr : inc0 φ₁ ⊎ inc0 φ₂) → inc0 (φ₁ :∧ φ₂)
  :∨-inc0 : ∀ {φ₁ φ₂ : form n} (pr : inc0 φ₁ ⊎ inc0 φ₂) → inc0 (φ₁ :∨ φ₂)

-----
-- Almost free from [var 0]
-----

data eaf0 {n : ℕ} : exp n → Set where
  val-eaf0 : ∀ {k} → eaf0 (val {n} k)
  var-eaf0 : ∀ {t : exp n} {p : ℕ} (pr : elin (ℕ.suc p) t) → eaf0 t

data af0 {n : ℕ} : form n → Set where
  :≤-af0 : ∀ {t₁ : exp n} (pr : eaf0 t₁) → af0 (t₁ :≤ :0)
  :≡-af0 : ∀ {t₁ : exp n} (pr : eaf0 t₁) → af0 (t₁ :≡ :0)
  :≢-af0 : ∀ {t₁ : exp n} (pr : eaf0 t₁) → af0 (:¬ (t₁ :≡ :0))
  :|-af0 : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : euni t₁) → af0 (k :| t₁)
  :|̸-af0 : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : euni t₁) → af0 (:¬ (k :| t₁))
  :∧-af0 : ∀ {φ₁ φ₂ : form n} (pr₁ : af0 φ₁) (pr₂ : af0 φ₂) → af0 (φ₁ :∧ φ₂)
  :∨-af0 : ∀ {φ₁ φ₂ : form n} (pr₁ : af0 φ₁) (pr₂ : af0 φ₂) → af0 (φ₁ :∨ φ₂)

-----
-- To be a common multiple of all the [k]s in [k :| something] expressions
-----

data adv {n : ℕ} (σ : Notnull) : form n → Set where
  :≤-adv : ∀ {t₁ : exp n} → adv σ (t₁ :≤ :0)
  :≡-adv : ∀ {t₁ : exp n} → adv σ (t₁ :≡ :0)
  :≢-adv : ∀ {t₁ : exp n} → adv σ (:¬ (t₁ :≡ :0))
  :|-adv : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : k ∣ (proj₁ σ)) → adv σ (k :| t₁)
  :|̸-adv : ∀ {k} {t₁ : exp n} (k≠0 : ≠0 k) (pr : k ∣ (proj₁ σ)) → adv σ (:¬ (k :| t₁))
  :∧-adv : ∀ {φ₁ φ₂ : form n} (pr₁ : adv σ φ₁) (pr₂ : adv σ φ₂) → adv σ (φ₁ :∧ φ₂)
  :∨-adv : ∀ {φ₁ φ₂ : form n} (pr₁ : adv σ φ₁) (pr₂ : adv σ φ₂) → adv σ (φ₁ :∨ φ₂)


-----
-- Subsets of problems
-----

Qfree : ℕ → Set
Qfree n = Σ (form n) qfree

Nnf : ℕ → Set
Nnf n = Σ (form n) nnf

ELin : ℕ → ℕ → Set
ELin n p =  Σ (exp n) (elin p)

Lin : ℕ → Set
Lin n = Σ (form n) lin

EUni : ℕ → Set
EUni n = Σ (exp n) euni

Uni : ℕ → Set
Uni n = Σ (form n) uni

Af0 : ℕ → Set
Af0 n = Σ (form n) af0

EAf0 : ℕ → Set
EAf0 n = Σ (exp n) eaf0

Adv : {n : ℕ} → form n → Set
Adv φ = Σ Notnull (λ σ → adv σ φ)
