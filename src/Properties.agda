module Properties where

open import Data.Nat as ℕ
import Data.Nat.LCM as LCM
import Data.Nat.GCD as GCD
import Data.Nat.Properties as NProp
open import Data.Integer as ℤ
open import Data.Integer.Divisibility
import Data.Integer.Properties as ZProp
open import Data.Fin as F
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Representation

infix 20 _:≡0 _:≢0 _:≤0
infixr 20 _:|_ _:|̸_

-----
-- Notations
-----

infix 3 _≠0
data _≠0 : ℤ → Set where
  +[1+_] : ∀ k → + (ℕ.suc k) ≠0
  -[1+_] : ∀ k → -[1+ k ] ≠0

from≢0 : ∀ {k} → k ≢ + 0 → k ≠0
from≢0 {+ zero}    k≢0 = ⊥-elim (k≢0 refl)
from≢0 {+ suc n}   k≢0 = +[1+ n ]
from≢0 { -[1+ n ]} k≢0 = -[1+ n ]

to≢0 : ∀ {k} → k ≠0 → k ≢ + 0
to≢0 +[1+ k ] = λ ()
to≢0 -[1+ k ] = λ ()

infix 3 _≠0?
_≠0? : ∀ k → (k ≡ + 0) ⊎ (k ≠0)
+ zero    ≠0? = inj₁ refl
+ ℕ.suc n ≠0? = inj₂ +[1+ n ]
-[1+ n ]  ≠0? = inj₂ -[1+ n ]

toℤ : ∀ {k} → k ≠0 → ℤ
toℤ {k} _ = k

[_*_≠0] : ∀ {k l} → k ≠0 → l ≠0 → k ℤ.* l ≠0
[ +[1+ k ] * +[1+ l ] ≠0] = +[1+ l ℕ.+ k ℕ.* ℕ.suc l ]
[ +[1+ k ] * -[1+ l ] ≠0] = -[1+ l ℕ.+ k ℕ.* ℕ.suc l ]
[ -[1+ k ] * +[1+ l ] ≠0] = -[1+ l ℕ.+ k ℕ.* ℕ.suc l ]
[ -[1+ k ] * -[1+ l ] ≠0] = +[1+ l ℕ.+ k ℕ.* ℕ.suc l ]

[∣_∣≠0] : ∀ {k} → k ≠0 → + ∣ k ∣ ≠0
[∣ +[1+ k ] ∣≠0] = +[1+ k ]
[∣ -[1+ k ] ∣≠0] = +[1+ k ]

lcm≠0 : ∀ {k l} → k ≠0 → l ≠0 → + proj₁ (LCM.lcm ∣ k ∣ ∣ l ∣) ≠0
lcm≠0 {k} {l} k≠0 l≠0 = from≢0 $ λ lcm≡0 →
  let (gcd , prfgcd) = GCD.gcd ∣ k ∣ ∣ l ∣
      (lcm , prflcm) = LCM.lcm ∣ k ∣ ∣ l ∣ in
  [ to≢0 [∣ k≠0 ∣≠0] ∘ cong ℤ.pos
  , to≢0 [∣ l≠0 ∣≠0] ∘ cong ℤ.pos
  ]′
  $ NProp.i*j≡0⇒i≡0∨j≡0 ∣ k ∣ $ begin
    ∣ k ∣ ℕ.* ∣ l ∣ ≡⟨ LCM.gcd*lcm prfgcd prflcm ⟩
    gcd   ℕ.* lcm   ≡⟨ cong (gcd ℕ.*_) (ZProp.+-injective lcm≡0) ⟩
    gcd   ℕ.* 0     ≡⟨ NProp.*-zeroʳ gcd ⟩
    0               ∎

infix 3 [-_≠0]
[-_≠0] : ∀ {k} → k ≠0 → - k ≠0
[- +[1+ k ] ≠0] = -[1+ k ]
[- -[1+ k ] ≠0] = +[1+ k ]

Notnull : Set
Notnull = Σ ℤ _≠0

∣_∣≠0 : Notnull → Notnull
∣ σ , Hσ ∣≠0 = + ∣ σ ∣ , [∣ Hσ ∣≠0]

1≠0 : Notnull
1≠0 = -, +[1+ 0 ]

:0 : {n : ℕ} → exp n
:0 {n} = val {n} (+ 0)

:1 : {n : ℕ} → exp n
:1 {n} = val {n} (+ 1)

-----
-- Erasure functions
----

toExp :  ∀ (P : ∀ {n} → exp n → Set) {n e} → P {n} e → exp n
toExp _ {e = e} _ = e

toForm : ∀ (P : ∀ {n} → form n → Set) {n φ} → P {n} φ → form n
toForm _ {φ = φ} _ = φ

-----
-- To be quantifier free
-----

data QFree {n : ℕ} : form n → Set where
  T : QFree T
  F : QFree F
  _:<_ : (t₁ t₂ : exp n) → QFree (t₁ :< t₂)
  _:>_ : (t₁ t₂ : exp n) → QFree (t₁ :> t₂)
  _:≤_ : (t₁ t₂ : exp n) → QFree (t₁ :≤ t₂)
  _:≥_ : (t₁ t₂ : exp n) → QFree (t₁ :≥ t₂)
  _:≡_ : (t₁ t₂ : exp n) → QFree (t₁ :≡ t₂)
  _:|_ : (k : ℤ) (t : exp n) → QFree (k :| t)
  :¬_  : {φ : form n} → QFree φ → QFree (:¬ φ)
  _:∧_ : {φ₁ φ₂ : form n} → QFree φ₁ → QFree φ₂ → QFree (φ₁ :∧ φ₂)
  _:∨_ : {φ₁ φ₂ : form n} → QFree φ₁ → QFree φ₂ → QFree (φ₁ :∨ φ₂)
  _:→_ : {φ₁ φ₂ : form n} → QFree φ₁ → QFree φ₂ → QFree (φ₁ :→ φ₂)

-----
-- To be in negation normal form
-----

data NNF {n : ℕ} : form n → Set where
  T    : NNF (T {n})
  F    : NNF (F {n})
  _:≤_ : (t₁ t₂ : exp n) → NNF (t₁ :≤ t₂)
  _:≡_ : (t₁ t₂ : exp n) → NNF (t₁ :≡ t₂)
  _:≢_ : (t₁ t₂ : exp n) → NNF (:¬ (t₁ :≡ t₂))
  _:|_ : (k : ℤ) (t : exp n) → NNF (k :| t)
  _:|̸_ : (k : ℤ) (t : exp n) → NNF (:¬ (k :| t))
  _:∧_ : {φ₁ φ₂ : form n} → NNF φ₁ → NNF φ₂ → NNF (φ₁ :∧ φ₂)
  _:∨_ : {φ₁ φ₂ : form n} → NNF φ₁ → NNF φ₂ → NNF (φ₁ :∨ φ₂)

-----
-- To be linear
-----

infix 21 _*var_[_]+_
data Lin-E {n : ℕ} (n₀ : ℕ) : exp n → Set where
  val         : (k : ℤ) → Lin-E n₀ (val k)
  _*var_[_]+_ : {k : ℤ} → k ≠0 → (p : Fin n) {r : exp n} →
                n₀ ℕ.≤ toℕ p → Lin-E (ℕ.suc (toℕ p)) r → Lin-E n₀ ((k :* var p) :+  r)

data Lin {n : ℕ} : form n → Set where
  T    : Lin T
  F    : Lin F
  _:≤0 : ∀ {t} → Lin-E zero t → Lin (t :≤ :0)
  _:≡0 : ∀ {t} → Lin-E zero t → Lin (t :≡ :0)
  _:≢0 : ∀ {t} → Lin-E zero t → Lin (:¬ (t :≡ :0))
  _:|_ : ∀ {k t} → k ≠0 → Lin-E zero t → Lin (k :| t)
  _:|̸_ : ∀ {k t} → k ≠0 → Lin-E zero t → Lin (:¬ (k :| t))
  _:∧_ : {φ₁ φ₂ : form n} → Lin φ₁ → Lin φ₂ → Lin (φ₁ :∧ φ₂)
  _:∨_ : {φ₁ φ₂ : form n} → Lin φ₁ → Lin φ₂ → Lin (φ₁ :∨ φ₂)

-----
-- All of var0's coefficients are divisible by σ
-----

infixr 21 c*varn_+_ _[_]*var0+_
data Div-E (σ : Notnull) : {n : ℕ} → exp n → Set where
  val         : ∀ {n} k → Div-E σ {n} (val k)
  c*varn_+_   : ∀ {n} {t : exp n} (p : ℕ) → Lin-E (ℕ.suc p) t → Div-E σ t
  _[_]*var0+_ : ∀ {n} {t : exp (ℕ.suc n)} k → k ∣′ (proj₁ σ) → Lin-E 1 t →
                Div-E σ ((k :* var zero) :+ t)

data Div {n : ℕ} (σ : Notnull) : form n → Set where
  T    : Div σ T
  F    : Div σ F
  _:≤0 : ∀ {t} → Div-E σ t → Div σ (t :≤ :0)
  _:≡0 : ∀ {t} → Div-E σ t → Div σ (t :≡ :0)
  _:≢0 : ∀ {t} → Div-E σ t → Div σ (:¬ (t :≡ :0))
  _:|_ : ∀ {k t} → k ≠0 → Div-E σ t → Div σ (k :| t)
  _:|̸_ : ∀ {k t} → k ≠0 → Div-E σ t → Div σ (:¬ (k :| t))
  _:∧_ : ∀ {φ₁ φ₂} → Div σ φ₁ → Div σ φ₂ → Div σ (φ₁ :∧ φ₂)
  _:∨_ : ∀ {φ₁ φ₂} → Div σ φ₁ → Div σ φ₂ → Div σ (φ₁ :∨ φ₂)

-----
-- To be unitary
-----

pattern :+1 = ℤ.+ 1
pattern :-1 = ℤ.-[1+ 0 ]

data ∣_∣≡1 : ℤ → Set where
  ∣+1∣ : ∣ :+1 ∣≡1
  ∣-1∣ : ∣ :-1 ∣≡1

toAbs : ∀ {k} → ∣ k ∣≡1 → ∣ k ∣ ≡ 1
toAbs ∣+1∣ = refl
toAbs ∣-1∣ = refl

fromAbs : ∀ {k} → ∣ k ∣ ≡ 1 → ∣ k ∣≡1
fromAbs {+ 1}       eq = ∣+1∣
fromAbs { -[1+ 0 ]} eq = ∣-1∣
fromAbs {+ zero}             ()
fromAbs {+ ℕ.suc (ℕ.suc _) } ()
fromAbs { -[1+ ℕ.suc _ ]}    ()

infixr 21 varn_+_
data Unit-E : {n : ℕ} → exp n → Set where
  val         : ∀ {n} k → Unit-E {n} (val k)
  varn_+_     : ∀ {n} {t : exp n} (p : ℕ) → Lin-E (ℕ.suc p) t → Unit-E t
  _[_]*var0+_ : ∀ {n t} k → ∣ k ∣≡1 → Lin-E {ℕ.suc n} 1 t →
                Unit-E ((k :* (var zero)) :+ t)

data Unit {n : ℕ} : form n → Set where
  T    : Unit T
  F    : Unit F
  _:≤0 : ∀ {t} → Unit-E t → Unit (t :≤ :0)
  _:≡0 : ∀ {t} → Unit-E t → Unit (t :≡ :0)
  _:≢0 : ∀ {t} → Unit-E t → Unit (:¬ (t :≡ :0))
  _:|_ : ∀ {k t} → k ≠0 → Unit-E t → Unit (k :| t)
  _:|̸_ : ∀ {k t} → k ≠0 → Unit-E t → Unit (:¬ (k :| t))
  _:∧_ : ∀ {φ₁ φ₂} → Unit φ₁ → Unit φ₂ → Unit (φ₁ :∧ φ₂)
  _:∨_ : ∀ {φ₁ φ₂} → Unit φ₁ → Unit φ₂ → Unit (φ₁ :∨ φ₂)

-----
-- Contains var0
-----

data Has0-E : {n : ℕ} → exp n → Set where
  _*var0+_ : ∀ {n t} (k : ℤ) → Lin-E 1 t → Has0-E {ℕ.suc n} ((k :* (var zero)) :+ t)

data Has0 {n : ℕ} : form n → Set where
  _:≤0 : ∀ {t} → Has0-E t → Has0 (t :≤ :0)
  _:≡0 : ∀ {t} → Has0-E t → Has0 (t :≡ :0)
  _:≢0 : ∀ {t} → Has0-E t → Has0 (:¬ (t :≡ :0))
  _:|_ : ∀ {k t} → k ≠0 → Has0-E t → Has0 (k :| t)
  _:|̸_ : ∀ {k t} → k ≠0 → Has0-E t → Has0 (:¬ (k :| t))
  :∧-⊎ : ∀ {φ₁ φ₂} → Has0 φ₁ ⊎ Has0 φ₂ → Has0 (φ₁ :∧ φ₂)
  :∨-⊎ : ∀ {φ₁ φ₂} → Has0 φ₁ ⊎ Has0 φ₂ → Has0 (φ₁ :∨ φ₂)

-----
-- Almost free from var0
-----

data Free0-E {n : ℕ} : exp n → Set where
  val     : ∀ k → Free0-E (val k)
  varn_+_ : ∀ {t : exp n} p → Lin-E (ℕ.suc p) t → Free0-E t

data Free0 {n : ℕ} : form n → Set where
  T    : Free0 T
  F    : Free0 F
  _:≤0 : ∀ {t} → Free0-E t → Free0 (t :≤ :0)
  _:≡0 : ∀ {t} → Free0-E t → Free0 (t :≡ :0)
  _:≢0 : ∀ {t} → Free0-E t → Free0 (:¬ (t :≡ :0))
  _:|_ : ∀ {k t} → k ≠0 → Unit-E t → Free0 (k :| t)
  _:|̸_ : ∀ {k t} → k ≠0 → Unit-E t → Free0 (:¬ (k :| t))
  _:∧_ : ∀ {φ₁ φ₂} → Free0 φ₁ → Free0 φ₂ → Free0 (φ₁ :∧ φ₂)
  _:∨_ : ∀ {φ₁ φ₂} → Free0 φ₁ → Free0 φ₂ → Free0 (φ₁ :∨ φ₂)

-----
-- For all k|_, k | σ
-----

data All∣′ {n : ℕ} (σ : Notnull) : form n → Set where
  T       : All∣′ σ T
  F       : All∣′ σ F
  _:≤0    : ∀ t → All∣′ σ (t :≤ :0)
  _:≡0    : ∀ t → All∣′ σ (t :≡ :0)
  _:≢0    : ∀ t → All∣′ σ (:¬ (t :≡ :0))
  _[_]:|_ : ∀ {k} → k ∣′ (proj₁ σ) → k ≠0 → ∀ t → All∣′ σ (k :| t)
  _[_]:|̸_ : ∀ {k} → k ∣′ (proj₁ σ) → k ≠0 → ∀ t → All∣′ σ (:¬ (k :| t))
  _:∧_    : ∀ {φ₁ φ₂} → All∣′ σ φ₁ → All∣′ σ φ₂ → All∣′ σ (φ₁ :∧ φ₂)
  _:∨_    : ∀ {φ₁ φ₂} → All∣′ σ φ₁ → All∣′ σ φ₂ → All∣′ σ (φ₁ :∨ φ₂)
