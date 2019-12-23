module Minusinf where

open import Data.Nat as ℕ using (ℕ)

open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ZProp
import Data.Integer.DivMod as ZDM

open import Data.Empty
open import Data.Product as Prod
open import Data.Vec as Vec
open import Function hiding (Equivalence; _↔_; _⇔_)

open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

open import Representation
open import Properties
open import Semantics
open import Semantics-prop
open import Equivalence
open import Comparisons
open import AllmostFree-prop

pattern :-1 = ℤ.-[1+ 0 ]
pattern :+0 = ℤ.+ 0
pattern :+1 = ℤ.+ 1


-- Equivalent formula if we're willing to let var0 go to -∞

var0⟶-∞ : ∀ {n φ} → Unit {n} φ → ∃ (Free0 {n})
var0⟶-∞ T        = -, T
var0⟶-∞ F        = -, F
-- :≤0
var0⟶-∞ (:-1 [ ∣-1∣ ]*var0+ e :≤0) = -, F
var0⟶-∞ (:+1 [ ∣+1∣ ]*var0+ e :≤0) = -, T
var0⟶-∞ (val k                :≤0) = -, val k :≤0
var0⟶-∞ (varn p + e           :≤0) = -, varn p + e :≤0
-- :≡0
var0⟶-∞ (k [ prf ]*var0+ e :≡0) = -, F
var0⟶-∞ (val k             :≡0) = -, val k :≡0
var0⟶-∞ (varn p + e        :≡0) = -, varn p + e :≡0
-- :≢0
var0⟶-∞ (k [ prf ]*var0+ e :≢0) = -, T
var0⟶-∞ (val k             :≢0) = -, val k :≢0
var0⟶-∞ (varn p + e        :≢0) = -, varn p + e :≢0
-- k :∣
var0⟶-∞ (k :| e) = -, k :| e
var0⟶-∞ (k :|̸ e) = -, k :|̸ e
var0⟶-∞ (φ :∧ ψ) = -, proj₂ (var0⟶-∞ φ) :∧ proj₂ (var0⟶-∞ ψ)
var0⟶-∞ (φ :∨ ψ) = -, proj₂ (var0⟶-∞ φ) :∨ proj₂ (var0⟶-∞ ψ)

bound : ∀ {n φ} → Unit {ℕ.suc n} φ → Vec ℤ n → ℤ
bound (:+1 [ ∣+1∣ ]*var0+ e :≤0) ρ = ℤ.- ⟦ toExp (Lin-E 1) e ⟧e (:+0 ∷ ρ)
bound (:-1 [ ∣-1∣ ]*var0+ e :≤0) ρ = :-1 ℤ.+ ⟦ toExp (Lin-E 1) e ⟧e (:+0 ∷ ρ)
bound (:+1 [ ∣+1∣ ]*var0+ e :≡0) ρ = :-1 ℤ.- ⟦ toExp (Lin-E 1) e ⟧e (:+0 ∷ ρ)
bound (:-1 [ ∣-1∣ ]*var0+ e :≡0) ρ = :-1 ℤ.+ ⟦ toExp (Lin-E 1) e ⟧e (:+0 ∷ ρ)
bound (:+1 [ ∣+1∣ ]*var0+ e :≢0) ρ = :-1 ℤ.- ⟦ toExp (Lin-E 1) e ⟧e (:+0 ∷ ρ)
bound (:-1 [ ∣-1∣ ]*var0+ e :≢0) ρ = :-1 ℤ.+ ⟦ toExp (Lin-E 1) e ⟧e (:+0 ∷ ρ)
bound (φ :∧ ψ) ρ = bound φ ρ ℤ.⊓ bound ψ ρ
bound (φ :∨ ψ) ρ = bound φ ρ ℤ.⊓ bound ψ ρ
bound _ _ = ℤ.+ 0

cooper-aux : ∀ x t → x ℤ.≤ ℤ.pred t → :+0 ℤ.< ℤ.- x ℤ.+ t
cooper-aux x t x≤pt = begin
  :+1                   ≡⟨ sym (ZProp.+-identityʳ :+1) ⟩
  :+1 ℤ.+ :+0           ≡⟨ cong (ℤ._+_ :+1) (sym (ZProp.+-inverseˡ x)) ⟩
  :+1 ℤ.+ (ℤ.- x ℤ.+ x) ≡⟨ ZProp.+-comm :+1 (ℤ.- x ℤ.+ x) ⟩
  ℤ.- x ℤ.+ x ℤ.+ :+1   ≡⟨ ZProp.+-assoc (ℤ.- x) x :+1 ⟩
  ℤ.- x ℤ.+ (x ℤ.+ :+1) ≡⟨ cong (ℤ._+_ (ℤ.- x)) (ZProp.+-comm x (ℤ.+ 1)) ⟩
  ℤ.- x ℤ.+ (:+1 ℤ.+ x) ≤⟨ ZProp.+-monoʳ-≤ (ℤ.- x) (ZProp.m≤pred[n]⇒m<n x≤pt) ⟩
  ℤ.- x ℤ.+ t           ∎ where open ZProp.≤-Reasoning


cooper-bound : ∀ {n f} (φ : Unit f) x ρ → x ℤ.≤ bound {n} φ ρ →
         ⟦ f ⟧ (x ∷ ρ) ↔ ⟦ proj₁ (var0⟶-∞ φ) ⟧ (x ∷ ρ)
cooper-bound T x ρ x≤lb = ↔-refl
cooper-bound F x ρ x≤lb = ↔-refl
-- :≤0
cooper-bound (:+1 [ ∣+1∣ ]*var0+ e :≤0) x ρ x≤lb = -,_ $ const $ begin
  let t = toExp (Lin-E 1) e; ⟦t⟧ = λ x → ⟦ t ⟧e (x ∷ ρ) in
  :+1 ℤ.* x ℤ.+ ⟦t⟧ x         ≡⟨ cong₂ ℤ._+_ (ZProp.*-identityˡ x) (lin-ext₁ e x :+0 ρ) ⟩
  x ℤ.+ ⟦t⟧ :+0               ≤⟨ ZProp.+-monoˡ-≤ (⟦ t ⟧e (:+0 ∷ ρ)) x≤lb ⟩
  ℤ.- (⟦t⟧ :+0) ℤ.+ (⟦t⟧ :+0) ≡⟨ ZProp.+-inverseˡ (⟦t⟧ :+0) ⟩
  :+0 ∎ where open ZProp.≤-Reasoning
cooper-bound (:-1 [ ∣-1∣ ]*var0+ e :≤0) x ρ x≤lb = flip _,_ ⊥-elim $ ZProp.>⇒≰ $ begin
  let ⟦t⟧ = λ x → ⟦ toExp (Lin-E 1) e ⟧e (x ∷ ρ) in
  ℤ.+ 1               ≤⟨ cooper-aux x (⟦t⟧ :+0) x≤lb ⟩
  ℤ.- x ℤ.+ ⟦t⟧ :+0   ≡⟨ cong₂ ℤ._+_ (sym (ZProp.-1*n≡-n x)) (lin-ext₁ e :+0 x ρ) ⟩
  :-1 ℤ.* x ℤ.+ ⟦t⟧ x ∎ where open ZProp.≤-Reasoning
cooper-bound (val k                :≤0) x ρ x≤lb = ↔-refl
cooper-bound (varn p + e           :≤0) x ρ x≤lb = ↔-refl
-- :≡0
cooper-bound (:+1 [ ∣+1∣ ]*var0+ e :≡0) x ρ x≤lb = flip _,_ ⊥-elim $ flip ZProp.<-irrefl $ begin
  let ⟦t⟧ = λ x → ⟦ toExp (Lin-E 1) e ⟧e (x ∷ ρ) in
  ℤ.suc (:+1 ℤ.* x ℤ.+ ⟦t⟧ x)
    ≡⟨ cong ℤ.suc $ cong₂ ℤ._+_ (ZProp.*-identityˡ x) (lin-ext₁ e x :+0 ρ) ⟩
  ℤ.suc (x ℤ.+ ⟦t⟧ :+0)
    ≤⟨ ZProp.+-monoˡ-< (⟦t⟧ :+0) {x} {ℤ.- ⟦t⟧ :+0} (ZProp.m≤pred[n]⇒m<n x≤lb) ⟩
  ℤ.- ⟦t⟧ :+0 ℤ.+ ⟦t⟧ :+0
    ≡⟨ ZProp.+-inverseˡ (⟦t⟧ :+0) ⟩
  :+0
    ∎ where open ZProp.≤-Reasoning
cooper-bound (:-1 [ ∣-1∣ ]*var0+ e :≡0) x ρ x≤lb = flip _,_ ⊥-elim $ flip ZProp.>-irrefl $ begin
  let ⟦t⟧ = λ x → ⟦ toExp (Lin-E 1) e ⟧e (x ∷ ρ) in
  ℤ.+ 1               ≤⟨ cooper-aux x (⟦t⟧ :+0) x≤lb ⟩
  ℤ.- x ℤ.+ ⟦t⟧ :+0   ≡⟨ cong₂ ℤ._+_ (sym (ZProp.-1*n≡-n x)) (lin-ext₁ e :+0 x ρ) ⟩
  :-1 ℤ.* x ℤ.+ ⟦t⟧ x ∎ where open ZProp.≤-Reasoning
cooper-bound (val k                :≡0) x ρ x≤lb = ↔-refl
cooper-bound (varn p + e           :≡0) x ρ x≤lb = ↔-refl
-- :≢0
cooper-bound (:+1 [ ∣+1∣ ]*var0+ e :≢0) x ρ x≤lb = -,_ $ const $ flip ZProp.<-irrefl $ begin
  let ⟦t⟧ = λ x → ⟦ toExp (Lin-E 1) e ⟧e (x ∷ ρ) in
  ℤ.suc (:+1 ℤ.* x ℤ.+ ⟦t⟧ x)
    ≡⟨ cong ℤ.suc $ cong₂ ℤ._+_ (ZProp.*-identityˡ x) (lin-ext₁ e x :+0 ρ) ⟩
  ℤ.suc (x ℤ.+ ⟦t⟧ :+0)
    ≤⟨ ZProp.+-monoˡ-< (⟦t⟧ :+0) {x} {ℤ.- ⟦t⟧ :+0} (ZProp.m≤pred[n]⇒m<n x≤lb) ⟩
  ℤ.- ⟦t⟧ :+0 ℤ.+ ⟦t⟧ :+0
    ≡⟨ ZProp.+-inverseˡ (⟦t⟧ :+0) ⟩
  :+0
    ∎ where open ZProp.≤-Reasoning
cooper-bound (:-1 [ ∣-1∣ ]*var0+ e :≢0) x ρ x≤lb = -,_ $ const $ flip ZProp.>-irrefl $ begin
  let ⟦t⟧ = λ x → ⟦ toExp (Lin-E 1) e ⟧e (x ∷ ρ) in
  ℤ.+ 1               ≤⟨ cooper-aux x (⟦t⟧ :+0) x≤lb ⟩
  ℤ.- x ℤ.+ ⟦t⟧ :+0   ≡⟨ cong₂ ℤ._+_ (sym (ZProp.-1*n≡-n x)) (lin-ext₁ e :+0 x ρ) ⟩
  :-1 ℤ.* x ℤ.+ ⟦t⟧ x ∎ where open ZProp.≤-Reasoning
cooper-bound (val k                :≢0) x ρ x≤lb = ↔-refl
cooper-bound (varn p + e           :≢0) x ρ x≤lb = ↔-refl
-- rest
cooper-bound (k :| e) x ρ x≤lb = ↔-refl
cooper-bound (k :|̸ e) x ρ x≤lb = ↔-refl
cooper-bound (φ :∧ ψ) x ρ x≤lb = cooper-bound φ x ρ (ZProp.≤-trans x≤lb (ZProp.m⊓n≤m _ _))
                              ↔× cooper-bound ψ x ρ (ZProp.≤-trans x≤lb (ZProp.m⊓n≤n _ _))
cooper-bound (φ :∨ ψ) x ρ x≤lb = cooper-bound φ x ρ (ZProp.≤-trans x≤lb (ZProp.m⊓n≤m _ _))
                      ↔⊎ cooper-bound ψ x ρ (ZProp.≤-trans x≤lb (ZProp.m⊓n≤n _ _))


⟦var0⟶-∞_⟧ : ∀ {n f} (φ : Unit {ℕ.suc n} f) {x} ρ →
             ⟦ proj₁ (var0⟶-∞ φ) ⟧ (x ∷ ρ) → ⟦ :∃ f ⟧ ρ
⟦var0⟶-∞ φ ⟧ {x} ρ prf with ℤcompare x (bound φ ρ)
... | less    x<lb = -, proj₂ (cooper-bound φ x ρ (ZProp.<⇒≤ x<lb)) prf
... | equal   x≡lb = -, proj₂ (cooper-bound φ x ρ (ZProp.≤-reflexive x≡lb)) prf
... | greater x>lb = -, proj₂ (cooper-bound φ x′ ρ x′≤lb) (proj₁ prf′ prf) where

   lb    = bound φ ρ
   ψ     = proj₂ (var0⟶-∞ φ)
   Σσ≠0  = proj₁ (lcm-:∣ ψ)
   σ     = proj₁ Σσ≠0
   σ≠0   = proj₂ Σσ≠0
   σ|ψ   = proj₂ (lcm-:∣ ψ)
   ∣σ∣≠0 = to≢0 σ≠0 ∘′ ZProp.∣n∣≡0⇒n≡0
   q     = ((bound φ ρ ℤ.- x) ZDM.div σ) {fromWitnessFalse ∣σ∣≠0}
   x′    = q ℤ.* σ ℤ.+ x
   qσ≤   : (lb ℤ.- x) ZDM.div σ ℤ.* σ ℤ.≤ lb ℤ.- x
   qσ≤   = ZDM.[n/d]*d≤n (lb ℤ.- x) σ
   x′≤lb : x′ ℤ.≤ lb
   x′≤lb = begin
     q ℤ.* σ ℤ.+ x        ≤⟨ ZProp.+-monoˡ-≤ x qσ≤ ⟩
     lb ℤ.- x ℤ.+ x       ≡⟨ ZProp.+-assoc lb (ℤ.- x) x ⟩
     lb ℤ.+ (ℤ.- x ℤ.+ x) ≡⟨ cong (ℤ._+_ lb) (ZProp.+-inverseˡ x) ⟩
     lb ℤ.+ ℤ.+ 0         ≡⟨ ZProp.+-identityʳ lb ⟩
     lb                   ∎ where open ZProp.≤-Reasoning
   prf′  = ⟦ ψ mod σ|ψ ⟧ q x ρ
