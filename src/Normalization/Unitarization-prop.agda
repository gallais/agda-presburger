module Normalization.Unitarization-prop where

open import Representation
open import Semantics
open import Semantics-prop
open import Properties
open import Equivalence
open import Normalization.Linearisation
open import Normalization.Linearisation-prop
open import Normalization.Unitarization

open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Divisibility as Ndiv
import Data.Nat.Properties as NProp
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Divisibility as Zdiv
open import Data.Integer.Divisibility.Signed
import Data.Integer.Properties as ZProp
open import Data.Fin as Fin using (Fin)
open import Data.Empty
open import Data.Product as Prod
open import Data.Vec
import Data.Sign as S
import Data.Sign.Properties as SProp
open import Function hiding (_↔_; _⇔_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

⟦unit-E_⟧ : ∀ {σ n t} (e : Div-E σ {ℕ.suc n} t) → ∀ ρ {x} →
   let k = unit-k e in
   ℤ.+ k ℤ.* ⟦ t ⟧e (x ∷ ρ) ≡ ⟦ proj₁ (unit-E e) ⟧e (toℤ (proj₂ σ) ℤ.* x ∷ ρ)
⟦unit-E val k             ⟧ ρ = ZProp.*-identityˡ k
⟦unit-E_⟧ {_ , σ} (c*varn p + e) ρ {x} = begin
  let ⟦t⟧e = ⟦ toExp (Lin-E (ℕ.suc p)) e ⟧e_ in
  ℤ.pos 1 ℤ.* (⟦t⟧e (x ∷ ρ)) ≡⟨ ZProp.*-identityˡ (⟦t⟧e (x ∷ ρ)) ⟩
  ⟦t⟧e (x ∷ ρ)               ≡⟨ lin-ext₁ e x (toℤ σ ℤ.* x) ρ ⟩
  ⟦t⟧e (toℤ σ ℤ.* x ∷ ρ)     ∎ where open ≡-Reasoning
⟦unit-E_⟧ {_ , σ} (k [ k∣′σ ]*var0+ e) ρ {x} = begin
  k′ ℤ.* (k ℤ.* x ℤ.+ ⟦t⟧e ρ₁)
    ≡⟨ ZProp.*-distribˡ-+ k′ _ _ ⟩
  k′ ℤ.* (k ℤ.* x) ℤ.+ k′ ℤ.* ⟦t⟧e ρ₁
    ≡⟨ cong₂ ℤ._+_ (sym (ZProp.*-assoc k′ k x)) (cong (k′ ℤ.*_) (lin-ext₁ e x _ ρ)) ⟩
  (k′ ℤ.* k) ℤ.* x ℤ.+ k′ ℤ.* ⟦t⟧e ρ₂
    ≡⟨ cong (λ z → z ℤ.* x ℤ.+  (k′ ℤ.* ⟦t⟧e ρ₂)) eq ⟩
  ((s ℤ.◃ 1) ℤ.* toℤ σ) ℤ.* x ℤ.+ k′ ℤ.* ⟦t⟧e ρ₂
    ≡⟨ cong₂ ℤ._+_ (ZProp.*-assoc (s ℤ.◃ 1) (toℤ σ) x) (k′ ⟦*E e ⟧ ρ₂) ⟩
  (s ℤ.◃ 1) ℤ.* (toℤ σ ℤ.* x) ℤ.+ ⟦ (k′ *E e) .proj₁ ⟧e ρ₂
    ∎ where

    open ≡-Reasoning

    -- evaluations
    ⟦t⟧e = ⟦ toExp (Lin-E 1) e ⟧e_
    ρ₁   = x ∷ ρ
    ρ₂   = toℤ σ ℤ.* x ∷ ρ

    -- coefficient
    k∣σ = ∣⇒∣ᵤ k∣′σ
    k′  = ℤ.+ Ndiv.quotient k∣σ
    s   = ℤ.sign k S.* ℤ.sign (toℤ σ)

    ∣eq∣ : ℤ.∣ k′ ℤ.* k ∣ ≡ ℤ.∣ (s ℤ.◃ 1) ℤ.* toℤ σ ∣
    ∣eq∣ = begin
      ℤ.∣ k′ ℤ.* k ∣                ≡⟨ ZProp.abs-*-commute k′ k ⟩
      ℤ.∣ k′ ∣ ℕ.* ℤ.∣ k ∣          ≡⟨ sym (Ndiv._∣_.equality k∣σ) ⟩
      ℤ.∣ toℤ σ ∣                   ≡⟨ sym (NProp.*-identityˡ _) ⟩
      1 ℕ.* ℤ.∣ toℤ σ ∣             ≡⟨ cong (ℕ._* _) (sym (ZProp.abs-◃ s 1)) ⟩
      ℤ.∣ s ℤ.◃ 1 ∣ ℕ.* ℤ.∣ toℤ σ ∣ ≡⟨ sym (ZProp.abs-*-commute (s ℤ.◃ 1) (toℤ σ)) ⟩
      ℤ.∣ (s ℤ.◃ 1) ℤ.* toℤ σ ∣     ∎ where open ≡-Reasoning

    sign-eq : ℤ.sign (k′ ℤ.* k) ≡ ℤ.sign ((s ℤ.◃ 1) ℤ.* toℤ σ)
    sign-eq with Ndiv.quotient k∣σ | Ndiv._∣_.equality k∣σ
    ... | ℕ.zero  | eq = ⊥-elim (to≢0 σ (ZProp.∣n∣≡0⇒n≡0 eq))
    ... | ℕ.suc q | eq with ℤ.∣ k ∣
    ... | ℕ.zero    = ⊥-elim (to≢0 σ (ZProp.∣n∣≡0⇒n≡0 (trans eq (NProp.*-zeroʳ q))))
    ... | ℕ.suc ∣k∣ rewrite eq = begin
      ℤ.sign (ℤ.sign k ℤ.◃ abs)
        ≡⟨ ZProp.sign-◃ _ _ ⟩
      ℤ.sign k
        ≡⟨ sym (SProp.*-identityʳ (ℤ.sign k)) ⟩
      ℤ.sign k S.* S.+
        ≡⟨ cong (ℤ.sign k S.*_) (sym (SProp.s*s≡+ (ℤ.sign (toℤ σ)))) ⟩
      ℤ.sign k S.* (ℤ.sign (toℤ σ) S.* ℤ.sign (toℤ σ))
        ≡⟨ sym (SProp.*-assoc (ℤ.sign k) _ _) ⟩
      s S.* ℤ.sign (toℤ σ)
        ≡⟨ cong (S._* ℤ.sign (toℤ σ)) (sym (ZProp.sign-◃ s 0)) ⟩
      sgn
        ≡⟨ sym (ZProp.sign-◃ _ _) ⟩
      ℤ.sign (sgn ℤ.◃ abs)
        ≡⟨ cong (λ m → ℤ.sign (sgn ℤ.◃ m)) (sym (NProp.*-identityˡ abs)) ⟩
      ℤ.sign (sgn ℤ.◃ 1 ℕ.* abs)
        ≡⟨ cong (λ m → ℤ.sign (sgn ℤ.◃ m ℕ.* abs)) (sym (ZProp.abs-◃ s 1)) ⟩
      ℤ.sign (sgn ℤ.◃ ℤ.∣ s ℤ.◃ 1 ∣ ℕ.* abs) ∎
      where
        open ≡-Reasoning
        sgn = ℤ.sign (s ℤ.◃ 1) S.* ℤ.sign (toℤ σ)
        abs = ℕ.suc q ℕ.* ℕ.suc ∣k∣
    eq : k′ ℤ.* k ≡ (s ℤ.◃ 1) ℤ.* toℤ σ
    eq = ZProp.◃-≡ sign-eq ∣eq∣

open import Relation.Binary.Reasoning.MultiSetoid

⟦unit_⟧ : ∀ {σ n φ} (p : Div {ℕ.suc n} σ φ) → ∀ ρ {x} →
          ⟦ φ ⟧ (x ∷ ρ) ↔ ⟦ proj₁ (unit p) ⟧ (toℤ (proj₂ σ) ℤ.* x ∷ ρ)
⟦unit T      ⟧ ρ = ↔-refl
⟦unit F      ⟧ ρ = ↔-refl
⟦unit_⟧ {σ} (e :≤0) ρ {x} = begin⟨ ↔-setoid ⟩
  let k = ℤ.+ (unit-k e); k' = ℤ.+ (ℕ.suc (ℕ.pred (unit-k e)))
      t = toExp (Div-E σ) e in
  ⟦ t :≤ :0 ⟧ (x ∷ ρ)
    ≈⟨ ZProp.*-monoˡ-≤-pos (ℕ.pred (unit-k e))
     , ZProp.*-cancelˡ-≤-pos (ℕ.pred (unit-k e)) _ _ ⟩
  k' ℤ.* ⟦ t ⟧e (x ∷ ρ) ℤ.≤ k' ℤ.* ℤ.+ 0
    ≡⟨ cong (λ k → ℤ.+ k ℤ.* ⟦ t ⟧e (x ∷ ρ) ℤ.≤ k' ℤ.* ℤ.+ 0) (sym (unit-k-pos e)) ⟩
  k ℤ.* ⟦ t ⟧e (x ∷ ρ) ℤ.≤ k' ℤ.* ℤ.+ 0
    ≡⟨ cong₂ (ℤ._≤_) (⟦unit-E e ⟧ ρ) (ZProp.*-zeroʳ k') ⟩
  ⟦ proj₁ (unit (e :≤0)) ⟧ _ ∎
⟦unit_⟧ {σ} (e :≡0) ρ {x} = begin⟨ ↔-setoid ⟩
  let k = ℤ.+ (unit-k e); k' = ℤ.+ (ℕ.suc (ℕ.pred (unit-k e)))
      t = toExp (Div-E σ) e in
  ⟦ t :≡ :0 ⟧ (x ∷ ρ)
    ≈⟨ cong (k' ℤ.*_) , ZProp.*-cancelˡ-≡ k' _ _ (λ ()) ⟩
  k' ℤ.* (⟦ t ⟧e (x ∷ ρ)) ≡ k' ℤ.* ℤ.+ 0
    ≡⟨ cong (λ k → ℤ.+ k ℤ.* (⟦ t ⟧e (x ∷ ρ)) ≡ k' ℤ.* ℤ.+ 0) (sym (unit-k-pos e)) ⟩
  k ℤ.* (⟦ t ⟧e (x ∷ ρ)) ≡ k' ℤ.* ℤ.pos 0
    ≡⟨ cong₂ _≡_ (⟦unit-E e ⟧ ρ) (ZProp.*-zeroʳ k') ⟩
  ⟦ proj₁ (unit (e :≡0)) ⟧ _ ∎
⟦unit_⟧ {σ} (e :≢0) ρ {x} = begin⟨ ↔-setoid ⟩
  let k = ℤ.+ (unit-k e); k' = ℤ.+ (ℕ.suc (ℕ.pred (unit-k e)))
      t = toExp (Div-E σ) e in
  ⟦ :¬ (t :≡ :0) ⟧ (x ∷ ρ)
    ≈⟨ ↔¬ (cong (k' ℤ.*_) , ZProp.*-cancelˡ-≡ k' _ _ (λ ())) ⟩
  k' ℤ.* (⟦ t ⟧e (x ∷ ρ)) ≢ k' ℤ.* ℤ.+ 0
    ≡⟨ cong (λ k → ℤ.+ k ℤ.* (⟦ t ⟧e (x ∷ ρ)) ≢ k' ℤ.* ℤ.+ 0) (sym (unit-k-pos e)) ⟩
  k ℤ.* (⟦ t ⟧e (x ∷ ρ)) ≢ k' ℤ.* ℤ.pos 0
    ≡⟨ cong₂ _≢_ (⟦unit-E e ⟧ ρ) (ZProp.*-zeroʳ k') ⟩
  ⟦ proj₁ (unit (e :≢0)) ⟧ _ ∎
⟦unit_⟧ {σ} (k≠0 :| e) ρ {x} = begin⟨ ↔-setoid ⟩
  let k = toℤ k≠0; t = toExp (Div-E σ) e; k' = unit-k e; k'k = ℤ.+ k' ℤ.* k in
  k ∣ (⟦ t ⟧e (x ∷ ρ))
    ≈⟨ *-monoʳ-∣ (ℤ.+ k')
     , *-cancelˡ-∣ (ℤ.+ k') (to≢0 (unit-k≠0 e)) ⟩
  k'k ∣ ℤ.pos k' ℤ.* (⟦ t ⟧e (x ∷ ρ))
    ≡⟨ cong (k'k ∣_) (⟦unit-E e ⟧ ρ) ⟩
  ⟦ proj₁ (unit (k≠0 :| e)) ⟧ (toℤ (proj₂ σ) ℤ.* x ∷ ρ) ∎
⟦unit_⟧ {σ} (k≠0 :|̸ e) ρ {x} = begin⟨ ↔-setoid ⟩
  let k = toℤ k≠0; t = toExp (Div-E σ) e; k' = unit-k e; k'k = ℤ.+ k' ℤ.* k in
  ¬ (k ∣ (⟦ t ⟧e (x ∷ ρ)))
    ≈⟨ ↔¬ (*-monoʳ-∣ (ℤ.+ k')
          , *-cancelˡ-∣ (ℤ.+ k') (to≢0 (unit-k≠0 e))) ⟩
  ¬ (k'k ∣ ℤ.pos k' ℤ.* (⟦ t ⟧e (x ∷ ρ)))
    ≡⟨ cong (λ p → ¬ k'k ∣ p) (⟦unit-E e ⟧ ρ) ⟩
  (¬ ⟦ proj₁ (unit (k≠0 :| e)) ⟧ (toℤ (proj₂ σ) ℤ.* x ∷ ρ)) ∎
⟦unit p :∧ q ⟧ ρ = ⟦unit p ⟧ ρ ↔× ⟦unit q ⟧ ρ
⟦unit p :∨ q ⟧ ρ = ⟦unit p ⟧ ρ ↔⊎ ⟦unit q ⟧ ρ
