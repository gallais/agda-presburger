module Normalization.Linearisation-prop where

-- Things specific to the solver
open import Representation
open import Properties
open import Normalization.Linearisation
open import Semantics
open import Semantics-prop
open import Equivalence

-- Comparisons functions
open import Comparisons

-- About ≡ and Dec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Datatypes
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as NProp

open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ZProp
open import Data.Integer.Divisibility.Signed

open import Data.Fin as Fin using (Fin)

open import Data.Product as Prod
open import Data.Sum
open import Data.Empty
open import Data.Vec using (lookup)

open import Function hiding (_↔_; _⇔_)

open import Relation.Nullary
open import Relation.Binary

⟦-E_⟧ : ∀ {n n₀ t} (e : Lin-E {n} n₀ t) → :- t ⇔e proj₁ (-E e)
⟦-E val k               ⟧ ρ = refl
⟦-E k *var p [ prf ]+ e ⟧ ρ = begin
  let kp = toℤ k :* var p; t = toExp (Lin-E (ℕ.suc (Fin.toℕ p))) e in
  (⟦ :- kp :+ t ⟧e ρ)
    ≡⟨ ZProp.neg-distrib-+ (⟦ kp ⟧e ρ) (⟦ t ⟧e ρ) ⟩
  ℤ.- (⟦ kp ⟧e ρ) ℤ.+ ℤ.- (⟦ t ⟧e ρ)
    ≡⟨ cong₂ ℤ._+_ (ZProp.neg-distribˡ-* (toℤ k) (⟦ var p ⟧e ρ)) (⟦-E e ⟧ ρ) ⟩
  ℤ.- toℤ k ℤ.* ⟦ var p ⟧e ρ ℤ.+ (⟦ proj₁ (-E e) ⟧e ρ)
    ∎

⟦val_*var_[_]+E_⟧ : ∀ {n n₀ t} (k : ℤ) (p : Fin n) (prf : n₀ ℕ.≤ Fin.toℕ p) (e : Lin-E _ t) →
                    (k :* var p :+ t) ⇔e proj₁ (val k *var p [ prf ]+E e)
⟦val k *var p [ prf ]+E e ⟧ ρ with k ≠0?
... | inj₁ refl = ZProp.+-identityˡ _
... | inj₂ k≠0  = refl

⟦_⟧+E⟦_⟧ : ∀ {n n₀ t u} (e : Lin-E {n} n₀ t) (f : Lin-E {n} n₀ u) → t :+ u ⇔e proj₁ (e +E f)
⟦ val k               ⟧+E⟦ val l                ⟧ ρ = refl
⟦ val k               ⟧+E⟦ l *var q [ prf' ]+ f ⟧ ρ = begin
  let lq = ⟦ toℤ l :* var q ⟧e ρ; u = ⟦ toExp (Lin-E (ℕ.suc (Fin.toℕ q))) f ⟧e ρ in
  k ℤ.+ (lq ℤ.+ u) ≡⟨ sym (ZProp.+-assoc k lq u) ⟩
  k ℤ.+ lq ℤ.+ u   ≡⟨ cong (ℤ._+ u) (ZProp.+-comm k lq) ⟩
  lq ℤ.+ k ℤ.+ u   ≡⟨ ZProp.+-assoc lq _ _ ⟩
  lq ℤ.+ (k ℤ.+ u) ≡⟨ cong (ℤ._+_ lq) (⟦ val k ⟧+E⟦ f ⟧ ρ) ⟩
  _ ∎
⟦ k *var p [ prf ]+ e ⟧+E⟦ val l                ⟧ ρ = begin
  let kp = ⟦ toℤ k :* var p ⟧e ρ; t = ⟦ toExp (Lin-E (ℕ.suc (Fin.toℕ p))) e ⟧e ρ in
  kp ℤ.+ t ℤ.+ l   ≡⟨ ZProp.+-assoc kp _ _ ⟩
  kp ℤ.+ (t ℤ.+ l) ≡⟨ cong (ℤ._+_ kp) (⟦ e ⟧+E⟦ val l ⟧ ρ) ⟩
  _ ∎
⟦ k *var p [ prf ]+ e ⟧+E⟦ l *var q [ prf' ]+ f ⟧ ρ with Fcompare p q
... | less p<q = begin
  let kp = ⟦ toℤ k :* var p ⟧e ρ; t = ⟦ toExp (Lin-E (ℕ.suc (Fin.toℕ p))) e ⟧e ρ
      lqf = ⟦ toℤ l :* var q :+ toExp (Lin-E (ℕ.suc (Fin.toℕ q))) f ⟧e ρ in
  (kp ℤ.+ t) ℤ.+ lqf ≡⟨ ZProp.+-assoc kp _ _ ⟩
  kp ℤ.+ (t ℤ.+ lqf) ≡⟨ cong (ℤ._+_ kp) (⟦ e ⟧+E⟦ _ ⟧ ρ) ⟩
  _ ∎
... | greater p>q = begin
  let kpe = ⟦ toℤ k :* var p :+ toExp (Lin-E (ℕ.suc (Fin.toℕ p))) e ⟧e ρ
      lq  = ⟦ toℤ l :* var q ⟧e ρ; u = ⟦ toExp (Lin-E (ℕ.suc (Fin.toℕ q))) f ⟧e ρ in
      kpe ℤ.+ (lq ℤ.+ u) ≡⟨ cong (ℤ._+_ kpe) (ZProp.+-comm lq u) ⟩
      kpe ℤ.+ (u ℤ.+ lq) ≡⟨ sym (ZProp.+-assoc kpe _ _) ⟩
      kpe ℤ.+ u ℤ.+ lq  ≡⟨ ZProp.+-comm (kpe ℤ.+ u) lq ⟩
      lq ℤ.+ (kpe ℤ.+ u) ≡⟨ cong (ℤ._+_ lq) (⟦ k *var p [ _ ]+ e ⟧+E⟦ f ⟧ ρ) ⟩
      _ ∎
... | equal refl = begin
  let kp = ⟦ toℤ k :* var p ⟧e ρ; t = ⟦ toExp (Lin-E (ℕ.suc (Fin.toℕ p))) e ⟧e ρ
      lq = ⟦ toℤ l :* var q ⟧e ρ; u = ⟦ toExp (Lin-E (ℕ.suc (Fin.toℕ q))) f ⟧e ρ
      klq = ⟦ (toℤ k ℤ.+ toℤ l) :* var q ⟧e ρ
      klq-eq = sym (ZProp.*-distribʳ-+ (lookup ρ q) (toℤ k) (toℤ l))
      (t+u , e+f) = e +E f in
  (kp ℤ.+ t) ℤ.+ (lq ℤ.+ u) ≡⟨ sym (ZProp.+-assoc (kp ℤ.+ t) lq u) ⟩
  kp ℤ.+ t ℤ.+ lq ℤ.+ u     ≡⟨ cong (ℤ._+ u) (ZProp.+-assoc kp t lq) ⟩
  kp ℤ.+ (t ℤ.+ lq) ℤ.+ u   ≡⟨ cong (λ p → kp ℤ.+ p ℤ.+ u) (ZProp.+-comm t lq) ⟩
  kp ℤ.+ (lq ℤ.+ t) ℤ.+ u   ≡⟨ cong (ℤ._+ u) (sym (ZProp.+-assoc kp lq t)) ⟩
  (kp ℤ.+ lq) ℤ.+ t ℤ.+ u   ≡⟨ ZProp.+-assoc (kp ℤ.+ lq) t u ⟩
  (kp ℤ.+ lq) ℤ.+ (t ℤ.+ u) ≡⟨ cong₂ ℤ._+_ klq-eq (⟦ e ⟧+E⟦ f ⟧ ρ) ⟩
  klq ℤ.+ ⟦ t+u ⟧e ρ        ≡⟨ ⟦val (toℤ k ℤ.+ toℤ l) *var q [ prf ]+E e+f ⟧ ρ ⟩
  ⟦ proj₁ (val (toℤ k ℤ.+ toℤ l) *var q [ prf ]+E e+f) ⟧e ρ ∎


_≠0⟦*E_⟧_ : ∀ {n n₀ t k} (k≠0 : k ≠0) (e :  Lin-E {n} n₀ t) →
           (k :* t) ⇔e proj₁ (k≠0 ≠0*E e)
k ≠0⟦*E val l               ⟧ ρ = refl
k ≠0⟦*E l *var q [ prf ]+ f ⟧ ρ = begin
  let lq = ⟦ toℤ l :* var q ⟧e ρ; u = ⟦ toExp (Lin-E (ℕ.suc (Fin.toℕ q))) f ⟧e ρ
      klq-eq = sym (ZProp.*-assoc (toℤ k) (toℤ l) (lookup ρ q)) in
  toℤ k ℤ.* (lq ℤ.+ u)         ≡⟨ ZProp.*-distribˡ-+ (toℤ k) lq u ⟩
  toℤ k ℤ.* lq ℤ.+ toℤ k ℤ.* u ≡⟨ cong₂ ℤ._+_ klq-eq (k ≠0⟦*E f ⟧ ρ) ⟩
  _ ∎

_⟦*E_⟧_ : ∀ {n n₀ t} k (e :  Lin-E {n} n₀ t) → (k :* t) ⇔e proj₁ (k *E e)
k ⟦*E e ⟧ ρ with k ≠0?
... | inj₁ refl = refl
... | inj₂ k≠0  = k≠0 ≠0⟦*E e ⟧ ρ

⟦lin-E_⟧ : ∀ {n} (e : exp n) → e ⇔e proj₁ (lin-E e)
⟦lin-E val k  ⟧ ρ = refl
⟦lin-E var p  ⟧ ρ = begin
  lookup ρ p                     ≡⟨ sym (ZProp.*-identityˡ (lookup ρ p)) ⟩
  ℤ.+ 1 ℤ.* lookup ρ p           ≡⟨ sym (ZProp.+-identityʳ (ℤ.+ 1 ℤ.* lookup ρ p)) ⟩
  ℤ.+ 1 ℤ.* lookup ρ p ℤ.+ ℤ.+ 0 ∎
⟦lin-E :- e   ⟧ ρ = begin
  let (t' , e') = lin-E e in
  ⟦ :- e  ⟧e ρ                ≡⟨ cong ℤ.-_ (⟦lin-E e ⟧ ρ) ⟩
  ⟦ :- t' ⟧e ρ                ≡⟨ ⟦-E e' ⟧ ρ ⟩
  ⟦ proj₁ (lin-E (:- e)) ⟧e ρ ∎
⟦lin-E e :+ f ⟧ ρ = begin
  let (t' , e') = lin-E e; (u' , f') = lin-E f in
  ⟦ e :+ f ⟧e ρ                 ≡⟨ cong₂ ℤ._+_ (⟦lin-E e ⟧ ρ) (⟦lin-E f ⟧ ρ) ⟩
  ⟦ t' ⟧e ρ ℤ.+ ⟦ u' ⟧e ρ       ≡⟨ ⟦ e' ⟧+E⟦ f' ⟧ ρ ⟩
  ⟦ proj₁ (lin-E (e :+ f)) ⟧e ρ ∎
⟦lin-E e :- f ⟧ ρ = begin
  let (t' , e') = lin-E e; (u' , f') = lin-E f; (-u' , -f') = -E f' in
  ⟦ e :- f ⟧e ρ                 ≡⟨ cong₂ ℤ._-_ (⟦lin-E e ⟧ ρ) (⟦lin-E f ⟧ ρ) ⟩
  ⟦ t' ⟧e ρ ℤ.+ ℤ.- ⟦ u' ⟧e ρ   ≡⟨ cong (ℤ._+_ (⟦ t' ⟧e ρ)) (⟦-E f' ⟧ ρ) ⟩
  ⟦ t' ⟧e ρ ℤ.+ ⟦ -u' ⟧e ρ      ≡⟨ ⟦ e' ⟧+E⟦ -f' ⟧ ρ ⟩
  ⟦ proj₁ (lin-E (e :- f)) ⟧e ρ ∎
⟦lin-E k :* e ⟧ ρ = begin
  let (t' , e') = lin-E e in
  ⟦ k :* e  ⟧e ρ                ≡⟨ cong (k ℤ.*_) (⟦lin-E e ⟧ ρ) ⟩
  k ℤ.* ⟦ t' ⟧e ρ               ≡⟨ k ⟦*E e' ⟧ ρ ⟩
  ⟦ proj₁ (lin-E (k :* e)) ⟧e ρ ∎

open import Relation.Binary.SetoidReasoning renaming (_∎ to _✓; _≡⟨_⟩_ to _≋⟨_⟩_)

⟦lin_⟧ : ∀ {n φ} (p : NNF {n} φ) → φ ⇔ proj₁ (lin p)
⟦lin T        ⟧ ρ = ↔-refl
⟦lin F        ⟧ ρ = ↔-refl
⟦lin t₁ :≤ t₂ ⟧ ρ = begin⟨ ↔-setoid ⟩
  ⟦ t₁ ⟧e ρ ℤ.≤ ⟦ t₂ ⟧e ρ           ≈⟨ ZProp.m≤n⇒m-n≤0 , ZProp.m-n≤0⇒m≤n ⟩
  ⟦ t₁ ⟧e ρ ℤ.- ⟦ t₂ ⟧e ρ ℤ.≤ ℤ.+ 0 ≋⟨ cong (ℤ._≤ ℤ.+ 0) (⟦lin-E t₁ :- t₂ ⟧ ρ) ⟩
  ⟦ proj₁ (lin (t₁ :≤ t₂)) ⟧ ρ      ✓
⟦lin t₁ :≡ t₂ ⟧ ρ = begin⟨ ↔-setoid ⟩
  ⟦ t₁ ⟧e ρ ≡ ⟦ t₂ ⟧e ρ           ≈⟨ ZProp.m≡n⇒m-n≡0 _ _ , ZProp.m-n≡0⇒m≡n _ _ ⟩
  ⟦ t₁ ⟧e ρ ℤ.- ⟦ t₂ ⟧e ρ ≡ ℤ.+ 0 ≋⟨ cong (_≡ ℤ.+ 0) (⟦lin-E t₁ :- t₂ ⟧ ρ) ⟩
  ⟦ proj₁ (lin (t₁ :≡ t₂)) ⟧ ρ    ✓
⟦lin t₁ :≢ t₂ ⟧ ρ = begin⟨ ↔-setoid ⟩
  ⟦ t₁ ⟧e ρ ≢ ⟦ t₂ ⟧e ρ           ≈⟨ ↔¬ (ZProp.m≡n⇒m-n≡0 _ _ , ZProp.m-n≡0⇒m≡n _ _) ⟩
  ⟦ t₁ ⟧e ρ ℤ.- ⟦ t₂ ⟧e ρ ≢ ℤ.+ 0 ≋⟨ cong (_≢ ℤ.+ 0) (⟦lin-E t₁ :- t₂ ⟧ ρ) ⟩
  ⟦ proj₁ (lin (t₁ :≢ t₂)) ⟧ ρ    ✓
⟦lin k :| t   ⟧ ρ with k ≠0?
... | inj₁ refl = begin⟨ ↔-setoid ⟩
  ℤ.+ 0 ∣ ⟦ t ⟧e ρ              ≈⟨ 0∣⇒≡0 , divides (ℤ.+ 0) ⟩
  ⟦ t ⟧e ρ ≡ ℤ.+ 0              ≋⟨ cong (_≡ ℤ.+ 0) (⟦lin-E t ⟧ ρ) ⟩
  ⟦ lin-E t .proj₁ ⟧e ρ ≡ ℤ.+ 0 ✓
... | inj₂ k≠0  = begin⟨ ↔-setoid ⟩
  k ∣ ⟦ t ⟧e ρ              ≋⟨ cong (k ∣_) (⟦lin-E t ⟧ ρ) ⟩
  k ∣ ⟦ lin-E t .proj₁ ⟧e ρ ✓
⟦lin k :|̸ t   ⟧ ρ with k ≠0?
... | inj₁ refl = ↔¬_ $′ begin⟨ ↔-setoid ⟩
  ℤ.+ 0 ∣ ⟦ t ⟧e ρ              ≈⟨ 0∣⇒≡0 , divides (ℤ.+ 0) ⟩
  ⟦ t ⟧e ρ ≡ ℤ.+ 0              ≋⟨ cong (_≡ ℤ.+ 0) (⟦lin-E t ⟧ ρ) ⟩
  ⟦ lin-E t .proj₁ ⟧e ρ ≡ ℤ.+ 0 ✓
... | inj₂ k≠0  = ↔¬_ $′ begin⟨ ↔-setoid ⟩
  k ∣ ⟦ t ⟧e ρ              ≋⟨ cong (k ∣_) (⟦lin-E t ⟧ ρ) ⟩
  k ∣ ⟦ lin-E t .proj₁ ⟧e ρ ✓
⟦lin p :∧ q   ⟧ ρ = ⟦lin p ⟧ ρ ↔× ⟦lin q ⟧ ρ
⟦lin p :∨ q   ⟧ ρ = ⟦lin p ⟧ ρ ↔⊎ ⟦lin q ⟧ ρ
