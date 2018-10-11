module Normalization.Linearisation where

-- Things specific to the solver
open import Representation
open import Properties
open import Properties-prop

-- Comparisons functions
open import Comparisons

-- About ≡ and Dec
open import Relation.Binary.PropositionalEquality

-- Datatypes
import Data.Nat as ℕ
import Data.Nat.Properties as NProp
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Data.Product as Prod
open import Data.Sum

-----
-- Linear expressions are closed under various operations
-----

infix 3 -E_
-E_ : ∀ {n n₀ e} → Lin-E {n} n₀ e → ∃ (Lin-E {n} n₀)
-E val k                 = -, val (ℤ.- k)
-E (k *var p [ prf ]+ e) = -, [- k ≠0] *var p [ prf ]+ proj₂ (-E e)

val_*var_[_]+E_ : ∀ {n n₀ e} (k : ℤ) (p : Fin n) → n₀ ℕ.≤ Fin.toℕ p →
                  Lin-E {n} (ℕ.suc (Fin.toℕ p)) e → ∃ (Lin-E {n} n₀)
val k *var p [ prf ]+E e with k ≠0?
... | inj₁ k≡0 = -, Lin-E^wk (NProp.≤-step prf) e
... | inj₂ k≠0 = -, k≠0 *var p [ prf ]+ e

infixr 4 _+E_
_+E_ : ∀ {n n₀ e f} → Lin-E {n} n₀ e → Lin-E {n} n₀ f → ∃ (Lin-E {n} n₀)
val k               +E val l                = -, val (k ℤ.+ l)
val k               +E l *var p [ prf ]+ f  = -, l *var p [ prf ]+ proj₂ (val k +E f)
k *var p [ prf ]+ e +E val l                = -, k *var p [ prf ]+ proj₂ (e +E val l)
k *var p [ prf ]+ e +E l *var q [ prf' ]+ f with Fcompare p q
... | less    p<q = -, k *var p [ prf ]+ proj₂ (e +E l *var q [ p<q' ]+ f)
  where p<q' = subst (_ ℕ.<_) (toℕ-inject₁ _) p<q
... | greater p>q = -, l *var q [ prf' ]+ proj₂ (k *var p [ p>q' ]+ e +E f)
  where p>q' = subst (_ ℕ.<_) (toℕ-inject₁ _) p>q
... | equal refl = val (toℤ k ℤ.+ toℤ l) *var p [ prf ]+E (proj₂ (e +E f))

_≠0*E_ : ∀ {n n₀ e k} → k ≠0 → Lin-E {n} n₀ e → ∃ (Lin-E {n} n₀)
k ≠0*E val l                 = -, val (toℤ k ℤ.* l)
k ≠0*E (l *var q [ prf ]+ f) = -, [ k * l ≠0] *var q [ prf ]+ proj₂ (k ≠0*E f)

_*E_ : ∀ {n n₀ e} → ℤ → Lin-E {n} n₀ e → ∃ (Lin-E {n} n₀)
k *E e with k ≠0?
... | inj₁ k≡0 = -, val (ℤ.+ 0)
... | inj₂ k≠0 = k≠0 ≠0*E e

-----
-- Linearize expressions
-----

lin-E : ∀ {n} → exp n → ∃ (Lin-E {n} 0)
lin-E (val k)  = -, val k
lin-E (var p)  = -, +[1+ 0 ] *var p [ ℕ.z≤n ]+ val (ℤ.+ 0)
lin-E (:- e)   = -E (proj₂ (lin-E e))
lin-E (e :+ f) = proj₂ (lin-E e) +E proj₂ (lin-E f)
lin-E (e :- f) = proj₂ (lin-E e) +E proj₂ (-E proj₂ (lin-E f))
lin-E (k :* e) = k *E proj₂ (lin-E e)

-----
-- Linearize formulas
-----

lin : ∀ {n φ} → NNF {n} φ → ∃ (Lin {n})
lin T          = -, T
lin F          = -, F
lin (t₁ :≤ t₂) = -, proj₂ (lin-E (t₁ :- t₂)) :≤0
lin (t₁ :≡ t₂) = -, proj₂ (lin-E (t₁ :- t₂)) :≡0
lin (t₁ :≢ t₂) = -, proj₂ (lin-E (t₁ :- t₂)) :≢0
lin (k :| t)   with k ≠0?
... | inj₁ k≡0 = -, proj₂ (lin-E t) :≡0
... | inj₂ k≠0 = -, k≠0 :| proj₂ (lin-E t)
lin (k :|̸ t)   with k ≠0?
... | inj₁ k≡0 = -, proj₂ (lin-E t) :≢0
... | inj₂ k≠0 = -, k≠0 :|̸ proj₂ (lin-E t)
lin (p :∧ q)   = -, proj₂ (lin p) :∧ proj₂ (lin q)
lin (p :∨ q)   = -, proj₂ (lin p) :∨ proj₂ (lin q)
