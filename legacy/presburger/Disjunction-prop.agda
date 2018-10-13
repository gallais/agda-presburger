module Disjunction-prop where

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Divisibility as Zdiv
open import Data.Fin as Fin using (Fin)
open import Data.List as List
open import Data.Sum as Sum
open import Data.Vec as Vec
open import Data.Product as Prod
open import Data.Empty
open import Function

open import Data.List.Any using (here; there; toSum)
open import Data.List.Membership.Propositional

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.SetoidReasoning as ≋-Reasoning

open import Representation
open import Properties
open import Properties-prop
open import Semantics
open import Semantics-prop
open import Equivalence
open import Disjunction
open import Normalization.Linearisation
open import Normalization.Linearisation-prop

⟦lin-E⁻_⟧ : ∀ {n p t} (e : Lin-E {ℕ.suc n} (ℕ.suc p) t) ρ {x} →
            ⟦ t ⟧e (x ∷ ρ) ≡ ⟦ proj₁ (lin-E⁻ e) ⟧e ρ
⟦lin-E⁻ val k                             ⟧ ρ = refl
⟦lin-E⁻ k *var Fin.zero  [ ()        ]+ e ⟧ ρ
⟦lin-E⁻ k *var Fin.suc p [ ℕ.s≤s prf ]+ e ⟧ ρ =
  cong (ℤ._+_ (toℤ k ℤ.* Vec.lookup p ρ)) (⟦lin-E⁻ e ⟧ ρ)

⟦⟨_/0⟩-E_⟧ : ∀ {n p p' u t} (f : Lin-E {ℕ.suc n} (ℕ.suc p) u) (e : Lin-E {ℕ.suc n} p' t) →
             ∀ ρ → ⟦ t ⟧e (⟦ u ⟧e (ℤ.+ 0 ∷ ρ) ∷ ρ) ≡ ⟦ proj₁ (⟨ f /0⟩-E e) ⟧e (ℤ.+ 0 ∷ ρ)
⟦⟨ f /0⟩-E val k                       ⟧ ρ = refl
⟦⟨_/0⟩-E_⟧ {n} {p} {p'} {u} f (k≠0 *var Fin.zero  [ prf ]+ e) ρ = begin
  let ⟦u⟧ = ⟦ u ⟧e (ℤ.+ 0 ∷ ρ); ρ′ = ℤ.+ 0 ∷ ρ; uρ = ⟦u⟧ ∷ ρ
      k = toℤ k≠0; r = toExp (Lin-E 1) e in
  k ℤ.* ⟦u⟧ ℤ.+ ⟦ r ⟧e uρ
    ≡⟨ cong₂ ℤ._+_ (k≠0 ≠0⟦*E f ⟧ ρ′) (lin-ext₁ e ⟦u⟧ (ℤ.+ 0) ρ) ⟩
  ⟦ (k≠0 ≠0*E f) .proj₁ ⟧e ρ′ ℤ.+ ⟦ r ⟧e ρ′
    ≡⟨ ⟦ Lin-E^wk (ℕ.s≤s ℕ.z≤n) (proj₂ (k≠0 ≠0*E f)) ⟧+E⟦ e ⟧ ρ′ ⟩
  ⟦ proj₁ (Lin-E^wk (ℕ.s≤s ℕ.z≤n) (proj₂ (k≠0 ≠0*E f)) +E e) ⟧e ρ′ ∎ where open ≡-Reasoning
⟦⟨_/0⟩-E_⟧ {n} {p} {p'} {u} f (k≠0 *var Fin.suc q [ prf ]+ e) ρ = begin
           let ⟦u⟧ = ⟦ u ⟧e (ℤ.+ 0 ∷ ρ); k = toℤ k≠0; r = toExp (Lin-E (2 ℕ.+ Fin.toℕ q)) e in
  k ℤ.* Vec.lookup q ρ ℤ.+ ⟦ r ⟧e (⟦u⟧ ∷ ρ)
    ≡⟨ cong (ℤ._+_ (k ℤ.* Vec.lookup q ρ)) (lin-ext₁ e ⟦u⟧ (ℤ.+ 0) ρ) ⟩
  k ℤ.* Vec.lookup q ρ ℤ.+ (⟦ r ⟧e (ℤ.pos 0 ∷ ρ)) ∎ where open ≡-Reasoning

⟦⟨_/0⟩-E⁻_⟧ : ∀ {n p p' u t} (f : Lin-E {ℕ.suc n} (ℕ.suc p) u) (e : Lin-E {ℕ.suc n} p' t) →
              ∀ ρ → ⟦ t ⟧e (⟦ u ⟧e (ℤ.+ 0 ∷ ρ) ∷ ρ) ≡ ⟦ proj₁ (⟨ f /0⟩-E⁻ e) ⟧e ρ
⟦⟨_/0⟩-E⁻_⟧ {n} {p} {p'} {u} {t} f e ρ = begin
  let ρ′ = ℤ.pos 0 ∷ ρ in
  ⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ)      ≡⟨ ⟦⟨ f /0⟩-E e ⟧ ρ ⟩
  ⟦ proj₁ (⟨ f /0⟩-E e) ⟧e ρ′ ≡⟨ ⟦lin-E⁻ proj₂ (⟨ f /0⟩-E e) ⟧ ρ ⟩
  ⟦ proj₁ (⟨ f /0⟩-E⁻ e) ⟧e ρ ∎ where open ≡-Reasoning

⟦⟨_/0⟩_⟧ : ∀ {n p u φ} (f : Lin-E {ℕ.suc n} (ℕ.suc p) u) (p : Lin {ℕ.suc n} φ) →
           ∀ ρ → ⟦ φ ⟧ (⟦ u ⟧e (ℤ.+ 0 ∷ ρ) ∷ ρ) ↔ ⟦ proj₁ (⟨ f /0⟩ p) ⟧ ρ
⟦⟨ f /0⟩ T      ⟧ ρ = ↔-refl
⟦⟨ f /0⟩ F      ⟧ ρ = ↔-refl
⟦⟨_/0⟩_⟧ {n} {p} {u} f (e :≤0) ρ = begin⟨ ↔-setoid ⟩
  let t = toExp (Lin-E 0) e; ρ′ = ℤ.+ 0 ∷ ρ in
  ⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ) ℤ.≤ ℤ.+ 0 ≡⟨ cong (ℤ._≤ ℤ.+ 0) (⟦⟨ f /0⟩-E⁻ e ⟧ ρ) ⟩
  ⟦ proj₁ (⟨ f /0⟩ (e :≤0)) ⟧ ρ ∎ where open ≋-Reasoning
⟦⟨_/0⟩_⟧ {n} {p} {u} f (e :≡0) ρ = begin⟨ ↔-setoid ⟩
  let t = toExp (Lin-E 0) e; ρ′ = ℤ.+ 0 ∷ ρ in
  ⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ) ≡ ℤ.+ 0 ≡⟨ cong (_≡ ℤ.+ 0) (⟦⟨ f /0⟩-E⁻ e ⟧ ρ) ⟩
  ⟦ proj₁ (⟨ f /0⟩ (e :≡0)) ⟧ ρ ∎ where open ≋-Reasoning
⟦⟨_/0⟩_⟧ {n} {p} {u} f (e :≢0) ρ = begin⟨ ↔-setoid ⟩
  let t = toExp (Lin-E 0) e; ρ′ = ℤ.+ 0 ∷ ρ in
  ¬ (⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ) ≡ ℤ.+ 0) ≡⟨ cong (λ p → ¬ (p ≡ ℤ.+ 0)) (⟦⟨ f /0⟩-E⁻ e ⟧ ρ) ⟩
  ⟦ proj₁ (⟨ f /0⟩ (e :≢0)) ⟧ ρ ∎ where open ≋-Reasoning
⟦⟨_/0⟩_⟧ {n} {p} {u} f (k≠0 :| e) ρ = begin⟨ ↔-setoid ⟩
  let k = toℤ k≠0; t = toExp (Lin-E 0) e; ρ′ = ℤ.+ 0 ∷ ρ in
  k Zdiv.∣ ⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ) ≡⟨ cong (k Zdiv.∣_) (⟦⟨ f /0⟩-E⁻ e ⟧ ρ) ⟩
  ⟦ proj₁ (⟨ f /0⟩ (k≠0 :| e)) ⟧ ρ ∎ where open ≋-Reasoning
⟦⟨_/0⟩_⟧ {n} {p} {u} f (k≠0 :|̸ e) ρ = begin⟨ ↔-setoid ⟩
  let k = toℤ k≠0; t = toExp (Lin-E 0) e; ρ′ = ℤ.+ 0 ∷ ρ in
  ¬ (k Zdiv.∣ ⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ)) ≡⟨ cong (λ p → ¬ (k Zdiv.∣ p)) (⟦⟨ f /0⟩-E⁻ e ⟧ ρ) ⟩
  ⟦ proj₁ (⟨ f /0⟩ (k≠0 :|̸ e)) ⟧ ρ ∎ where open ≋-Reasoning
⟦⟨ f /0⟩ φ :∧ ψ ⟧ ρ = ⟦⟨ f /0⟩ φ ⟧ ρ ↔× ⟦⟨ f /0⟩ ψ ⟧ ρ
⟦⟨ f /0⟩ φ :∨ ψ ⟧ ρ = ⟦⟨ f /0⟩ φ ⟧ ρ ↔⊎ ⟦⟨ f /0⟩ ψ ⟧ ρ


⟦⋁_⟧ : ∀ {n} (φs : List (∃ (Lin {n}))) →
       ∀ ρ → ⟦ proj₁ (⋁ φs) ⟧ ρ ↔ (∃ λ φ → φ ∈ φs × ⟦ proj₁ φ ⟧ ρ)
⟦⋁ []     ⟧ ρ = ⊥-elim , λ ()
⟦⋁ φ ∷ φs ⟧ ρ = let ih = ⟦⋁ φs ⟧ ρ in
  [ (λ p → -, here refl , p) , (Prod.map₂ (Prod.map₁ there) ∘′ (proj₁ ih)) ]′
  , λ where (φ , φ∈φ∷φs , p) → [ (λ where refl → inj₁ p)
                               , (λ φ∈φs → inj₂ (proj₂ ih (-, φ∈φs , p)))
                               ]′ (toSum φ∈φ∷φs)
