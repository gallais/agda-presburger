module Disjunction-prop where

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Integer.Divisibility.Signed
open import Data.Fin as Fin using (Fin)
open import Data.List as List
open import Data.Sum as Sum
open import Data.Vec as Vec
open import Data.Product as Prod
open import Data.Empty
open import Function hiding (Equivalence; _↔_; _⇔_)

open import Data.Vec.Properties
open import Data.Vec.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Vec.Relation.Unary.Any.Properties as AnyProp
open import Data.Vec.Membership.Propositional as Mem using (_∈_)
import Data.Vec.Membership.Propositional.Properties as LMem

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.MultiSetoid as ≋-Reasoning

open import Representation
open import Properties
open import Properties-prop
open import Semantics
open import Semantics-prop
open import Equivalence
open import Disjunction
open import Normalization.Linearisation
open import Normalization.Linearisation-prop
open import StdlibCompat

⟦lin-E⁻_⟧ : ∀ {n p t} (e : Lin-E {ℕ.suc n} (ℕ.suc p) t) ρ {x} →
            ⟦ t ⟧e (x ∷ ρ) ≡ ⟦ proj₁ (lin-E⁻ e) ⟧e ρ
⟦lin-E⁻ val k                             ⟧ ρ = refl
⟦lin-E⁻ k *var Fin.zero  [ ()        ]+ e ⟧ ρ
⟦lin-E⁻ k *var Fin.suc p [ ℕ.s≤s prf ]+ e ⟧ ρ =
  cong (ℤ._+_ (toℤ k ℤ.* Vec.lookup ρ p)) (⟦lin-E⁻ e ⟧ ρ)

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
  k ℤ.* Vec.lookup ρ q ℤ.+ ⟦ r ⟧e (⟦u⟧ ∷ ρ)
    ≡⟨ cong (ℤ._+_ (k ℤ.* Vec.lookup ρ q)) (lin-ext₁ e ⟦u⟧ (ℤ.+ 0) ρ) ⟩
  k ℤ.* Vec.lookup ρ q ℤ.+ (⟦ r ⟧e (ℤ.pos 0 ∷ ρ)) ∎ where open ≡-Reasoning

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
  ⟦ proj₁ (⟨ f /0⟩ (e :≤0)) ⟧ ρ    ∎ where open ≋-Reasoning
⟦⟨_/0⟩_⟧ {n} {p} {u} f (e :≡0) ρ = begin⟨ ↔-setoid ⟩
  let t = toExp (Lin-E 0) e; ρ′ = ℤ.+ 0 ∷ ρ in
  ⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ) ≡ ℤ.+ 0 ≡⟨ cong (_≡ ℤ.+ 0) (⟦⟨ f /0⟩-E⁻ e ⟧ ρ) ⟩
  ⟦ proj₁ (⟨ f /0⟩ (e :≡0)) ⟧ ρ  ∎ where open ≋-Reasoning
⟦⟨_/0⟩_⟧ {n} {p} {u} f (e :≢0) ρ = ↔¬_ $′ begin⟨ ↔-setoid ⟩
  let t = toExp (Lin-E 0) e; ρ′ = ℤ.+ 0 ∷ ρ in
  ⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ) ≡ ℤ.+ 0 ≡⟨ cong (_≡ ℤ.+ 0) (⟦⟨ f /0⟩-E⁻ e ⟧ ρ) ⟩
  ⟦ proj₁ (⟨ f /0⟩ (e :≡0)) ⟧ ρ  ∎ where open ≋-Reasoning
⟦⟨_/0⟩_⟧ {n} {p} {u} f (k≠0 :| e) ρ = begin⟨ ↔-setoid ⟩
  let k = toℤ k≠0; t = toExp (Lin-E 0) e; ρ′ = ℤ.+ 0 ∷ ρ in
  k ∣ ⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ) ≡⟨ cong (k ∣_) (⟦⟨ f /0⟩-E⁻ e ⟧ ρ) ⟩
  ⟦ proj₁ (⟨ f /0⟩ (k≠0 :| e)) ⟧ ρ ∎ where open ≋-Reasoning
⟦⟨_/0⟩_⟧ {n} {p} {u} f (k≠0 :|̸ e) ρ = ↔¬_ $′ begin⟨ ↔-setoid ⟩
  let k = toℤ k≠0; t = toExp (Lin-E 0) e; ρ′ = ℤ.+ 0 ∷ ρ in
  k ∣ ⟦ t ⟧e (⟦ u ⟧e ρ′ ∷ ρ) ≡⟨ cong (k ∣_) (⟦⟨ f /0⟩-E⁻ e ⟧ ρ) ⟩
  ⟦ proj₁ (⟨ f /0⟩ (k≠0 :| e)) ⟧ ρ ∎ where open ≋-Reasoning
⟦⟨ f /0⟩ φ :∧ ψ ⟧ ρ = ⟦⟨ f /0⟩ φ ⟧ ρ ↔× ⟦⟨ f /0⟩ ψ ⟧ ρ
⟦⟨ f /0⟩ φ :∨ ψ ⟧ ρ = ⟦⟨ f /0⟩ φ ⟧ ρ ↔⊎ ⟦⟨ f /0⟩ ψ ⟧ ρ

toSum : ∀ {a} {A : Set a} {p} {P : A → Set p} {x m} {xs : Vec A m} →
        Any P (x ∷ xs) → P x ⊎ Any P xs
toSum (here px) = inj₁ px
toSum (there p) = inj₂ p

⟦⋁_⟧ : ∀ {m n} (φs : Vec (∃ (Lin {n})) m) → ∀ ρ →
       ⟦ proj₁ (⋁ φs) ⟧ ρ ↔ Any (λ φ → ⟦ proj₁ φ ⟧ ρ) φs
⟦⋁ []     ⟧ ρ = ⊥-elim , λ ()
⟦⋁ φ ∷ φs ⟧ ρ = [ here , there ∘′ proj₁ ih ]′ , Sum.map₂ (proj₂ ih) ∘′ toSum
  where ih = ⟦⋁ φs ⟧ ρ

⟦⋁[k<_]_⟧ : ∀ {n} (σ : ℕ) (φ : Fin σ → ∃ (Lin {n})) →
            ∀ ρ → ⟦ proj₁ (⋁[k< σ ] φ) ⟧ ρ ↔ (∃ λ (k : Fin σ) → ⟦ proj₁ (φ k) ⟧ ρ)
⟦⋁[k< σ ] φ ⟧ ρ = begin⟨ ↔-setoid ⟩
  let φs = Vec.map φ (Vec.allFin σ) in
  ⟦ proj₁ (⋁[k< σ ] φ) ⟧ ρ                       ↔⟨ ⟦⋁ φs ⟧ ρ ⟩
  Any (⟦_⟧ ρ ∘ proj₁) (Vec.map φ (Vec.allFin σ)) ↔⟨ AnyProp.map⁻ , AnyProp.map⁺ ⟩
  Any (⟦_⟧ ρ ∘ proj₁ ∘ φ) (Vec.allFin σ)         ↔⟨ Prod.map₂ proj₂ ∘′ LMem.fromAny
                                                  , LMem.toAny (LMem.∈-allFin⁺ _) ∘ proj₂ ⟩
  ∃ (λ k → ⟦ proj₁ (φ k) ⟧ ρ) ∎ where open ≋-Reasoning

⟦⋁[k<_]⟨k/0⟩_⟧ : ∀ {n f} (σ : ℕ) (φ : Lin {ℕ.suc n} f) ρ →
                 ⟦ proj₁ (⋁[k< σ ]⟨k/0⟩ φ) ⟧ ρ
               ↔ (∃ λ (k : Fin σ) → ⟦ f ⟧ (ℤ.+ (Fin.toℕ k) ∷ ρ))
⟦⋁[k<_]⟨k/0⟩_⟧ {n} σ φ ρ =  begin⟨ ↔-setoid ⟩
  let f = toForm Lin φ in
  ⟦ proj₁ (⋁[k< σ ]⟨k/0⟩ φ) ⟧ ρ
    ↔⟨ ⟦⋁[k< σ ] (λ k → ⟨ val (ℤ.pos (Fin.toℕ k)) /0⟩ φ) ⟧ ρ ⟩
  ∃ (λ k → ⟦ proj₁ (⟨ val (ℤ.pos (Fin.toℕ k)) /0⟩ φ) ⟧ ρ)
    ↔⟨ Prod.map₂ (proj₂ (⟦⟨ val _ /0⟩ φ ⟧ ρ))
     , Prod.map₂ (proj₁ (⟦⟨ val _ /0⟩ φ ⟧ ρ)) ⟩
  ∃ (λ k → ⟦ f ⟧ (ℤ.+ Fin.toℕ k ∷ ρ)) ∎ where open ≋-Reasoning
