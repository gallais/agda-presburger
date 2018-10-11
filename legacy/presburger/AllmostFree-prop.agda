module AllmostFree-prop where

open import Representation
open import Properties
open import Properties-prop
open import Semantics
open import Semantics-prop
open import Equivalence
open import Lcm
open import Disjunction
open import Disjunction-prop
open import Fin-prop

open import Integer.Basic-Properties
open import Integer.DivMod
open import Integer.LCM
import Integer.Structures as IntProp

open import Relation.Binary.PropositionalEquality

-- Datatypes
open import Data.Sign as S
open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Nat.Divisibility as ℕdiv
open import Data.Fin as F
open import Data.Integer.Divisibility as ℤdiv
open import Data.Integer.Properties

open import Product

import Data.Product as P
open import Data.Sum
open import Data.Vec renaming (map to Vmap)
open import Data.Unit
open import Data.Empty

open import Function
open import Relation.Binary
open import Algebra.Structures

private module Pos = Poset Div.poset
private module ℤr = IsCommutativeRing IntProp.isCommutativeRing

lcm-dvd : ∀ {n} (φ : Af0 n) → Dall (proj₁ φ)
lcm-dvd (.T , T-allmost) = (+ 1 , λ ()) , T-alldvd
lcm-dvd (.F , F-allmost) = (+ 1 , λ ()) , F-alldvd
lcm-dvd (.(t₁ le val (+ 0)) , le-allmost {t₁} y) =  (+ 1 , λ ()) , le-alldvd
lcm-dvd (.(t₁ eq val (+ 0)) , eq-allmost {t₁} y) =  (+ 1 , λ ()) , eq-alldvd
lcm-dvd (.(not (t₁ eq val (+ 0))) , neq-allmost {t₁} y) =  (+ 1 , λ ()) , neq-alldvd
lcm-dvd (.(k dvd t₁) , dvd-allmost {k} {t₁} y y') = (k , y) , dvd-alldvd y Pos.refl
lcm-dvd (.(not (k dvd t₁)) , ndvd-allmost {k} {t₁} y y') = (k , y) , ndvd-alldvd y Pos.refl
lcm-dvd (.(φ₁ and φ₂) , and-allmost {φ₁} {φ₂} y y') with lcm-dvd (φ₁ , y) | lcm-dvd (φ₂ , y')
... | (σ₁ , not0₁) , h₁ | (σ₂ , not0₂) , h₂ with lcm₂ σ₁ σ₂
... | σ , H with lcm₂-neq (σ₁ , not0₁) (σ₂ , not0₂) H | LCM.commonMultiple H
... | not0 | P._,_ h h' = (+ σ , not0) , and-alldvd (alldvd-ext h₁ (+ σ , not0) h) (alldvd-ext h₂ (+ σ , not0) h')
lcm-dvd (.(φ₁ or φ₂) , or-allmost {φ₁} {φ₂} y y') with lcm-dvd (φ₁ , y) | lcm-dvd (φ₂ , y')
... | (σ₁ , not0₁) , h₁ | (σ₂ , not0₂) , h₂ with lcm₂ σ₁ σ₂
... | σ , H with lcm₂-neq (σ₁ , not0₁) (σ₂ , not0₂) H | LCM.commonMultiple H
... | not0 | P._,_ h h' = (+ σ , not0) , or-alldvd (alldvd-ext h₁ (+ σ , not0) h) (alldvd-ext h₂ (+ σ , not0) h')

ℤ+-≡ : ∀ p q r → p ℤ+ q ≡ p ℤ+ r → q ≡ r
ℤ+-≡ p q r H = subst₂ (λ u v → u ≡ v) (P.proj₁ ℤr.+-identity q) (P.proj₁ ℤr.+-identity r) (subst (λ u → u ℤ+ q ≡ u ℤ+ r) (ℤ+-opp-l p) (subst₂ (λ u v → u ≡ v) (sym (ℤr.+-assoc (- p) p q)) (sym (ℤr.+-assoc (- p) p r)) (ℤ+-left { - p} H)))

abstract

  dvd-mod : ∀ {n} (t : Une (ℕs n)) (σ k : Notnull) → (proj₁ k) ℤdvd (proj₁ σ) → ∀ k' x ρ → [| (proj₁ k) dvd (proj₁ t) |] (x ∷ ρ) ↔ [| (proj₁ k) dvd (proj₁ t) |] ((x ℤ+ (k' ℤ* proj₁ σ)) ∷ ρ)
  dvd-mod {n} (.(val k) , val-isunit {.(ℕs n)} {k}) (σ , neqσ) (k' , neqk) Hdiv k0 x ρ = P._,_ id id
  dvd-mod (t , varn-isunit y) (σ , neqσ) (k , neqk) Hdiv k' x ρ with [| t |]e ((x ℤ+ (k' ℤ* σ)) ∷ ρ) | context-simpl (t , y) x (x ℤ+ (k' ℤ* σ)) ρ
  ... | .([| t |]e (x ∷ ρ)) | refl = P._,_ id id
  dvd-mod {n} (.((k' :* var zero) :+ t) , var0-isunit {.n} {t} {k'} y y') (σ , neqσ) (k , neqk) Hdiv k0 x ρ with [| t |]e ((x ℤ+ (k0 ℤ* σ)) ∷ ρ) | context-simpl (t , y') x (x ℤ+ (k0 ℤ* σ)) ρ | div-elim k σ Hdiv
  ... | .([| t |]e (x ∷ ρ)) | refl | P._,_ p Hp = P._,_ (λ h → P._,_ ((P.proj₁ h) ℤ+ (k' ℤ* (k0 ℤ* p))) (subst₂ (λ x' x0 → x' ℤ+ [| t |]e (x ∷ ρ) ≡ x0) (sym ((P.proj₁ ℤr.distrib) k' x (k0 ℤ* σ))) (sym ((P.proj₁ ℤr.distrib) k (P.proj₁ h) (k' ℤ* (k0 ℤ* p)))) (subst₂ (λ x' x0 → x' ≡ k ℤ* (P.proj₁ h) ℤ+ x0) (sym (ℤr.+-assoc (k' ℤ* x) (k' ℤ* (k0 ℤ* σ)) ([| t |]e (x ∷ ρ)))) (ℤr.*-comm (k' ℤ* (k0 ℤ* p)) k) (subst₂ (λ x' x0 → (k' ℤ* x) ℤ+ x' ≡ (k ℤ* (P.proj₁ h)) ℤ+ x0) (ℤr.+-comm ([| t |]e (x ∷ ρ)) (k' ℤ* (k0 ℤ* σ))) (sym (ℤr.*-assoc k' (k0 ℤ* p) k)) (subst₂ (λ x' x0 → x' ≡ k ℤ* (P.proj₁ h) ℤ+ (k' ℤ* x0)) (ℤr.+-assoc (k' ℤ* x) ([| t |]e (x ∷ ρ)) (k' ℤ* (k0 ℤ* σ))) (sym (ℤr.*-assoc k0 p k)) (subst₂ (λ x' x0 → x' ℤ+ (k' ℤ* (k0 ℤ* σ)) ≡ (k ℤ* (P.proj₁ h)) ℤ+ k' ℤ* (k0 ℤ* x0)) (sym (P.proj₂ h)) Hp refl)))))) (λ h → P._,_ ((- (k' ℤ* (k0 ℤ* p))) ℤ+ (P.proj₁ h)) (subst (λ x' → (k' ℤ* x) ℤ+ [| t |]e (x ∷ ρ) ≡ x') (sym ((P.proj₁ ℤr.distrib) k (- (k' ℤ* (k0 ℤ* p))) (P.proj₁ h))) (subst (λ x' → (k' ℤ* x) ℤ+ [| t |]e (x ∷ ρ) ≡ (k ℤ* - (k' ℤ* (k0 ℤ* p))) ℤ+ x') (P.proj₂ h) (subst (λ x' → (k' ℤ* x) ℤ+ [| t |]e (x ∷ ρ) ≡ x') (ℤr.+-assoc (k ℤ* - (k' ℤ* (k0 ℤ* p))) (k' ℤ* (x ℤ+ (k0 ℤ* σ))) ([| t |]e (x ∷ ρ))) (ℤ+-right {[| t |]e (x ∷ ρ)} (subst₂ (λ x₁ x₂ → k' ℤ* x ≡ x₁ ℤ+ x₂) (ℤr.*-comm (- (k' ℤ* (k0 ℤ* p))) k) (sym ((P.proj₁ ℤr.distrib) k' x (k0 ℤ* σ))) (subst₂ (λ x₁ x₂ → k' ℤ* x ≡ x₁ ℤ+ x₂) (-distr-ℤ*-l (k' ℤ* (k0 ℤ* p)) k) (ℤr.+-comm (k' ℤ* (k0 ℤ* σ)) (k' ℤ* x)) (subst₂ (λ x₁ x₂ → k' ℤ* x ≡ (- (x₁ ℤ* k)) ℤ+ ((k' ℤ* (k0 ℤ* x₂)) ℤ+ k' ℤ* x)) (ℤr.*-assoc k' k0 p) (sym Hp) (subst₂ (λ  x₁ x₂ → k' ℤ* x ≡ (- x₁) ℤ+ (x₂ ℤ+ k' ℤ* x)) (sym (ℤr.*-assoc (k' ℤ* k0) p k)) (ℤr.*-assoc k' k0 (p ℤ* k)) (subst (λ x' → k' ℤ* x ≡ x') (ℤr.+-assoc (- (k' ℤ* k0 ℤ* (p ℤ* k))) (k' ℤ* k0 ℤ* (p ℤ* k)) (k' ℤ* x)) (subst (λ x' → k' ℤ* x ≡ x' ℤ+ k' ℤ* x) (sym (ℤ+-opp-l (k' ℤ* k0 ℤ* (p ℤ* k)))) (sym (P.proj₁ ℤr.+-identity (k' ℤ* x))))))))))))))

  Af0-mod : ∀ {n} (φ : Af0 (ℕs n)) (σ : Dall (proj₁ φ)) k x ρ → [| proj₁ φ |] (x ∷ ρ) ↔ [| proj₁ φ |] ((x ℤ+ (k ℤ* (proj₁ (proj₁ σ)))) ∷ ρ)
  Af0-mod (.T , Hφ) ((σ , not0) , T-alldvd) k x ρ = P._,_ id id
  Af0-mod (.F , Hφ) ((σ , not0) , F-alldvd) k x ρ = P._,_ id id
  Af0-mod (.(val k le val (+ 0)) , le-allmost (val-free0 {k})) ((σ , not0) , le-alldvd) k' x ρ = P._,_ id id
  Af0-mod (.(t₁ le val (+ 0)) , le-allmost (varn-free0 y)) ((σ , not0) , le-alldvd {t₁}) k x ρ with [| t₁ |]e (x ∷ ρ) | context-simpl (t₁ , y) x (x ℤ+ (k ℤ* σ)) ρ
  ... | .([| t₁ |]e ((x ℤ+ k ℤ* σ) ∷ ρ)) | refl = P._,_ id id
  Af0-mod (.(val k eq val (+ 0)) , eq-allmost (val-free0 {k})) ((σ , not0) , eq-alldvd) k' x ρ = P._,_ id id
  Af0-mod (.(t₁ eq val (+ 0)) , eq-allmost (varn-free0 y)) ((σ , not0) , eq-alldvd {t₁}) k x ρ with [| t₁ |]e (x ∷ ρ) | context-simpl (t₁ , y) x (x ℤ+ (k ℤ* σ)) ρ
  ... | .([| t₁ |]e (x ℤ+ (k ℤ* σ) ∷ ρ)) | refl = P._,_ id id
  Af0-mod (.(not (val k eq val (+ 0))) , neq-allmost (val-free0 {k})) ((σ , not0) , neq-alldvd) k' x ρ = P._,_ id id
  Af0-mod (.(not (t₁ eq val (+ 0))) , neq-allmost (varn-free0 y)) ((σ , not0) , neq-alldvd {t₁}) k x ρ with [| t₁ |]e (x ∷ ρ) | context-simpl (t₁ , y) x (x ℤ+ (k ℤ* σ)) ρ
  ... | .([| t₁ |]e ((x ℤ+ k ℤ* σ) ∷ ρ)) | refl = P._,_ id id
  Af0-mod (.(k dvd t) , dvd-allmost y Ht) (σ , dvd-alldvd {k} {t} y' Hdiv) k' x ρ = dvd-mod (t , Ht) σ (k , y) Hdiv k' x ρ
  Af0-mod (.(not (k dvd t)) , ndvd-allmost y Ht) (σ , ndvd-alldvd {k} {t} y' Hdiv) k' x ρ with dvd-mod (t , Ht) σ (k , y) Hdiv k' x ρ
  ... | P._,_ P Q = P._,_ (λ h hf → h (Q hf)) (λ h hf → h (P hf))
  Af0-mod (.(φ₁ and φ₂) , and-allmost y y') ((σ , not0) , and-alldvd {φ₁} {φ₂} y0 y1) k x ρ with Af0-mod (φ₁ , y) ((σ , not0) , y0) k x ρ | Af0-mod (φ₂ , y') ((σ , not0) , y1) k x ρ
  ... | P._,_ p₁ q₁ | P._,_ p₂ q₂ = P._,_ (λ h → P._,_ (p₁ (P.proj₁ h)) (p₂ (P.proj₂ h))) (λ h → P._,_ (q₁ (P.proj₁ h)) (q₂ (P.proj₂ h)))
  Af0-mod (.(φ₁ or φ₂) , or-allmost y y') ((σ , not0) , or-alldvd {φ₁} {φ₂} y0 y1) k x ρ with Af0-mod (φ₁ , y) ((σ , not0) , y0) k x ρ | Af0-mod (φ₂ , y') ((σ , not0) , y1) k x ρ
  ... | P._,_ p₁ q₁ | P._,_ p₂ q₂ = P._,_ [ inj₁ ∘ p₁ , inj₂ ∘ p₂ ]′ [ inj₁ ∘ q₁ , inj₂ ∘ q₂ ]′

  ℕs-neq : ∀ {n} → ℕs n ≡ 0 → ⊥
  ℕs-neq ()

  Af0-Fin-equiv₁ : ∀ {n} (φ : Af0 (ℕs n)) (σ : Dall (proj₁ φ)) ρ → P.∃ (λ x → [| proj₁ φ |] (x ∷ ρ)) → P.∃ (λ (x : Fin ((∣_∣ ∘ proj₁ ∘ proj₁) σ)) → [| proj₁ φ |] ((+ toℕ x) ∷ ρ))
  Af0-Fin-equiv₁ φ ((σ , neqσ) , Hdiv) ρ (P._,_ x Hx) with ∣ σ ∣ | ◃-left-inverse σ
  Af0-Fin-equiv₁ φ ((.(+ 0) , neqσ) , Hdiv) ρ (P._,_ x Hx) | zero | refl = ⊥-elim (neqσ refl)
  Af0-Fin-equiv₁ φ ((σ , neqσ) , Hdiv) ρ (P._,_ x Hx) | ℕs n | w with neqσ ∘ abs-null-elim | ∣ σ ∣ | subst (λ u → ∣ u ∣ ≡ ℕs n) w (abs-◃ (sign σ) (ℕs n)) | (x ℤmod ∣ σ ∣) {neqσ ∘ abs-null-elim} | (x ℤdiv ∣ σ ∣) {neqσ ∘ abs-null-elim} | ℤmod-ℤdiv-correction x (∣ σ ∣) {neqσ ∘ abs-null-elim} | Af0-mod φ ((abs-Notnull (σ , neqσ)) , alldvd-abs Hdiv) ((x ℤdiv ∣ σ ∣) {neqσ ∘ abs-null-elim}) (+ toℕ ((x ℤmod ∣ σ ∣) {neqσ ∘ abs-null-elim})) ρ
  ... | notnull | .(ℕs n) | refl | r | q | H | P._,_ P Q = P._,_ r (Q (subst (λ u → [| proj₁ φ |] (u ∷ ρ)) (ℤr.+-comm (q ℤ* (+ (ℕs n))) (+ toℕ r)) (subst (λ u → [| proj₁ φ |] (u ∷ ρ)) H Hx)))

  Af0-Fin-equiv : ∀ {n} (φ : Af0 (ℕs n)) (σ : Dall (proj₁ φ)) ρ → P.∃ (λ x → [| proj₁ φ |] (x ∷ ρ)) ↔ P.∃ (λ (x : Fin ((∣_∣ ∘ proj₁ ∘ proj₁) σ)) → [| proj₁ φ |] ((+ toℕ x) ∷ ρ))
  Af0-Fin-equiv (φ , Hφ) ((σ , neqσ) , Hdiv) ρ = P._,_ (Af0-Fin-equiv₁ (φ , Hφ) ((σ , neqσ) , Hdiv) ρ) (λ h → P._,_ (+ toℕ (P.proj₁ h)) (P.proj₂ h))

  Af0-Fin-reduc : ∀ {n} (φ : Af0 (ℕs n)) (σ : Dall (proj₁ φ)) ρ → P.∃ (λ x → [| proj₁ φ |] (x ∷ ρ)) ↔ [| proj₁ (Finite-disjunction {_} {_} {0} (proj₁ φ , (isunitary-islin ∘ allmost-free0-isunitary) (proj₂ φ)) (Vmap (λ u → (val (+ toℕ u) , val-islinn-i)) (allFin ((∣_∣ ∘ proj₁ ∘ proj₁) σ)))) |] ρ
  Af0-Fin-reduc {n} φ σ ρ with Finite-disjunction-sem {_} {_} {0} (proj₁ φ , isunitary-islin (allmost-free0-isunitary (proj₂ φ))) (Vmap (λ u → val (+ toℕ u) , val-islinn-i) (allFin ∣ proj₁ (proj₁ σ) ∣)) ρ | Af0-Fin-equiv₁ φ σ ρ
  ... | P._,_ P₁ Q₁ | PQ = P._,_ (λ h → Q₁ (P._,_ (P.proj₁ (PQ h)) (subst (λ u → [| proj₁ φ |] ([| proj₁ u |]e (+ 0 ∷ ρ) ∷ ρ)) (Fin-Vmap-compat {_} {_} {Lin′ (ℕs n) 1} (λ (u : Fin ((∣_∣ ∘ proj₁ ∘ proj₁) σ)) → (val (+ toℕ u) , val-islinn-i)) (allFin ((∣_∣ ∘ proj₁ ∘ proj₁) σ)) (P.proj₁ (PQ h))) (subst (λ u → [| proj₁ φ |] ([| val (+ toℕ u) |]e (+ 0 ∷ ρ) ∷ ρ)) (sym (allFin-inv (P.proj₁ (PQ h)))) (P.proj₂ (PQ h)))))) (λ h → P.proj₂ (Af0-Fin-equiv φ σ ρ) (P._,_ (P.proj₁ (P₁ h)) (subst (λ u → [| proj₁ φ |] ([| val (+ toℕ u) |]e (+ 0 ∷ ρ) ∷ ρ)) (allFin-inv (P.proj₁ (P₁ h))) (subst (λ u → [| proj₁ φ |] ([| proj₁ u |]e (+ 0 ∷ ρ) ∷ ρ)) (sym (Fin-Vmap-compat {_} {_} {Lin′ (ℕs n) 1} (λ (u : Fin ((∣_∣ ∘ proj₁ ∘ proj₁) σ)) → (val (+ toℕ u) , val-islinn-i)) (allFin ((∣_∣ ∘ proj₁ ∘ proj₁) σ)) (P.proj₁ (P₁ h)))) (P.proj₂ (P₁ h))))))