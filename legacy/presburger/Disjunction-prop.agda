module Disjunction-prop where

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

open import Data.Sign renaming (- to S- ; + to S+ ; _*_ to _S*_)
open import Data.Vec hiding (_∈_)
open import Data.List hiding (or ; and) renaming (_∷_ to _L∷_)
open import Product
open import Data.Sum
open import Data.Empty
import Data.Product as P

open import Function

open import Relation.Binary.PropositionalEquality

open import Representation
open import Properties
open import Properties-prop
open import Normalization.Linearization
open import Normalization.Linearization-prop
open import Semantics
open import Semantics-prop
open import Equivalence
open import Disjunction
open import Fin-prop
open import List-tools

open import Integer.Basic-Properties

open import Algebra.Structures
import Integer.Structures as IntProp

open import Relation.Binary
private module ℤr = IsCommutativeRing IntProp.isCommutativeRing
private module ℕ≤ = DecTotalOrder Nat.decTotalOrder

abstract

  decr-lin-sem : ∀ {n} {p} (e : Lin′ (ℕs n) (ℕs p)) x ρ → [| proj₁ e |]e (x ∷ ρ) ≡ [| proj₁ (decr-lin e) |]e ρ
  decr-lin-sem {n} {p} (.(val k) , val-islinn-i {.(ℕs p)} {k}) x ρ = refl
  decr-lin-sem {n} {p} (.((k :* var zero) :+ r) , var-islinn-i {.(ℕs p)} {k} {zero} {r} y () y0) x ρ
  decr-lin-sem {n} {p} (.((k :* var (Fs i)) :+ r) , var-islinn-i {.(ℕs p)} {k} {Fs i} {r} y (s≤s y') y0) x ρ with decr-lin (r , y0) | decr-lin-sem (r , y0) x ρ
  ... | r' , h' | Heq = ℤ+-left {[| k :* var (Fs i) |]e (x ∷ ρ)} Heq

  Inst-exp-sem : ∀ {n p p'} (e : Lin′ (ℕs n) p) (x : Lin′ (ℕs n) (ℕs p')) ρ → [| proj₁ e |]e (([| proj₁ x |]e (+ 0 ∷ ρ)) ∷ ρ) ≡ [| proj₁ (Inst-exp e x) |]e (+ 0 ∷ ρ)
  Inst-exp-sem {n} {p} (.(val k) , val-islinn-i {.p} {k}) x ρ = refl
  Inst-exp-sem {n} {p} (.((k :* var zero) :+ r) , var-islinn-i {.p} {k} {zero} {r} y y' y0) (e' , He') ρ with lin-mult k (e' , He') | lin-mult-sem k (e' , He') (+ 0 ∷ ρ)
  ... | e'' , He'' | Heq₁ with lin-plus (e'' , islinn-i-weakening (s≤s z≤n) He'') (r , y0) | lin-plus-sem (e'' , islinn-i-weakening (s≤s z≤n) He'') (r , y0) (+ 0 ∷ ρ)
  ... | r' , Hr' | Heq₂ = subst₂ (λ u v → u ℤ+ v ≡ [| r' |]e (+ 0 ∷ ρ)) (sym (Heq₁)) (context-simpl (r , y0) (+ 0) ([| e' |]e (+ 0 ∷ ρ)) ρ) Heq₂
  Inst-exp-sem {n} {p} (.((k :* var (Fs i)) :+ r) , var-islinn-i {.p} {k} {Fs i} {r} y y' y0) x ρ = ℤ+-left {[| k :* var (Fs i) |]e (([| proj₁ x |]e (+ 0 ∷ ρ)) ∷ ρ)} (context-simpl (r , y0) ([| proj₁ x |]e (+ 0 ∷ ρ)) (+ 0) ρ)

  Inst-form-sem : ∀ {n p'} (φ : Lin (ℕs n)) (x : Lin′ (ℕs n) (ℕs p')) ρ → [| proj₁ φ |] (([| proj₁ x |]e (+ 0 ∷ ρ)) ∷ ρ) ↔ [| proj₁ (Inst-form φ x) |] ρ
  Inst-form-sem (.T , T-islin) x ρ = P._,_ id id
  Inst-form-sem (.F , F-islin) x ρ = P._,_ id id
  Inst-form-sem {n} (.(t₁ le val (+ 0)) , le-islin {t₁} y) x ρ with Inst-exp (t₁ , y) x | Inst-exp-sem (t₁ , y) x ρ
  ... | e' , He' | Heq₁ with decr-lin (e' , He') | decr-lin-sem (e' , He') (+ 0) ρ
  ... | e'' , He'' | Heq₂ = P._,_ (λ h → subst (λ u → u ℤ≤ + 0) Heq₂ (subst (λ u → u ℤ≤ + 0) Heq₁ h)) (λ h → subst (λ u → u ℤ≤ + 0) (sym Heq₁) (subst (λ u → u ℤ≤ + 0) (sym Heq₂) h))
  Inst-form-sem {n} (.(t₁ eq val (+ 0)) , eq-islin {t₁} y) x ρ with Inst-exp (t₁ , y) x | Inst-exp-sem (t₁ , y) x ρ
  ... | e , He | Heq₁ with decr-lin (e , He) | decr-lin-sem (e , He) (+ 0) ρ
  ... | e' , He' | Heq₂ = P._,_ (λ h → subst (λ u → u ≡ + 0) Heq₂ (subst (λ u → u ≡ + 0) Heq₁ h))  (λ h → subst (λ u → u ≡ + 0) (sym Heq₁) (subst (λ u → u ≡ + 0) (sym Heq₂) h))
  Inst-form-sem {n} (.(not (t₁ eq val (+ 0))) , neq-islin {t₁} y) x ρ with Inst-exp (t₁ , y) x | Inst-exp-sem (t₁ , y) x ρ
  ... | e , He | Heq₁ with decr-lin (e , He) | decr-lin-sem (e , He) (+ 0) ρ
  ... | e' , He' | Heq₂ = P._,_ (λ h → subst (λ u → u ≡ + 0 → ⊥) Heq₂ (subst (λ u → u ≡ + 0 → ⊥) Heq₁ h)) (λ h → subst (λ u → u ≡ + 0 → ⊥) (sym Heq₁) (subst (λ u → u ≡ + 0 → ⊥) (sym Heq₂) h))
  Inst-form-sem {n} (.(k dvd t₁) , dvd-islin {k} {t₁} y y') x ρ with Inst-exp (t₁ , y') x | Inst-exp-sem (t₁ , y') x ρ
  ... | e , He | Heq₁ with decr-lin (e , He) | decr-lin-sem (e , He) (+ 0) ρ
  ... | e' , He' | Heq₂ = P._,_ (λ h → P._,_ (P.proj₁ h) (subst (λ u → u ≡ k ℤ* (P.proj₁ h)) Heq₂ (subst (λ u → u ≡ k ℤ* (P.proj₁ h)) Heq₁ (P.proj₂ h)))) (λ h → P._,_ (P.proj₁ h) (subst (λ u → u ≡ k ℤ* (P.proj₁ h)) (sym Heq₁) (subst (λ u → u ≡ k ℤ* (P.proj₁ h)) (sym Heq₂) (P.proj₂ h))))
  Inst-form-sem {n} (.(not (k dvd t₁)) , ndvd-islin {k} {t₁} y y') x ρ with Inst-exp (t₁ , y') x | Inst-exp-sem (t₁ , y') x ρ
  ... | e , He | Heq₁ with decr-lin (e , He) | decr-lin-sem (e , He) (+ 0) ρ
  ... | e' , He' | Heq₂ = P._,_ (λ hf h → hf (P._,_ (P.proj₁ h) (subst (λ u → u ≡ k ℤ* (P.proj₁ h)) (sym Heq₁) (subst (λ u → u ≡ k ℤ* (P.proj₁ h)) (sym Heq₂) (P.proj₂ h))))) (λ hf h → hf (P._,_ (P.proj₁ h) (subst (λ u → u ≡ k ℤ* (P.proj₁ h)) Heq₂ (subst (λ u → u ≡ k ℤ* (P.proj₁ h)) Heq₁ (P.proj₂ h)))))
  Inst-form-sem {n} (.(φ₁ and φ₂) , and-islin {φ₁} {φ₂} y y') x ρ with Inst-form (φ₁ , y) x | Inst-form (φ₂ , y') x | Inst-form-sem (φ₁ , y) x ρ | Inst-form-sem (φ₂ , y') x ρ
  ... | ψ₁ , h₁ | ψ₂ , h₂ | P._,_ p₁ q₁ | P._,_ p₂ q₂ = P._,_ (λ h → P._,_ (p₁ (P.proj₁ h)) (p₂ (P.proj₂ h))) (λ h → P._,_ (q₁ (P.proj₁ h)) (q₂ (P.proj₂ h)))
  Inst-form-sem {n} (.(φ₁ or φ₂) , or-islin {φ₁} {φ₂} y y') x ρ with Inst-form (φ₁ , y) x | Inst-form (φ₂ , y') x | Inst-form-sem (φ₁ , y) x ρ | Inst-form-sem (φ₂ , y') x ρ
  ... | ψ₁ , h₁ | ψ₂ , h₂ | P._,_ p₁ q₁ | P._,_ p₂ q₂ = P._,_ [ (inj₁ ∘ p₁) , (inj₂ ∘ p₂) ]′ [ (inj₁ ∘ q₁) , (inj₂ ∘ q₂) ]′

  Finite-disjunction-sem : ∀ {n p p' : ℕ} (φ : Lin (ℕs n)) (L : Vec (Lin′ (ℕs n) (ℕs p')) p) ρ →
                                     [| proj₁ (Finite-disjunction φ L) |] ρ ↔ (P.∃ (λ x → [| proj₁ φ |] (([| proj₁ (lookup x L) |]e (+ 0 ∷ ρ)) ∷ ρ)))
  Finite-disjunction-sem {n} φ [] ρ = P._,_ ⊥-elim (λ h → elim-Fin0 (P.proj₁ h))
  Finite-disjunction-sem {n} φ (x ∷ []) ρ with Inst-form φ x | Inst-form-sem φ x ρ
  ... | ψ , h | P._,_ p q = P._,_ (λ h → P._,_ zero (q h)) (λ h → p (elim-Fin1 (λ u → [| proj₁ φ |] (([| proj₁ (lookup u (x ∷ [])) |]e (+ 0 ∷ ρ)) ∷ ρ)) h))
  Finite-disjunction-sem φ (x ∷ x' ∷ xs) ρ with Inst-form φ x | Inst-form-sem φ x ρ | Finite-disjunction φ (x' ∷ xs) | Finite-disjunction-sem φ (x' ∷ xs) ρ
  ... | ψ₁ , h₁ | P._,_ p₁ q₁ | ψ₂ , h₂ | P._,_ p₂ q₂ = P._,_ [ (λ h → P._,_ zero (q₁ h)) , (λ h → P._,_ (Fs (P.proj₁ (p₂ h))) (P.proj₂ (p₂ h))) ]′ (λ h → [ (λ hx → inj₁ (p₁ (subst (λ u → [| proj₁ φ |] (([| proj₁ u |]e (+ 0 ∷ ρ)) ∷ ρ)) (cong (λ k → lookup k (x ∷ x' ∷ xs)) hx) (P.proj₂ h)))) , (λ hx → inj₂ (q₂ (P._,_ (P.proj₁ hx) (subst (λ u → [| proj₁ φ |] (([| proj₁ u |]e (+ 0 ∷ ρ)) ∷ ρ)) (cong (λ k → lookup k (x ∷ x' ∷ xs)) (P.proj₂ hx)) (P.proj₂ h))))) ]′ (elim-Finℕsn (P.proj₁ h)))

  Fin-dij-sem : ∀ {A : Set} {n p : ℕ} (φ : A → Lin n) (L : Vec A p) (ρ : Vec ℤ n)→
              [| proj₁ (Fin-dij φ L) |] ρ ↔ P.∃ (λ j → [| proj₁ (φ (lookup j L)) |] ρ )
  Fin-dij-sem φ [] ρ = P._,_ ⊥-elim (λ h → elim-Fin0 (P.proj₁ h))
  Fin-dij-sem φ (x ∷ []) ρ = P._,_ (λ h → P._,_ zero h) (λ h → elim-Fin1 _ h)
  Fin-dij-sem φ (x ∷ x' ∷ xs) ρ = P._,_ [ (λ h → P._,_ zero h) , (λ h → P._,_ (Fs (P.proj₁ (P.proj₁ (Fin-dij-sem φ (x' ∷ xs) ρ) h))) (P.proj₂ (P.proj₁ (Fin-dij-sem φ (x' ∷ xs) ρ) h))) ]′ (λ h → [ (λ hx → inj₁ (subst (λ u → [| proj₁ (φ (lookup u (x ∷ x' ∷ xs))) |] ρ) hx (P.proj₂ h))) , (λ hx → inj₂ (P.proj₂ (Fin-dij-sem φ (x' ∷ xs) ρ) (P._,_ (P.proj₁ hx) (subst (λ u → [| proj₁ (φ (lookup u (x ∷ x' ∷ xs))) |] ρ) (P.proj₂ hx) (P.proj₂ h))))) ]′ (elim-Finℕsn (P.proj₁ h)))

  Finite-disjunction′-sem : ∀ {n p : ℕ} (φ : Lin (ℕs n)) (L : List (Lin′ (ℕs n) (ℕs p))) ρ →
                         [| proj₁ (Finite-disjunction′ φ L) |] ρ ↔ P.∃ (λ (b : Lin′ (ℕs n) (ℕs p)) → P._×_ (b ∈ L) ([| proj₁ φ |] (([| proj₁ b |]e (+ 0 ∷ ρ)) ∷ ρ)))
  Finite-disjunction′-sem φ [] ρ = P._,_ ⊥-elim (λ h → b∈[]-elim (P.proj₁ (P.proj₂ h)))
  Finite-disjunction′-sem φ (x L∷ []) ρ with Inst-form φ x | Inst-form-sem φ x ρ
  ... | ψ , h | P._,_ p q = P._,_ (λ h → P._,_ x (P._,_ here (q h))) (λ h → p (subst (λ u → [| proj₁ φ |] (([| proj₁ u |]e (+ 0 ∷ ρ)) ∷ ρ)) (b∈[x]-elim (P.proj₁ (P.proj₂ h))) (P.proj₂ (P.proj₂ h))))
  Finite-disjunction′-sem φ (x L∷ x' L∷ xs) ρ with Inst-form φ x | Inst-form-sem φ x ρ | Finite-disjunction′ φ (x' L∷ xs) | Finite-disjunction′-sem φ (x' L∷ xs) ρ
  ... | ψ₁ , h₁ | P._,_ p₁ q₁ | ψ₂ , h₂ | P._,_ p₂ q₂ = P._,_ [ (λ h → P._,_ x (P._,_ here (q₁ h))) , (λ h → P._,_ (P.proj₁ (p₂ h)) (P._,_ (there (P.proj₁ (P.proj₂ (p₂ h)))) (P.proj₂ (P.proj₂ (p₂ h))))) ]′ (λ h → [ (λ hx → inj₁ (p₁ (subst (λ u → [| proj₁ φ |] (([| proj₁ u |]e (+ 0 ∷ ρ)) ∷ ρ)) hx (P.proj₂ (P.proj₂ h))))) , (λ hx → inj₂ (q₂ (P._,_ (P.proj₁ h) (P._,_ hx (P.proj₂ (P.proj₂ h)))))) ]′ (b∈L-elim (P.proj₁ (P.proj₂ h))))