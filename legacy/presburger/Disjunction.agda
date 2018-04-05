module Disjunction where

open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Fin as F
open import Data.Vec
open import Data.List hiding (and ; or) renaming (_∷_ to _L∷_)
open import Product
import Data.Product as P

open import Relation.Binary.PropositionalEquality

open import Representation
open import Properties
open import Properties-prop
open import Normalization.Linearization
open import Normalization.Unitarization
open import Semantics

open import Function

Fin-dij : ∀ {A : Set} {n p : ℕ} (φ : A → Lin n) (L : Vec A p) → Lin n
Fin-dij φ [] = F , F-islin
Fin-dij φ (x ∷ []) = φ x
Fin-dij φ (x ∷ x' ∷ xs) = ((proj₁ (φ x)) or (proj₁ (Fin-dij φ (x' ∷ xs)))) , or-islin (proj₂ (φ x)) (proj₂ (Fin-dij φ (x' ∷ xs)))

decr-lin : ∀ {n} {p} → Lin′ (ℕs n) (ℕs p) → Lin′ n p
decr-lin {n} {p} (.(val k) , val-islinn-i {.(ℕs p)} {k}) = val k , val-islinn-i
decr-lin {n} {p} (.((k :* var zero) :+ r) , var-islinn-i {.(ℕs p)} {k} {zero} {r} y () y0)
decr-lin {n} {p} (.((k :* var (Fs i)) :+ r) , var-islinn-i {.(ℕs p)} {k} {Fs i} {r} y (s≤s y') y0) with decr-lin (r , y0)
... | r' , h' = ((k :* var i) :+ r' ) , (var-islinn-i y y' h')

decr-exp : ∀ {n p} → Lin′ (ℕs n) (ℕs p) → Une n
decr-exp e with decr-lin e | lcme (decr-lin e)
... | e' | k , Hk = unit-exp e' k Hk

Inst-exp : ∀ {n p p'} (e : Lin′ (ℕs n) p) (e' : Lin′ (ℕs n) (ℕs p')) → Lin′ (ℕs n) 1
Inst-exp {n} {p} (.(val k) , val-islinn-i {.p} {k}) _ = val k , val-islinn-i
Inst-exp {n} {p} (.((k :* var zero) :+ r) , var-islinn-i {.p} {k} {zero} {r} y y' y0) (e' , He') with lin-mult k (e' , He')
... | e'' , He'' = lin-plus (e'' , islinn-i-weakening (s≤s z≤n) He'') (r , y0)
Inst-exp {n} {p} (.((k :* var (Fs i)) :+ r) , var-islinn-i {.p} {k} {Fs i} {r} y y' y0) _ = (k :* var (Fs i)) :+ r , var-islinn-i y (s≤s z≤n) y0

Inst-unit-exp : ∀ {n p p'} (e : Lin′ (ℕs n) p) (e' : Lin′ (ℕs n) (ℕs p')) → Une n
Inst-unit-exp e e' = decr-exp (Inst-exp e e')

Inst-form : ∀ {n p'} (φ : Lin (ℕs n)) (e' : Lin′ (ℕs n) (ℕs p')) → Lin n
Inst-form (.T , T-islin) e' = T , T-islin
Inst-form (.F , F-islin) e' = F , F-islin
Inst-form {n} (.(t₁ le val (+ 0)) , le-islin {t₁} y) e' with decr-lin (Inst-exp (t₁ , y) e')
... | e , He = e le val (+ 0) , le-islin He
Inst-form {n} (.(t₁ eq val (+ 0)) , eq-islin {t₁} y) e' with decr-lin (Inst-exp (t₁ , y) e')
... | e , He  = e eq val (+ 0) , eq-islin He
Inst-form {n} (.(not (t₁ eq val (+ 0))) , neq-islin {t₁} y) e' with decr-lin (Inst-exp (t₁ , y) e')
... | e , He  = not (e eq val (+ 0)) , neq-islin He
Inst-form {n} (.(k dvd t₁) , dvd-islin {k} {t₁} y y') e' with decr-lin (Inst-exp (t₁ , y') e')
... | e , He  = k dvd e , dvd-islin y He
Inst-form {n} (.(not (k dvd t₁)) , ndvd-islin {k} {t₁} y y') e' with decr-lin (Inst-exp (t₁ , y') e')
... | e , He  = (not (k dvd e)) , ndvd-islin y He
Inst-form {n} (.(φ₁ and φ₂) , and-islin {φ₁} {φ₂} y y') e' with Inst-form (φ₁ , y) e' | Inst-form (φ₂ , y') e'
... | ψ₁ , h₁ | ψ₂ , h₂ = ψ₁ and ψ₂ , and-islin h₁ h₂
Inst-form {n} (.(φ₁ or φ₂) , or-islin {φ₁} {φ₂} y y') e' with Inst-form (φ₁ , y) e' | Inst-form (φ₂ , y') e'
... | ψ₁ , h₁ | ψ₂ , h₂ = ψ₁ or ψ₂ , or-islin h₁ h₂

Finite-disjunction : ∀ {n p p' : ℕ} (φ : Lin (ℕs n)) (L : Vec (Lin′ (ℕs n) (ℕs p')) p) → Lin n
Finite-disjunction φ [] = F , F-islin
Finite-disjunction φ (x ∷ []) = Inst-form φ x
Finite-disjunction φ (x ∷ x' ∷ xs) with Inst-form φ x | Finite-disjunction φ (x' ∷ xs)
... | ψ₁ , h₁ | ψ₂ , h₂ = ψ₁ or ψ₂ , or-islin h₁ h₂

Finite-disjunction-unit : ∀ {n p p' : ℕ} (φ : Lin (ℕs n)) (L : Vec (Lin′ (ℕs n) (ℕs p')) (ℕs p)) → Unf n
Finite-disjunction-unit φ L with Finite-disjunction φ L | lcmφ (Finite-disjunction φ L)
... | ψ , h | P._,_ σ Hdiv = unitarise-aux (ψ , h) σ Hdiv

Finite-disjunction′ : ∀ {n p' : ℕ} (φ : Lin (ℕs n)) (L : List (Lin′ (ℕs n) (ℕs p'))) → Lin n
Finite-disjunction′ φ [] = F , F-islin
Finite-disjunction′ φ (x L∷ []) = Inst-form φ x
Finite-disjunction′ φ (x L∷ x' L∷ xs) with Inst-form φ x | Finite-disjunction′ φ (x' L∷ xs)
... | ψ₁ , h₁ | ψ₂ , h₂ = ψ₁ or ψ₂ , or-islin h₁ h₂