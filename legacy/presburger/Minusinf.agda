{-# OPTIONS --termination-depth=2 #-}

module Minusinf where

-- Our decision procedure modules
open import Representation
open import Properties
open import Properties-prop
open import AllmostFree-prop
open import Semantics
open import Semantics-prop
open import Equivalence
open import Comparisons
open import Lcm
open import Integer.Basic-Properties
open import Integer.Order-Properties

-- About ≡ and Dec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- Datatypes
open import Data.Sign as S
open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Nat.Divisibility as ℕ÷
open import Data.Fin as F
open import Data.Integer.Properties
open import Data.Integer.Divisibility as ℤ÷
open import Product
import Data.Product as P
open import Data.Sum
open import Data.Empty
open import Data.Unit
open import Data.Vec

open import Integer.LCM
open import Function

import Data.Nat.Properties as NatProp
import Integer.Structures as IntProp

open import Relation.Binary
open import Algebra.Structures

private module Pos = Poset Div.poset
private module ℕr = IsCommutativeSemiring NatProp.isCommutativeSemiring
private module ℤr = IsCommutativeRing IntProp.isCommutativeRing
private module ℤ≤ = DecTotalOrder Int.decTotalOrder


--open import Normalization.Linearization

-- Output a formula equivalent to φ if (var zero) can be as small as we want
minusinf : ∀ {n} → (φ : Unf n) → Af0 n
minusinf (.T , T-isunitary) = T , T-allmost
minusinf (.F , F-isunitary) = F , F-allmost
minusinf (.(((-[1+ 0 ] :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {n} {t} { -[1+ .0 ]} refl y')) = F , F-allmost
minusinf (.((((+ 1) :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {n} {t} {+ .1} refl y')) = T , T-allmost
minusinf (.(((k :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {n} {t} {k} y y')) = F , F-allmost
minusinf (.(not (((k :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {n} {t} {k} y y')) = T , T-allmost
minusinf (.(k dvd t₁) , dvd-isunitary {k} {t₁} y y') = k dvd t₁ , dvd-allmost y y'
minusinf (.(not (k dvd t₁)) , ndvd-isunitary {k} {t₁} y y') = not (k dvd t₁) , ndvd-allmost y y'
minusinf (.(φ₁ and φ₂) , and-isunitary {φ₁} {φ₂} y y') with minusinf (φ₁ , y) | minusinf (φ₂ , y')
... | ψ₁ , h₁ | ψ₂ , h₂ = ψ₁ and ψ₂ , and-allmost h₁ h₂
minusinf (.(φ₁ or φ₂) , or-isunitary {φ₁} {φ₂} y y') with minusinf (φ₁ , y) | minusinf (φ₂ , y')
... | ψ₁ , h₁ | ψ₂ , h₂ = ψ₁ or ψ₂ , or-allmost h₁ h₂
minusinf {n} (.(val k le val (+ 0)) , le-isunitary (val-isunit {.n} {k})) = val k le val (+ 0) , le-allmost val-free0
minusinf  (.(t₁ le val (+ 0)) , le-isunitary {t₁} (varn-isunit y)) = t₁ le val (+ 0) , le-allmost (varn-free0 y)
minusinf {n} (.(val k eq val (+ 0)) , eq-isunitary (val-isunit {.n} {k})) = val k eq val (+ 0) , eq-allmost val-free0
minusinf (.(t₁ eq val (+ 0)) , eq-isunitary {t₁} (varn-isunit y)) = t₁ eq val (+ 0) , eq-allmost (varn-free0 y)
minusinf {n} (.(not (val k eq val (+ 0))) , neq-isunitary (val-isunit {.n} {k})) = not (val k eq val (+ 0)) , neq-allmost val-free0
minusinf (.(not (t₁ eq val (+ 0))) , neq-isunitary {t₁} (varn-isunit y)) = not (t₁ eq val (+ 0)) , neq-allmost (varn-free0 y)

alldvd-and-proj : ∀ {n} {φ₁ φ₂ : Unf n} {δ : Notnull} (pr : alldvd δ (proj₁ (minusinf (proj₁ φ₁ and proj₁ φ₂ , and-isunitary (proj₂ φ₁) (proj₂ φ₂))))) → P._×_ (alldvd δ (proj₁ (minusinf φ₁))) (alldvd δ (proj₁ (minusinf φ₂)))
alldvd-and-proj {n} {φ₁ , Hφ₁} {φ₂ , Hφ₂} {δ} pr with minusinf (φ₁ , Hφ₁) | minusinf (φ₂ , Hφ₂)
alldvd-and-proj {n} {φ₁ , Hφ₁} {φ₂ , Hφ₂} {δ} (and-alldvd y y') | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = P._,_ y y'

alldvd-or-proj : ∀ {n} {φ₁ φ₂ : Unf n} {δ : Notnull} (pr : alldvd δ (proj₁ (minusinf (proj₁ φ₁ or proj₁ φ₂ , or-isunitary (proj₂ φ₁) (proj₂ φ₂))))) → P._×_ (alldvd δ (proj₁ (minusinf φ₁))) (alldvd δ (proj₁ (minusinf φ₂)))
alldvd-or-proj {n} {φ₁ , Hφ₁} {φ₂ , Hφ₂} {δ} pr with minusinf (φ₁ , Hφ₁) | minusinf (φ₂ , Hφ₂)
alldvd-or-proj {n} {φ₁ , Hφ₁} {φ₂ , Hφ₂} {δ} (or-alldvd y y') | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = P._,_ y y'

alldvd-and-l : ∀ {n} {φ₁ φ₂ : Unf n} {δ : Notnull} (pr : alldvd δ (proj₁ (minusinf (proj₁ φ₁ and proj₁ φ₂ , and-isunitary (proj₂ φ₁) (proj₂ φ₂))))) → alldvd δ (proj₁ (minusinf φ₁))
alldvd-and-l {n} {φ₁} {φ₂} {δ} = P.proj₁ ∘ (alldvd-and-proj {n} {φ₁} {φ₂} {δ})

alldvd-and-r : ∀ {n} {φ₁ φ₂ : Unf n} {δ : Notnull} (pr : alldvd δ (proj₁ (minusinf (proj₁ φ₁ and proj₁ φ₂ , and-isunitary (proj₂ φ₁) (proj₂ φ₂))))) → alldvd δ (proj₁ (minusinf φ₂))
alldvd-and-r {n} {φ₁} {φ₂} {δ} = P.proj₂ ∘ (alldvd-and-proj {n} {φ₁} {φ₂} {δ})

alldvd-or-l : ∀ {n} {φ₁ φ₂ : Unf n} {δ : Notnull} (pr : alldvd δ (proj₁ (minusinf (proj₁ φ₁ or proj₁ φ₂ , or-isunitary (proj₂ φ₁) (proj₂ φ₂))))) → alldvd δ (proj₁ (minusinf φ₁))
alldvd-or-l {n} {φ₁} {φ₂} {δ} = P.proj₁ ∘ (alldvd-or-proj {n} {φ₁} {φ₂} {δ})

alldvd-or-r : ∀ {n} {φ₁ φ₂ : Unf n} {δ : Notnull} (pr : alldvd δ (proj₁ (minusinf (proj₁ φ₁ or proj₁ φ₂ , or-isunitary (proj₂ φ₁) (proj₂ φ₂))))) → alldvd δ (proj₁ (minusinf φ₂))
alldvd-or-r {n} {φ₁} {φ₂} {δ} = P.proj₂ ∘ (alldvd-or-proj {n} {φ₁} {φ₂} {δ})

{- THIS IS USELESS: WE ALWAYS USE alldvd ON Af0 formulas
alldvd-minusinf : ∀ {n} {δ : Notnull} (φ : Unf n) → alldvd δ (proj₁ φ) → alldvd δ (proj₁ (minusinf φ))
alldvd-minusinf (.T , T-isunitary) T-alldvd = T-alldvd
alldvd-minusinf (.F , F-isunitary) F-alldvd = F-alldvd
alldvd-minusinf (.(((-[1+ 0 ] :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {n} {t} { -[1+ .0 ]} refl y')) le-alldvd = F-alldvd
alldvd-minusinf (.((((+ 1) :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {n} {t} {+ .1} refl y')) le-alldvd = T-alldvd
alldvd-minusinf (.(((k :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {n} {t} {k} y y')) eq-alldvd = F-alldvd
alldvd-minusinf (.(not (((k :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {n} {t} {k} y y')) neq-alldvd = T-alldvd
alldvd-minusinf (.(k dvd t₁) , dvd-isunitary y y') (dvd-alldvd {k} {t₁} y0 y1) = dvd-alldvd y y1
alldvd-minusinf (.(not (k dvd t₁)) , ndvd-isunitary y y') (ndvd-alldvd {k} {t₁} y0 y1) = ndvd-alldvd y y1
alldvd-minusinf (.(φ₁ and φ₂) , and-isunitary y y') (and-alldvd {φ₁} {φ₂} y0 y1) with minusinf (φ₁ , y) | minusinf (φ₂ , y') | alldvd-minusinf (φ₁ , y) y0 | alldvd-minusinf (φ₂ , y') y1
... | ψ₁ , h₁ | ψ₂ , h₂ | l | r = and-alldvd l r
alldvd-minusinf (.(φ₁ or φ₂) , or-isunitary y y') (or-alldvd {φ₁} {φ₂} y0 y1) with minusinf (φ₁ , y) | minusinf (φ₂ , y') | alldvd-minusinf (φ₁ , y) y0 | alldvd-minusinf (φ₂ , y') y1
... | ψ₁ , h₁ | ψ₂ , h₂ | l | r = or-alldvd l r
alldvd-minusinf {n} (.(val k le val (+ 0)) , le-isunitary (val-isunit {.n} {k})) le-alldvd = le-alldvd
alldvd-minusinf (.(t₁ le val (+ 0)) , le-isunitary (varn-isunit y)) (le-alldvd {t₁}) = le-alldvd
alldvd-minusinf {n} (.(val k eq val (+ 0)) , eq-isunitary (val-isunit {.n} {k})) eq-alldvd = eq-alldvd
alldvd-minusinf (.(t₁ eq val (+ 0)) , eq-isunitary (varn-isunit y)) (eq-alldvd {t₁}) = eq-alldvd
alldvd-minusinf {n} (.(not (val k eq val (+ 0))) , neq-isunitary (val-isunit {.n} {k})) neq-alldvd = neq-alldvd
alldvd-minusinf (.(not (t₁ eq val (+ 0))) , neq-isunitary (varn-isunit y)) (neq-alldvd {t₁}) = neq-alldvd
-}

bound-inf₁ : ∀ x y → x ℤ≤ -[1+ 0 ] ℤ+ - y → x ℤ+ y ≡ + 0 → ⊥
bound-inf₁ x y h₁ h₂ with ℤ+-opp-simpl {x} { - y} (subst (λ u → x ℤ+ u ≡ + 0) (sym (opp-invol y)) h₂)
bound-inf₁ .(- y) y h₁ h₂ | refl = ℤ<-irrefl' (- y) h₁

bound-inf₂ :  ∀ x y → x ℤ≤ -[1+ 0 ] ℤ+ y → (- x) ℤ+ y ≡ + 0 → ⊥
bound-inf₂ x y h₁ h₂ with ℤ+-opp-simpl {y} {x} (subst (λ u → u ≡ + 0) (ℤr.+-comm (- x) y) h₂)
bound-inf₂ x .x h₁ h₂ | refl = ℤ<-irrefl' x h₁

bound-inf : ∀ {n} (φ : Unf (ℕs n)) (ρ : Vec ℤ n) → ℤ
bound-inf (.T , T-isunitary) ρ = + 0
bound-inf (.F , F-isunitary) ρ = + 0
bound-inf {n} (.(val k le val (+ 0)) , le-isunitary (val-isunit {.(ℕs n)} {k})) ρ = + 0
bound-inf (.(t₁ le val (+ 0)) , le-isunitary {t₁} (varn-isunit y)) ρ = + 0
bound-inf {n} (.(((-[1+ 0 ] :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ρ = -[1+ 0 ] ℤ+ [| t |]e (+ 0 ∷ ρ)
bound-inf {n} (.((((+ 1) :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) ρ =  - [| t |]e (+ 0 ∷ ρ)
bound-inf {n} (.(val k eq val (+ 0)) , eq-isunitary (val-isunit {.(ℕs n)} {k})) ρ = + 0
bound-inf (.(t₁ eq val (+ 0)) , eq-isunitary {t₁} (varn-isunit y)) ρ = + 0
bound-inf {n} (.(((-[1+ 0 ] :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ρ = -[1+ 0 ] ℤ+ [| t |]e (+ 0 ∷ ρ)
bound-inf {n} (.((((+ 1) :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) ρ = -[1+ 0 ] ℤ+ (- [| t |]e ((+ 0) ∷ ρ))
bound-inf {n} (.(not (val k eq val (+ 0))) , neq-isunitary (val-isunit {.(ℕs n)} {k})) ρ = + 0
bound-inf (.(not (t₁ eq val (+ 0))) , neq-isunitary {t₁} (varn-isunit y)) ρ = + 0
bound-inf {n} (.(not (((-[1+ 0 ] :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ρ = -[1+ 0 ] ℤ+ [| t |]e (+ 0 ∷ ρ)
bound-inf {n} (.(not ((((+ 1) :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) ρ = -[1+ 0 ] ℤ+ (- [| t |]e ((+ 0) ∷ ρ))
bound-inf (.(k dvd t₁) , dvd-isunitary {k} {t₁} y y') ρ = + 0
bound-inf (.(not (k dvd t₁)) , ndvd-isunitary {k} {t₁} y y') ρ = + 0
bound-inf (.(φ₁ and φ₂) , and-isunitary {φ₁} {φ₂} y y') ρ = (bound-inf (φ₁ , y) ρ) ℤ⊓ (bound-inf (φ₂ , y') ρ)
bound-inf (.(φ₁ or φ₂) , or-isunitary {φ₁} {φ₂} y y') ρ = (bound-inf (φ₁ , y) ρ) ℤ⊓ (bound-inf (φ₂ , y') ρ)

cooper₂ : ∀ {n} (φ : Unf (ℕs n)) ρ x → x ℤ≤ (bound-inf φ ρ) → [| proj₁ φ |] (x ∷ ρ) ↔ [| proj₁ (minusinf φ) |] (x ∷ ρ)
cooper₂ (.T , T-isunitary) ρ x x-bd = P._,_ id id
cooper₂ (.F , F-isunitary) ρ x x-bd = P._,_ id id
cooper₂ {n} (.(val k le val (+ 0)) , le-isunitary (val-isunit {.(ℕs n)} {k})) ρ x x-bd = P._,_ id id
cooper₂ (.(t₁ le val (+ 0)) , le-isunitary {t₁} (varn-isunit y)) ρ x x-bd = P._,_ id id
cooper₂ {n} (.(((-[1+ 0 ] :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ρ x x-bd =  P._,_ (λ hf → ℤ<-irrefl' ((- x) ℤ+ [| t |]e (+ 0 ∷ ρ)) (ℤ≤.trans (subst₂ (λ u v → u ℤ+ v ℤ≤ + 0) (sym (unfold-opp x)) (context-simpl (t , y') x (+ 0) ρ) hf) (subst (λ u → + 0 ℤ≤ -[1+ 0 ] ℤ+ u) (ℤr.+-comm ([| t |]e (+ 0 ∷ ρ)) (- x)) (subst (λ u → + 0 ℤ≤ u) (ℤr.+-assoc -[1+ 0 ] ([| t |]e (+ 0 ∷ ρ)) (- x)) (ℤ≤-simpl₁' (-[1+ 0 ] ℤ+ [| t |]e (+ 0 ∷ ρ)) x x-bd))))) ⊥-elim
cooper₂ {n} (.((((+ 1) :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) ρ x x-bd = (P._,_ (λ _ → tt) (λ _ → subst₂ (λ u v → u ℤ+ v ℤ≤ + 0) (sym (P.proj₁ ℤr.*-identity x)) (context-simpl (t , y') (+ 0) x ρ) (subst (λ u → x ℤ+ u ℤ≤ + 0) (opp-invol ([| t |]e (+ 0 ∷ ρ))) (ℤ≤-simpl₁ x (- [| t |]e (+ 0 ∷ ρ)) x-bd))))
cooper₂ {n} (.(val k eq val (+ 0)) , eq-isunitary (val-isunit {.(ℕs n)} {k})) ρ x x-bd = P._,_ id id
cooper₂ (.(t₁ eq val (+ 0)) , eq-isunitary {t₁} (varn-isunit y)) ρ x x-bd = P._,_ id id
cooper₂ {n} (.((((-[1+ 0 ]) :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ρ x x-bd =  P._,_ (λ hf → bound-inf₂ x ([| t |]e (+ 0 ∷ ρ)) x-bd (subst₂ (λ u v → u ℤ+ v ≡ + 0) (sym (unfold-opp x)) (context-simpl (t , y') x (+ 0) ρ) hf)) ⊥-elim
cooper₂ {n} (.((((+ 1) :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) ρ x x-bd = P._,_ (λ hf → bound-inf₁ x ([| t |]e (+ 0 ∷ ρ)) x-bd (subst₂ (λ u v → u ℤ+ v ≡ + 0) (P.proj₁ ℤr.*-identity x) (context-simpl (t , y') x (+ 0) ρ) hf)) ⊥-elim
cooper₂ {n} (.(not (val k eq val (+ 0))) , neq-isunitary (val-isunit {.(ℕs n)} {k})) ρ x x-bd = P._,_ id id
cooper₂ (.(not (t₁ eq val (+ 0))) , neq-isunitary {t₁} (varn-isunit y)) ρ x x-bd = P._,_ id id
cooper₂ {n} (.(not (((-[1+ 0 ] :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ρ x x-bd = P._,_ (λ _ → tt) (λ _ → λ hf → bound-inf₂ x ([| t |]e (+ 0 ∷ ρ)) x-bd (subst₂ (λ u v → u ℤ+ v ≡ + 0) (sym (unfold-opp x)) (context-simpl (t , y') x (+ 0) ρ) hf))
cooper₂ {n} (.(not ((((+ 1) :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) ρ x x-bd = P._,_ (λ _ → tt) (λ _ → λ hf → bound-inf₁ x ([| t |]e (+ 0 ∷ ρ)) x-bd (subst₂ (λ u v → u ℤ+ v ≡ + 0) (P.proj₁ ℤr.*-identity x) (context-simpl (t , y') x (+ 0) ρ) hf))
cooper₂ (.(k dvd t₁) , dvd-isunitary {k} {t₁} y y') ρ x x-bd = P._,_ id id
cooper₂ (.(not (k dvd t₁)) , ndvd-isunitary {k} {t₁} y y') ρ x x-bd = P._,_ id id
cooper₂ (.(φ₁ and φ₂) , and-isunitary {φ₁} {φ₂} y y') ρ x x-bd with minusinf (φ₁ , y) | minusinf (φ₂ , y') | bound-inf (φ₁ , y) ρ | bound-inf (φ₂ , y') ρ | cooper₂ (φ₁ , y) ρ | cooper₂ (φ₂ , y') ρ
... | ψ₁ , h₁ | ψ₂ , h₂ | z₁ | z₂ | H₁ | H₂ = P._,_ (λ p → P._,_ (P.proj₁ (H₁ x (ℤ≤.trans x-bd (ℤ⊓-ℤ≤-l z₁ z₂))) (P.proj₁ p)) (P.proj₁ (H₂ x (ℤ≤.trans x-bd (ℤ⊓-ℤ≤-r z₁ z₂))) (P.proj₂ p))) (λ p → P._,_ (P.proj₂ (H₁ x (ℤ≤.trans x-bd (ℤ⊓-ℤ≤-l z₁ z₂))) (P.proj₁ p)) (P.proj₂ (H₂ x (ℤ≤.trans x-bd (ℤ⊓-ℤ≤-r z₁ z₂))) (P.proj₂ p)))
cooper₂ (.(φ₁ or φ₂) , or-isunitary {φ₁} {φ₂} y y') ρ x x-bd with minusinf (φ₁ , y) | minusinf (φ₂ , y') | bound-inf (φ₁ , y) ρ | bound-inf (φ₂ , y') ρ | cooper₂ (φ₁ , y) ρ | cooper₂ (φ₂ , y') ρ
... | ψ₁ , h₁ | ψ₂ , h₂ | z₁ | z₂ | H₁ | H₂ =  P._,_ [ (λ k → inj₁ (P.proj₁ (H₁ x (ℤ≤.trans x-bd (ℤ⊓-ℤ≤-l z₁ z₂))) k)) , (λ k → inj₂ (P.proj₁ (H₂ x (ℤ≤.trans x-bd (ℤ⊓-ℤ≤-r z₁ z₂))) k)) ]′ [ (λ k → inj₁ (P.proj₂ (H₁ x (ℤ≤.trans x-bd (ℤ⊓-ℤ≤-l z₁ z₂))) k)) , (λ k → inj₂ (P.proj₂ (H₂ x (ℤ≤.trans x-bd (ℤ⊓-ℤ≤-r z₁ z₂))) k)) ]′

cooper₂-simpl : ∀ {n} (φ : Unf (ℕs n)) ρ x → [| proj₁ (minusinf φ) |] (x ∷ ρ) → P.∃ (λ x → [| proj₁ φ |] (x ∷ ρ))
cooper₂-simpl φ ρ x H with ℤcompare x (bound-inf φ ρ)
cooper₂-simpl φ ρ x H | less y = P._,_ x (P.proj₂ (cooper₂ φ ρ x (ℤ≤.trans (nℤ≤sn x) y)) H)
cooper₂-simpl φ ρ .(bound-inf φ ρ) H | equal refl = P._,_ (bound-inf φ ρ) (P.proj₂ (cooper₂ φ ρ (bound-inf φ ρ) ℤ≤.refl) H)
cooper₂-simpl φ ρ x H | greater y with lcm-dvd (minusinf φ)
... | ((δ , neq) , Hdiv) with ℤ≤-reachability x (bound-inf φ  ρ) (δ , neq) (ℤ≤.trans (nℤ≤sn (bound-inf φ ρ)) y)
... | P._,_ k Hk = P._,_ (x ℤ- ((+ k) ℤ* + ∣ δ ∣)) (P.proj₂ (cooper₂ φ ρ (x ℤ- ((+ k) ℤ* + ∣ δ ∣)) Hk) (subst (λ u → [| proj₁ (minusinf φ) |] (u ∷ ρ)) (sym (unfold-ℤ- x ((+ k) ℤ* + ∣ δ ∣))) (subst (λ u → [| proj₁ (minusinf φ) |] (x ℤ+ u ∷ ρ)) (sym (-distr-ℤ*-l (+ k) (+ ∣ δ ∣))) (P.proj₁ (Af0-mod (minusinf φ) ((abs-Notnull (δ , neq)) , alldvd-abs Hdiv) (- (+ k)) x ρ) H))))