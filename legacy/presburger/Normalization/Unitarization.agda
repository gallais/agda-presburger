module Normalization.Unitarization where

-- Things specific to the solver
open import Representation
open import Properties
open import Lcm
open import Normalization.Linearisation

-- Comparisons functions
open import Comparisons
open import Integer.Basic-Properties
open import Integer.Properties using (integrity)
open import Integer.Order-Properties
open import Integer.LCM
open import Properties-prop

-- About ≡ and Dec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- Datatypes
open import Data.Sign renaming (_*_ to _S*_ ; - to S- ; + to S+)
open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_)
open import Data.Nat.Divisibility as Div renaming (_∣_ to _ℕdiv_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)
open import Data.Integer.Properties
open import Data.Integer.Divisibility renaming (_∣_ to _ℤdiv_)
import Data.Product as P
open import Product
open import Data.Empty

open import Algebra.Structures
import Integer.Structures as IntProp
open import Function

open import Relation.Binary
private module Pos = Poset Div.poset
private module ℕ≤ = DecTotalOrder Nat.decTotalOrder
private module ℤr = IsCommutativeRing IntProp.isCommutativeRing

lcme : ∀ {n p} (e : Lin′ n p) → Σ Notnull (λ x → div-exp x (proj₁ e))
lcme {n} {p} (.(val k) , val-islinn-i {.p} {k}) = ((+ 1) , (λ ())) , val-div-exp
lcme {zero} {p} (.((k :* var _) :+ r) , var-islinn-i {.p} {k} {()} {r} y y' y0)
lcme {ℕs n} {p} (.((k :* var zero) :+ r) , var-islinn-i {.p} {k} {zero} {r} y y' y0) = (k , y) , (var0-div-exp Pos.refl y0)
lcme {ℕs n} {p} (.((k :* var (Fs i)) :+ r) , var-islinn-i {.p} {k} {Fs i} {r} y y' y0) = (+ 1 , λ ()) , varn-div-exp (var-islinn-i {ℕs n} y ℕ≤.refl y0)

lcmφ : ∀ {n} (φ : Lin n) → P.Σ Notnull (λ x → divall x (proj₁ φ))
lcmφ (.T , T-islin) = P._,_ ((+ 1) , (λ ())) T-divall
lcmφ (.F , F-islin) = P._,_ ((+ 1) , (λ ())) F-divall
lcmφ {n} (.(t₁ le val (+ 0)) , le-islin {t₁} y) with lcme (t₁ , y)
... | e , He = P._,_ e (le-divall He)
lcmφ {n} (.(t₁ eq val (+ 0)) , eq-islin {t₁} y) with lcme (t₁ , y)
... | e , He = P._,_ e (eq-divall He)
lcmφ {n} (.(not (t₁ eq val (+ 0))) , neq-islin {t₁} y) with lcme (t₁ , y)
... | e , He = P._,_ e (neq-divall He)
lcmφ {n} (.(k dvd t₁) , dvd-islin {k} {t₁} y y') with lcme (t₁ , y')
... | e , He = P._,_ e (dvd-divall y He)
lcmφ {n} (.(not (k dvd t₁)) , ndvd-islin {k} {t₁} y y') with lcme (t₁ , y')
... | e , He = P._,_ e (ndvd-divall y He)
lcmφ {n} (.(φ₁ and φ₂) , and-islin {φ₁} {φ₂} y y') with lcmφ (φ₁ , y) | lcmφ (φ₂ , y')
... | P._,_ (z₁ , not₁) dvd₁ | P._,_ (z₂ , not₂) dvd₂ with lcm₂ z₁ z₂
... | d , Hd = P._,_ (+ d , lcm₂-neq (z₁ , not₁) (z₂ , not₂) Hd) (and-divall (divall-ext dvd₁ (+ d , lcm₂-neq (z₁ , not₁) (z₂ , not₂) Hd) (P.proj₁ (LCM.commonMultiple Hd))) (divall-ext dvd₂ (+ d , lcm₂-neq (z₁ , not₁) (z₂ , not₂) Hd) (P.proj₂ (LCM.commonMultiple Hd))))
lcmφ {n} (.(φ₁ or φ₂) , or-islin {φ₁} {φ₂} y y') with lcmφ (φ₁ , y) | lcmφ (φ₂ , y')
... | P._,_ (z₁ , not₁) dvd₁ | P._,_ (z₂ , not₂) dvd₂ with lcm₂ z₁ z₂
... | d , Hd = P._,_ ((+ d) , (lcm₂-neq (z₁ , not₁) (z₂ , not₂) Hd)) (or-divall (divall-ext dvd₁ (+ d , lcm₂-neq (z₁ , not₁) (z₂ , not₂) Hd) (P.proj₁ (LCM.commonMultiple Hd))) (divall-ext dvd₂ (+ d , lcm₂-neq (z₁ , not₁) (z₂ , not₂) Hd) (P.proj₂ (LCM.commonMultiple Hd))))

Fin0-elim : ∀ (p : Fin 0) → ⊥
Fin0-elim ()

my-k : ∀ {n p : ℕ} (e : Lin′ n p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ℤ
my-k {n} (.(val k) , He) σ (val-div-exp {.n} {k}) = + 1
my-k (e , He) σ (varn-div-exp y) = + 1
my-k (.((k :* var zero) :+ t) , He) σ (var0-div-exp {n} {.σ} {t} {k} (divides q H) y') = + q

my-k-neq : ∀ {n p : ℕ} (e : Lin′ n p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → (my-k e σ Hdiv ≡ + 0) → ⊥
my-k-neq {n} (.(val k) , He) σ (val-div-exp {.n} {k}) ()
my-k-neq (e , He) σ (varn-div-exp y) ()
my-k-neq (.((k :* var zero) :+ t) , He) (σ , notnull) (var0-div-exp {n} {.(σ , notnull)} {t} {k} (divides .0 Hq) y') refl = notnull (abs-null-elim Hq)

unit-exp : ∀ {n p} → (e : Lin′ n p) (σ : Notnull) → div-exp σ (proj₁ e) → Une n
unit-exp {n} (.(val k) , val-islinn-i) σ (val-div-exp {.n} {k}) = val k , val-isunit
unit-exp {n} (e , He) σ (varn-div-exp y) = e , islinn-i-isunit e y
unit-exp (.((k :* var zero) :+ t) , He) (σ , notnull) (var0-div-exp {n} {.(σ , notnull)} {t} {k} (divides q H) y') with lin-mult (+ q) (t , y')
... | e' , He' = (((sign k S* sign σ) ◃ 1) :* var zero) :+ e' , var0-isunit (abs-◃ (sign k S* sign σ) 1) He'

unitarise-aux : ∀ {n} (φ : Lin n) (σ : Notnull) → divall σ (proj₁ φ) → Unf n
unitarise-aux (.T , Hφ) σ T-divall = T , T-isunitary
unitarise-aux (.F , Hφ) σ F-divall = F , F-isunitary
unitarise-aux (.(t₁ le val (+ 0)) , le-islin y) σ (le-divall {t₁} y') with unit-exp (t₁ , y) σ y'
... | e , He = (e le val (+ 0)) , (le-isunitary He)
unitarise-aux (.(t₁ eq val (+ 0)) , eq-islin y) σ (eq-divall {t₁} y') with unit-exp (t₁ , y) σ y'
... | e , He = e eq val (+ 0) , eq-isunitary He
unitarise-aux (.(not (t₁ eq val (+ 0))) , neq-islin y) σ (neq-divall {t₁} y') with unit-exp (t₁ , y) σ y'
... | e , He = not (e eq val (+ 0)) , neq-isunitary He
unitarise-aux (.(k dvd t₁) , dvd-islin y y') σ (dvd-divall {k} {t₁} y0 y1) with unit-exp (t₁ , y') σ y1
... | e , He = ((my-k (t₁ , y') σ y1) ℤ* k) dvd e , dvd-isunitary (λ x → my-k-neq (t₁ , y') σ y1 (integrity (subst (λ x' → x' ≡ + 0) (ℤr.*-comm (my-k (t₁ , y') σ y1) k) x) y)) He
unitarise-aux (.(not (k dvd t₁)) , ndvd-islin y y') σ (ndvd-divall {k} {t₁} y0 y1) with unit-exp (t₁ , y') σ y1
... | e , He = not (((my-k (t₁ , y') σ y1) ℤ* k) dvd e) , ndvd-isunitary (λ x → my-k-neq (t₁ , y') σ y1 (integrity (subst (λ x' → x' ≡ + 0) (ℤr.*-comm (my-k (t₁ , y') σ y1) k) x) y)) He
unitarise-aux (.(φ₁ and φ₂) , and-islin H₁ H₂) σ (and-divall {φ₁} {φ₂} H₁' H₂') with unitarise-aux (φ₁ , H₁) σ H₁' | unitarise-aux (φ₂ , H₂) σ H₂'
... | ψ₁ , h₁ | ψ₂ , h₂ = ψ₁ and ψ₂ , and-isunitary h₁ h₂
unitarise-aux (.(φ₁ or φ₂) , or-islin H₁ H₂) σ (or-divall {φ₁} {φ₂} H₁' H₂') with unitarise-aux (φ₁ , H₁) σ H₁' | unitarise-aux (φ₂ , H₂) σ H₂'
... | ψ₁ , h₁ | ψ₂ , h₂ = ψ₁ or ψ₂ , or-isunitary h₁ h₂

unitarise : ∀ {n} (φ : Lin n) → Unf n
unitarise φ with lcmφ φ
... | P._,_ σ Hdiv = unitarise-aux φ σ Hdiv