{-# OPTIONS  --no-termination-check #-}

module Normalization.Linearisation where

-- Things specific to the solver
open import Representation
open import Properties

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
open import Product
open import Data.Empty

open import Algebra.Structures
import Integer.Structures as IntProp
open import Function

open import Relation.Binary
private module Pos = Poset Div.poset
private module ℕ≤ = DecTotalOrder Nat.decTotalOrder
private module ℤr = IsCommutativeRing IntProp.isCommutativeRing

-- A bunch of useful lemmas (TODO:  see if we can get rid of them)
lemma : ∀ {k} → - k ≡ + 0 → k ≡ + 0
lemma { -[1+ n ]} ()
lemma {+ zero} _ = refl
lemma {+ ℕs n} ()

pwet : ∀ {n} {p₁ p₂ : Fin n} → ℕs (toℕ p₁) ℕ≤ toℕ (inject₁ p₂) → ℕs (toℕ p₁) ℕ≤ toℕ p₂
pwet {zero} {()} {()} H
pwet {ℕs n} {zero} {zero} ()
pwet {ℕs n} {zero} {Fs i} (s≤s m≤n) = s≤s z≤n
pwet {ℕs n} {Fs i} {zero} ()
pwet {ℕs n} {Fs i} {Fs i'} (s≤s m≤n) = s≤s (pwet m≤n)

n≤Sn : ∀ {n} → n ℕ≤ ℕs n
n≤Sn {zero} = z≤n
n≤Sn {ℕs n} = s≤s n≤Sn

-----
-- Linearisation functions
-----

lin-inject : ∀ {n p₁ p₂} {r : exp n} → p₁ ℕ≤ p₂ → islinn-i p₂ r → islinn-i p₁ r
lin-inject H val-islinn-i = val-islinn-i
lin-inject H (var-islinn-i y y' y0) = var-islinn-i y (ℕ≤.trans H y') y0

lin-opp : ∀ {n p} → Lin′ n p → Lin′ n p
lin-opp {n} {p} (.(val k) , val-islinn-i {.p} {k}) = (val (- k)) , val-islinn-i
lin-opp {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) with lin-opp (r , y0)
... | (e , e₁) = (((- k) :* (var p')) :+ e) , var-islinn-i (λ x → y (lemma x)) y' e₁

lin-plus : ∀ {n p} → Lin′ n p → Lin′ n p → Lin′ n p
lin-plus {n} {p} (.(val k) , val-islinn-i {.p} {k}) (.(val k') , val-islinn-i {.p} {k'}) = (val (k ℤ+ k')) , val-islinn-i
lin-plus {n} {p} (.(val k) , val-islinn-i {.p} {k}) (.((k' :* var p') :+ r) , var-islinn-i {.p} {k'} {p'} {r} y y' y0) with lin-plus (val k , val-islinn-i) (r , y0)
... | (e , He) = ((k' :* (var p')) :+ e) , var-islinn-i y y' He
lin-plus {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.(val k') , val-islinn-i {.p} {k'}) with lin-plus (r , y0) (val k' , val-islinn-i)
... | (e , He) = ((k :* (var p')) :+ e) , var-islinn-i y y' He
lin-plus {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.((k' :* var p0) :+ r') , var-islinn-i {.p} {k'} {p0} {r'} y1 y2 y3) with Fcompare p' p0
lin-plus {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.((k' :* var p0) :+ r') , var-islinn-i {.p} {k'} {p0} {r'} y1 y2 y3) | less H with lin-plus (r , y0) (((k' :* var p0) :+ r') , var-islinn-i {n} {ℕs (toℕ p')} {k'} {p0} {r'} y1 (pwet H) y3)
... | (e , He) = ((k :* (var p')) :+ e) , (var-islinn-i y y' He)
lin-plus {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.((k' :* var p') :+ r') , var-islinn-i {.p} {k'} {.p'} {r'} y1 y2 y3) | equal refl with ℤnull-dec (k ℤ+ k') | lin-plus (r , y0) (r' , y3)
... | yes H | (e , He) = e , lin-inject (ℕ≤.trans y2 n≤Sn) He
... | no ¬H | (e , He) = (((k ℤ+ k') :* (var p')) :+ e) , var-islinn-i ¬H y' He
lin-plus {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.((k' :* var p0) :+ r') , var-islinn-i {.p} {k'} {p0} {r'} y1 y2 y3) | greater H with lin-plus (((k :* var p') :+ r) , var-islinn-i {n} {ℕs (toℕ p0)} {k} {p'} {r} y (pwet H) y0) (r' , y3)
... | (e , He) = (((k' :* var p0) :+ e) , var-islinn-i y1 y2 He)

lin-mult : ∀ {n p} → ℤ → Lin′ n p → Lin′ n p
lin-mult {n} {p} k (.(val k') , val-islinn-i {.p} {k'}) = (val (k ℤ* k')) , val-islinn-i
lin-mult {n} {p} -[1+ n' ] (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) with lin-mult (-[1+ n' ]) (r , y0)
... | (e , He) = (((-[1+ n' ] ℤ* k) :* var p') :+ e) , var-islinn-i (λ x → y (integrity { -[1+ n' ]} x (λ ()))) y' He
lin-mult {n} {p} (+ zero) (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) = (val (+ 0)) , val-islinn-i
lin-mult {n} {p} (+ ℕs n') (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) with lin-mult (+ ℕs n') (r , y0)
... | (e , He) = ((((+ ℕs n') ℤ* k) :* (var p')) :+ e) , (var-islinn-i (λ x → y (integrity {+ ℕs n'} x (λ ()))) y' He)

lin-i : ∀ {n} → exp n → Lin′ n zero
lin-i (val y) = (val y) , val-islinn-i
lin-i (var y) = (((+ 1) :* var y) :+ val (+ 0)) , var-islinn-i (λ ()) z≤n val-islinn-i
lin-i (:- y) = lin-opp (lin-i y)
lin-i (y :+ y') = lin-plus (lin-i y) (lin-i y')
lin-i (y :- y') = lin-plus (lin-i y) (lin-opp (lin-i y'))
lin-i (y :* y') = lin-mult y (lin-i y')

lin : ∀ {n} → Nnf n → Lin n
lin (.T , T-isnnf) = T , T-islin
lin (.F , F-isnnf) = F , F-islin
lin {n} (.(t₁ le t₂) , le-isnnf {t₁} {t₂}) with lin-i (t₁ :- t₂)
... | (e , He) = (e le (val (+ 0))) , (le-islin He)
lin {n} (.(t₁ eq t₂) , eq-isnnf {t₁} {t₂}) with lin-i (t₁ :- t₂)
... | (e , He) = (e eq (val (+ 0))) , eq-islin He
lin {n} (.(not (t₁ eq t₂)) , neq-isnnf {t₁} {t₂}) with lin-i (t₁ :- t₂)
... | (e , He) = (not (e eq val (+ 0))) , (neq-islin He)
lin {n} (.(k dvd t₁) , dvd-isnnf {k} {t₁}) with lin-i t₁
lin {n} (. (-[1+ n' ] dvd t₁) , dvd-isnnf { -[1+ n' ]} {t₁}) | e , He = (-[1+ n' ] dvd e) , (dvd-islin (λ ()) He)
lin {n} (.((+ zero) dvd t₁) , dvd-isnnf {+ zero} {t₁}) | e , He = (e eq (val (+ 0))) , (eq-islin He)
lin {n} (.((+ ℕs n') dvd t₁) , dvd-isnnf {+ ℕs n'} {t₁}) | e , He = ((+ ℕs n') dvd e) , (dvd-islin (λ ()) He)
lin {n} (.(not (k dvd t₁)) , ndvd-isnnf {k} {t₁}) with lin-i t₁
lin {n} (.(not (-[1+ n' ] dvd t₁)) , ndvd-isnnf { -[1+ n' ]} {t₁}) | (e , He) = (not (-[1+ n' ] dvd e)) , (ndvd-islin (λ ()) He)
lin {n} (.(not ((+ 0) dvd t₁)) , ndvd-isnnf {+ zero} {t₁}) | (e , He) = not (e eq (val (+ 0))) , neq-islin He
lin {n} (.(not ((+ ℕs n') dvd t₁)) , ndvd-isnnf {+ ℕs n'} {t₁}) | (e , He) = (not ((+ ℕs n') dvd e)) , (ndvd-islin (λ ()) He)
lin {n} (.(φ₁ and φ₂) , and-isnnf {φ₁} {φ₂} y y') with lin (φ₁ , y) | lin (φ₂ , y')
... | (ψ₁ , H₁) | (ψ₂ , H₂) = (ψ₁ and ψ₂) , (and-islin H₁ H₂)
lin {n} (.(φ₁ or φ₂) , or-isnnf {φ₁} {φ₂} y y') with lin (φ₁ , y) | lin (φ₂ , y')
... | (ψ₁ , H₁) | (ψ₂ , H₂) = (ψ₁ or ψ₂) , (or-islin H₁ H₂)