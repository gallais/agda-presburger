{-# OPTIONS --no-termination-check #-}

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
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Integer.Properties using (integrity)
open import Integer.Basic-Properties
open import Integer.Elimination
open import Integer.Order-Properties

-- Datatypes
open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)
open import Data.Nat.Properties as NatProp
import Data.Product as P
open import Product
open import Data.Sum
open import Data.Empty
open import Data.Unit

open import Function

open import Data.Nat.Divisibility renaming (_∣_ to _div_)

open import Algebra.Structures
import Integer.Structures as IntProp

open import Relation.Binary
private module ℕr = IsCommutativeSemiring NatProp.isCommutativeSemiring
private module ℤr = IsCommutativeRing IntProp.isCommutativeRing
private module ℤ≤ = DecTotalOrder Int.decTotalOrder

-----
-- Compatibility with the semantics
-----

open import Data.Vec
open import Data.Sign renaming (_*_ to _S*_ ; - to S- ; + to S+)

abstract

  lin-opp-sem : ∀ {n p} (e : Lin′ n p) (ρ : Vec ℤ n) → - [| proj₁ e |]e ρ ≡ [| proj₁ (lin-opp e) |]e ρ
  lin-opp-sem {n} {p} (.(val k) , val-islinn-i {.p} {k}) ρ = refl
  lin-opp-sem {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) ρ with lin-opp (r , y0) | lin-opp-sem (r , y0) ρ
  ... | (e , He) | Heq = subst (λ x → x ≡ (sign (- k) S* sign ([| var p' |]e ρ) ◃ ∣ - k ∣ ℕ* ∣ [| var p' |]e ρ ∣) ℤ+ [| e |]e ρ) (sym (-distr-ℤ+ (k ℤ* [| var p' |]e ρ) ([| r |]e ρ))) (subst (λ x → (- (sign k S* sign (lookup p' ρ) ◃ ∣ k ∣ ℕ* ∣ lookup p' ρ ∣) ℤ+ - [| r |]e ρ ≡ (sign (- k) S* sign (lookup p' ρ) ◃ ∣ - k ∣ ℕ* ∣ lookup p' ρ ∣) ℤ+ x)) Heq (ℤ+-right { - [| r |]e ρ} (-distr-ℤ*-l k ([| var p' |]e ρ))))

  lin-mult-sem : ∀ {n p} (k : ℤ) (e : Lin′ n p) (ρ : Vec ℤ n) → k ℤ* [| proj₁ e |]e ρ ≡ [| proj₁ (lin-mult k e) |]e ρ
  lin-mult-sem {n} {p} k (.(val k') , val-islinn-i {.p} {k'}) ρ = refl
  lin-mult-sem {n} {p} -[1+ n' ] (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) ρ with lin-mult -[1+ n' ] (r , y0) | lin-mult-sem -[1+ n' ]  (r , y0) ρ
  ... | (e , He) | Heq = subst₂ (λ x x' → -[1+ n' ] ℤ* ((k ℤ* [| var p' |]e ρ) ℤ+ [| r |]e ρ) ≡  x ℤ+ x') (sym (ℤr.*-assoc (-[1+ n' ]) k ([| var p' |]e ρ))) Heq (P.proj₁ ℤr.distrib (-[1+ n' ]) (k ℤ* [| var p' |]e ρ) ([| r |]e ρ))
  lin-mult-sem {n} {p} (+ zero) (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) ρ = refl
  lin-mult-sem {n} {p} (+ ℕs n') (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) ρ with lin-mult (+ ℕs n') (r , y0) | lin-mult-sem (+ ℕs n') (r , y0) ρ
  ... | e , He | Heq = subst₂ (λ x x' → (+ ℕs n') ℤ* ((k ℤ* [| var p' |]e ρ) ℤ+ [| r |]e ρ) ≡  x ℤ+ x') (sym (ℤr.*-assoc (+ ℕs n') k ([| var p' |]e ρ))) Heq (P.proj₁ ℤr.distrib (+ ℕs n') (k ℤ* [| var p' |]e ρ) ([| r |]e ρ))

  lps-pre₁ : ∀ p q r s → p ℤ+ q ℤ+ (r ℤ+ s) ≡ (p ℤ+ r) ℤ+ (q ℤ+ s)
  lps-pre₁ p q r t = subst₂ (λ x x' → x ≡ x') (sym (ℤr.+-assoc p q (r ℤ+ t))) (sym  (ℤr.+-assoc p r (q ℤ+ t))) (ℤ+-left {p} (subst₂ (λ x x' → q ℤ+ x ≡ x') (ℤr.+-comm t r) (ℤr.+-comm (q ℤ+ t) r) (sym (ℤr.+-assoc q t r))))

  lps-pre₃ : ∀ k₁ k₂ → k₁ ≡ + 0 → k₁ ℤ* k₂ ≡ + 0
  lps-pre₃ .(+ 0) k₂ refl = refl

  lps-pre₄ : ∀ m n o p → m ℤ+ n ℤ+ (o ℤ+ p) ≡ n ℤ+ (m ℤ+ o ℤ+ p)
  lps-pre₄ m n o p = subst (λ x → m ℤ+ n ℤ+ (o ℤ+ p) ≡ n ℤ+ x) (sym (ℤr.+-assoc m o p)) (subst (λ x → m ℤ+ n ℤ+ (o ℤ+ p) ≡ x) (ℤr.+-assoc n m (o ℤ+ p)) (ℤ+-right (ℤr.+-comm m n)))

  lin-plus-sem : ∀ {n p} (e₁ e₂ : Lin′ n p) (ρ : Vec ℤ n) → [| (proj₁ e₁) :+ (proj₁ e₂) |]e ρ ≡  [| proj₁ (lin-plus e₁ e₂) |]e ρ
  lin-plus-sem {n} {p} (.(val k) , val-islinn-i {.p} {k}) (.(val k') , val-islinn-i {.p} {k'}) ρ = refl
  lin-plus-sem {n} {p} (.(val k) , val-islinn-i {.p} {k}) (.((k' :* var p') :+ r) , var-islinn-i {.p} {k'} {p'} {r} y y' y0) ρ with lin-plus (val k , val-islinn-i) (r , y0) | lin-plus-sem ((val k) , val-islinn-i) (r , y0) ρ
  ... | (e , He) | Heq = subst (λ x → x ≡ (sign k' S* sign ([| var p' |]e ρ) ◃ ∣ k' ∣ ℕ* ∣ [| var p' |]e ρ ∣) ℤ+ [| e |]e ρ) (ℤr.+-assoc k (k' ℤ* [| var p' |]e ρ) ([| r |]e ρ)) (subst (λ x → x ℤ+ [| r |]e ρ ≡ k' ℤ* [| var p' |]e ρ ℤ+ [| e |]e ρ) (ℤr.+-comm (k' ℤ* [| var p' |]e ρ) k) (subst (λ x → x ≡ k' ℤ* [| var p' |]e ρ ℤ+ [| e |]e ρ) (sym (ℤr.+-assoc (k' ℤ* [| var p' |]e ρ) k ([| r |]e ρ))) (ℤ+-left {[| k' :* var p' |]e ρ} Heq)))
  lin-plus-sem {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.(val k') , val-islinn-i {.p} {k'}) ρ with lin-plus (r , y0) (val k' , val-islinn-i) | lin-plus-sem (r , y0) (val k' , val-islinn-i) ρ
  ... | (e , He) | Heq = subst (λ x → x ≡ (k ℤ* [| var p' |]e ρ) ℤ+ [| e |]e ρ) (sym (ℤr.+-assoc (k ℤ* [| var p' |]e ρ) ([| r |]e ρ) k')) (ℤ+-left {[| k :* var p' |]e ρ} Heq)
  lin-plus-sem {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.((k' :* var p0) :+ r') , var-islinn-i {.p} {k'} {p0} {r'} y1 y2 y3) ρ with Fcompare p' p0
  lin-plus-sem {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.((k' :* var p0) :+ r') , var-islinn-i {.p} {k'} {p0} {r'} y1 y2 y3) ρ | less H with lin-plus (r , y0) (((k' :* var p0) :+ r') , var-islinn-i y1 (pwet H) y3) | lin-plus-sem (r , y0) (((k' :* var p0) :+ r') , var-islinn-i y1 (pwet H) y3) ρ
  ... | (e₁ , He₁) | Heq₁ = subst (λ x → (k ℤ* ([| var p' |]e ρ)) ℤ+ [| r |]e ρ ℤ+ ((k' ℤ* ([| var p0 |]e ρ)) ℤ+ [| r' |]e ρ) ≡ (k ℤ* ([| var p' |]e ρ)) ℤ+ x) Heq₁ (subst (λ x → x ≡ (k ℤ* [| var p' |]e ρ) ℤ+ ([| r |]e ρ ℤ+ ((k' ℤ* ([| var p0 |]e ρ)) ℤ+  [| r' |]e ρ))) (sym (ℤr.+-assoc (k ℤ* [| var p' |]e ρ) ([| r |]e ρ) (k' ℤ* [| var p0 |]e ρ ℤ+ [| r' |]e ρ))) refl)
  lin-plus-sem {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.((k' :* var p') :+ r') , var-islinn-i {.p} {k'} {.p'} {r'} y1 y2 y3) ρ | equal refl with ℤnull-dec (k ℤ+ k') | lin-plus (r , y0) (r' , y3) | lin-plus-sem (r , y0) (r' , y3) ρ
  ... | yes P | (e , He) | Heq = subst (λ x → x ≡ [| e |]e ρ) (sym (lps-pre₁ (sign k S* sign (lookup p' ρ) ◃ ∣ k ∣ ℕ* ∣ lookup p' ρ ∣) ( [| r |]e ρ) (sign k' S* sign (lookup p' ρ) ◃ ∣ k' ∣ ℕ* ∣ lookup p' ρ ∣) ([| r' |]e ρ))) (subst (λ x → x ℤ+ ([| r |]e ρ ℤ+ [| r' |]e ρ) ≡ [| e |]e ρ) (P.proj₂ ℤr.distrib (lookup p' ρ) k k') (subst (λ x → x ℤ+ ([| r |]e ρ ℤ+ [| r' |]e ρ) ≡ [| e |]e ρ) (sym (lps-pre₃ (k ℤ+ k') (lookup p' ρ) P)) (subst (λ x → + 0 ℤ+ ([| r |]e ρ ℤ+ [| r' |]e ρ) ≡ x) Heq (ℤ+-zero-l ([| r |]e ρ ℤ+ [| r' |]e ρ)))))
  ... | no ¬P | (e , He) | Heq = subst (λ x → x ≡ (sign (k ℤ+ k') S* sign (lookup p' ρ) ◃ ∣ k ℤ+ k' ∣ ℕ* ∣ lookup p' ρ ∣) ℤ+ [| e |]e ρ) (sym (lps-pre₁ (sign k S* sign (lookup p' ρ) ◃ ∣ k ∣ ℕ* ∣ lookup p' ρ ∣) ( [| r |]e ρ) (sign k' S* sign (lookup p' ρ) ◃ ∣ k' ∣ ℕ* ∣ lookup p' ρ ∣) ([| r' |]e ρ))) (subst (λ x → x ℤ+ ([| r |]e ρ ℤ+ [| r' |]e ρ) ≡ (sign (k ℤ+ k') S* sign (lookup p' ρ) ◃ ∣ k ℤ+ k' ∣ ℕ* ∣ lookup p' ρ ∣) ℤ+ [| e |]e ρ) (P.proj₂ ℤr.distrib (lookup p' ρ) k k') (subst (λ x → (sign (k ℤ+ k') S* sign (lookup p' ρ) ◃ ∣ k ℤ+ k' ∣ ℕ* ∣ lookup p' ρ ∣) ℤ+ ([| r |]e ρ ℤ+ [| r' |]e ρ) ≡ (sign (k ℤ+ k') S* sign (lookup p' ρ) ◃ ∣ k ℤ+ k' ∣ ℕ* ∣ lookup p' ρ ∣) ℤ+ x) Heq refl))
  lin-plus-sem {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) (.((k' :* var p0) :+ r') , var-islinn-i {.p} {k'} {p0} {r'} y1 y2 y3) ρ | greater H with lin-plus (((k :* var p') :+ r) , var-islinn-i y (pwet H) y0) (r' , y3) | lin-plus-sem (((k :* var p') :+ r) , var-islinn-i y (pwet H) y0) (r' , y3) ρ
  ... | (e , He) | Heq = subst (λ x → x ≡ (sign k' S* sign ([| var p0 |]e ρ) ◃ ∣ k' ∣ ℕ* ∣ [| var p0 |]e ρ ∣) ℤ+ [| e |]e ρ) (sym (lps-pre₁ (sign k S* sign (lookup p' ρ) ◃ ∣ k ∣ ℕ* ∣ lookup p' ρ ∣) ([| r |]e ρ) (sign k' S* sign (lookup p0 ρ) ◃ ∣ k' ∣ ℕ* ∣ lookup p0 ρ ∣) ([| r' |]e ρ))) (subst (λ x → (sign k S* sign (lookup p' ρ) ◃ ∣ k ∣ ℕ* ∣ lookup p' ρ ∣) ℤ+ (sign k' S* sign (lookup p0 ρ) ◃ ∣ k' ∣ ℕ* ∣ lookup p0 ρ ∣) ℤ+ ([| r |]e ρ ℤ+ [| r' |]e ρ) ≡ (sign k' S* sign ([| var p0 |]e ρ) ◃ ∣ k' ∣ ℕ* ∣ [| var p0 |]e ρ ∣) ℤ+ x) Heq (lps-pre₄ (sign k S* sign (lookup p' ρ) ◃ ∣ k ∣ ℕ* ∣ lookup p' ρ ∣) (sign k' S* sign (lookup p0 ρ) ◃ ∣ k' ∣ ℕ* ∣ lookup p0 ρ ∣) ([| r |]e ρ) ([| r' |]e ρ)))

  lin-i-sem : ∀ {n} (e : exp n) (ρ : Vec ℤ n) → [| e |]e ρ ≡ [| proj₁ (lin-i e) |]e ρ
  lin-i-sem (val y) ρ = refl
  lin-i-sem (var y) ρ with ∣ lookup y ρ ∣ ℕ+ 0 | P.proj₂ ℕr.+-identity (∣ lookup y ρ ∣)
  ... | .(∣ lookup y ρ ∣) | refl = subst (λ x → lookup y ρ ≡ x ℤ+ + 0) (sym (◃-left-inverse (lookup y ρ))) (sym (P.proj₂ ℤr.+-identity (lookup y ρ)))
  lin-i-sem (:- y) ρ with lin-i y | lin-i-sem y ρ
  ... | (e , He) | Heq = subst (λ x → - x ≡ [| proj₁ (lin-opp (e , He)) |]e ρ) (sym Heq) (lin-opp-sem (e , He) ρ)
  lin-i-sem (y :+ y') ρ with lin-i y | lin-i y' | lin-i-sem y ρ | lin-i-sem y' ρ
  ... | (e₁ , He₁) | (e₂ , He₂) | Heq₁ | Heq₂ = subst₂ (λ x x' → x ℤ+ x' ≡ [| proj₁ (lin-plus (e₁ , He₁) (e₂ , He₂)) |]e ρ) (sym Heq₁) (sym Heq₂) (lin-plus-sem (e₁ , He₁) (e₂ , He₂) ρ)
  lin-i-sem (y :- y') ρ with lin-i y | lin-i y' | lin-i-sem y ρ | lin-i-sem y' ρ
  ... | (e₁ , H₁) | (e₂ , H₂) | Heq₁ | Heq₂ with lin-opp (e₂ , H₂) | lin-opp-sem (e₂ , H₂) ρ
  ... | (e₃ , H₃) | Heq₃ with lin-plus (e₁ , H₁) (e₃ , H₃) | lin-plus-sem (e₁ , H₁) (e₃ , H₃) ρ
  ... | (e₄ , H₄) | Heq₄  = subst₂ (λ x x' → x ℤ- x' ≡ [| e₄ |]e ρ) (sym Heq₁) (sym Heq₂) (subst (λ x → [| e₁ |]e ρ ℤ- [| e₂ |]e ρ ≡ x) Heq₄ (subst (λ x → [| e₁ |]e ρ ℤ- [| e₂ |]e ρ ≡ [| e₁ |]e ρ ℤ+ x) Heq₃ (unfold-ℤ- ([| e₁ |]e ρ) ([| e₂ |]e ρ))))
  lin-i-sem (y :* y') ρ with lin-i y' | lin-i-sem y' ρ
  ... | (e , He) | Heq = subst (λ x → y ℤ* x ≡ [| proj₁ (lin-mult y (e , He)) |]e ρ) (sym Heq) (lin-mult-sem y (e , He) ρ)

  lin-sem : ∀ {n} → (φ : Nnf n) → (proj₁ φ) ⇔ proj₁ (lin φ)
  lin-sem (.T , T-isnnf) ρ = P._,_ (λ x → x) (λ x → x)
  lin-sem (.F , F-isnnf) ρ = P._,_ (λ x → x) (λ x → x)
  lin-sem {n} (.(t₁ le t₂) , le-isnnf {t₁} {t₂}) ρ with lin ((t₁ le t₂) , le-isnnf) | lin-opp (lin-i t₂) | lin-opp-sem (lin-i t₂) ρ | lin-i-sem t₂ ρ
  ... | e₁ , He₁ | e₂ , He₂ | Heq₁ | Ht₂ with lin-plus (lin-i t₁) (e₂ , He₂) | lin-plus-sem (lin-i t₁) (e₂ , He₂) ρ | lin-i-sem t₁ ρ
  ... | e₃ , He₃ | Heq₂ | Ht₁ = P._,_ (λ x → subst (λ x' → x' ℤ≤ + 0) Heq₂ (subst (λ x' → [| proj₁ (lin-i t₁) |]e ρ ℤ+ x' ℤ≤ + 0) Heq₁ (subst₂ (λ x' x0 → x' ℤ+ - x0 ℤ≤ + 0) Ht₁ Ht₂ (ℤ≤-simpl₁ ([| t₁ |]e ρ) ([| t₂ |]e ρ) x)))) (λ x → ℤ≤-simpl₂ ([| t₁ |]e ρ) ([| t₂ |]e ρ) (subst₂ (λ x' x0 → x' ℤ+ - x0 ℤ≤ + 0) (sym Ht₁) (sym Ht₂) (subst (λ x' → [| proj₁ (lin-i t₁) |]e ρ ℤ+ x' ℤ≤ + 0) (sym Heq₁) (subst (λ x' → x' ℤ≤ + 0) (sym Heq₂) x))))
  lin-sem {n} (.(t₁ eq t₂) , eq-isnnf {t₁} {t₂}) ρ with lin (t₁ eq t₂ , eq-isnnf) | lin-opp (lin-i t₂) | lin-opp-sem (lin-i t₂) ρ | lin-i-sem t₂ ρ
  ... | e₁ , He₁ | e₂ , He₂ | Heq₁ | Ht₂ with lin-plus (lin-i t₁) (e₂ , He₂) | lin-plus-sem (lin-i t₁) (e₂ , He₂) ρ | lin-i-sem t₁ ρ
  ... | e₃ , He₃ | Heq₂ | Ht₁ = P._,_ (λ x → subst (λ x' → x' ≡ + 0) Heq₂ (subst₂ (λ x' x0 → x' ℤ+ x0 ≡ + 0) Ht₁ Heq₁ (subst₂ (λ x' x0 → x' ℤ+ - x0 ≡ + 0) (sym x) Ht₂ (ℤ+-opp-r ([| t₂ |]e ρ))))) (λ x → subst₂ (λ x' x0 → x' ≡ x0) (sym Ht₁) (sym Ht₂) (ℤ+-opp-simpl (subst₂ (λ x' x0 → [| proj₁ (lin-i t₁) |]e ρ ℤ+ x' ≡ x0) (sym Heq₁) x Heq₂)))
  lin-sem {n} (.(not (t₁ eq t₂)) , neq-isnnf {t₁} {t₂}) ρ with lin (not (t₁ eq t₂) , neq-isnnf) | lin-opp (lin-i t₂) | lin-opp-sem (lin-i t₂) ρ | lin-i-sem t₂ ρ
  ... | e₁ , He₁ | e₂ , He₂ | Heq₁ | Ht₂ with lin-plus (lin-i t₁) (e₂ , He₂) | lin-plus-sem (lin-i t₁) (e₂ , He₂) ρ | lin-i-sem t₁ ρ
  ... | e₃ , He₃ | Heq₂ | Ht₁ = P._,_ (λ x x' → x (subst₂ (λ x0 x1 → x0 ≡ x1) (sym Ht₁) (sym Ht₂) (ℤ+-opp-simpl (subst₂ (λ x0 x1 → [| proj₁ (lin-i t₁) |]e ρ ℤ+ x0 ≡ x1) (sym Heq₁) x' Heq₂)))) (λ x x' → x ( subst (λ x0 → x0 ≡ + 0) Heq₂ (subst₂ (λ x0 x1 → x0 ℤ+ x1 ≡ + 0) Ht₁ Heq₁ (subst₂ (λ x0 x1 → x0 ℤ+ - x1 ≡ + 0) (sym x') Ht₂ (ℤ+-opp-r ([| t₂ |]e ρ))))))
  lin-sem {n} (.(k dvd t₁) , dvd-isnnf {k} {t₁}) ρ with lin-i t₁ | lin-i-sem t₁ ρ
  lin-sem {n} (.(-[1+ n' ] dvd t₁) , dvd-isnnf { -[1+ n' ]} {t₁}) ρ | e , He | Ht₁ = P._,_ (λ x → P._,_ (P.proj₁ x) (subst (λ x' → x' ≡ (-[1+ n' ] ℤ* (P.proj₁ x))) Ht₁ (P.proj₂ x))) (λ x → P._,_ (P.proj₁ x) (subst (λ x' → x' ≡ -[1+ n' ] ℤ* (P.proj₁ x)) (sym Ht₁) (P.proj₂ x)))
  lin-sem {n} (.((+ zero) dvd t₁) , dvd-isnnf {+ zero} {t₁}) ρ | e , He | Ht₁ = P._,_ (λ x → subst (λ x' → x' ≡ + 0) Ht₁ (P.proj₂ x)) (λ x → P._,_ (+ 0) (subst (λ x' → x' ≡ + 0) (sym Ht₁) x))
  lin-sem {n} (.((+ ℕs n') dvd t₁) , dvd-isnnf {+ ℕs n'} {t₁}) ρ | e , He | Ht₁ = P._,_ (λ x → P._,_ (P.proj₁ x) (subst (λ x' → x' ≡ (+ ℕs n') ℤ* (P.proj₁ x)) Ht₁ (P.proj₂ x))) (λ x → P._,_ (P.proj₁ x) (subst (λ x' → x' ≡ (+ ℕs n') ℤ* (P.proj₁ x)) (sym Ht₁) (P.proj₂ x)))
  lin-sem {n} (.(not (k dvd t₁)) , ndvd-isnnf {k} {t₁}) ρ with lin-i t₁ | lin-i-sem t₁ ρ
  lin-sem {n} (.(not (-[1+ n' ] dvd t₁)) , ndvd-isnnf { -[1+ n' ]} {t₁}) ρ | e₁ , H₁ | Ht₁ = P._,_ (λ x x' → x (P._,_ (P.proj₁ x') (subst (λ x0 → x0 ≡ -[1+ n' ] ℤ* (P.proj₁ x')) (sym Ht₁) (P.proj₂ x')))) (λ x x' → x (P._,_ (P.proj₁ x') (subst (λ x0 → x0 ≡ -[1+ n' ] ℤ* (P.proj₁ x')) Ht₁ (P.proj₂ x'))))
  lin-sem {n} (.(not ((+ zero) dvd t₁)) , ndvd-isnnf {+ zero} {t₁}) ρ | e₁ , H₁ | Ht₁ = P._,_ (λ x x' → x (P._,_ (+ 0) (subst (λ x0 → x0 ≡ + 0) (sym Ht₁) x'))) (λ x x' → x (subst (λ x0 → x0 ≡ + 0) Ht₁ (P.proj₂ x')))
  lin-sem {n} (.(not ((+ ℕs n') dvd t₁)) , ndvd-isnnf {+ ℕs n'} {t₁}) ρ | e₁ , H₁ | Ht₁ = P._,_ (λ x x' → x (P._,_ (P.proj₁ x') (subst (λ x0 → x0 ≡ (+ ℕs n') ℤ* (P.proj₁ x')) (sym Ht₁) (P.proj₂ x')))) (λ x x' → x (P._,_ (P.proj₁ x') (subst (λ x0 → x0 ≡ (+ ℕs n') ℤ* (P.proj₁ x')) Ht₁ (P.proj₂ x'))))
  lin-sem {n} (.(φ₁ and φ₂) , and-isnnf {φ₁} {φ₂} y y') ρ with lin (φ₁ , y) |  lin (φ₂ , y') | lin-sem (φ₁ , y) ρ | lin-sem (φ₂ , y') ρ
  ... | e₁ , H₁ | e₂ , H₂ | P._,_ φ₁-l φ₁-r | P._,_ φ₂-l φ₂-r = P._,_ (λ x → P._,_ (φ₁-l (P.proj₁ x)) (φ₂-l (P.proj₂ x))) (λ x → P._,_ (φ₁-r (P.proj₁ x)) (φ₂-r (P.proj₂ x)))
  lin-sem {n} (.(φ₁ or φ₂) , or-isnnf {φ₁} {φ₂} y y') ρ with lin (φ₁ , y) |  lin (φ₂ , y') | lin-sem (φ₁ , y) ρ | lin-sem (φ₂ , y') ρ
  ... | e₁ , H₁ | e₂ , H₂ | P._,_ φ₁-l φ₁-r | P._,_ φ₂-l φ₂-r = P._,_ ([ (λ x → inj₁ (φ₁-l x)) , (λ x → inj₂ (φ₂-l x)) ]′) ([ (λ x → inj₁ (φ₁-r x)) , (λ x → inj₂ (φ₂-r x)) ]′)