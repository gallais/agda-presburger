module Normalization.Unitarization-prop where

-- Things specific to the solver
open import Representation
open import Properties
open import Semantics
open import Semantics-prop
open import Normalization.Linearisation
open import Normalization.Linearisation-prop
open import Normalization.Unitarization
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
  unit-exp-sem₁₁ : ∀ {n n'} → ℕs n ≡ n' ℕ* 0 → ⊥
  unit-exp-sem₁₁ {n} {zero} ()
  unit-exp-sem₁₁ {n} {ℕs n'} H = unit-exp-sem₁₁ {n} {n'} H

  unit-exp-sem₁ : ∀ {k q σ} → ∣ σ ∣ ≡ q ℕ* ∣ k ∣ → (+ q) ℤ* k ≡ ((sign k S* sign σ) ◃ 1) ℤ* σ
  unit-exp-sem₁ {k} {zero} { -[1+ n ]} ()
  unit-exp-sem₁ {k} {zero} {+ 0} refl = sym (ℤ*-zero-r ((sign k S* S+) ◃ 1))
  unit-exp-sem₁ {k} {zero} {+ (ℕs n)} ()
  unit-exp-sem₁ { -[1+ n ]} {ℕs n'} { -[1+ .(n ℕ+ n' ℕ* ℕs n) ]} refl = cong -[1+_] (sym (P.proj₁ (ℕr.*-identity) (n ℕ+ n' ℕ* ℕs n)))
  unit-exp-sem₁ { -[1+ n ]} {ℕs n'} {+ .(ℕs (n ℕ+ n' ℕ* ℕs n))} refl = cong -[1+_] (sym (P.proj₁ (ℕr.*-identity) (n ℕ+ n' ℕ* ℕs n)))
  unit-exp-sem₁ {+ zero} {ℕs n'} { -[1+ n0 ]} H = ⊥-elim (unit-exp-sem₁₁ {n0} {n'} H)
  unit-exp-sem₁ {+ ℕs n} {ℕs n'} { -[1+ .(n ℕ+ n' ℕ* ℕs n) ]} refl = cong (λ x → + ℕs x) (sym (P.proj₁ (ℕr.*-identity) (n ℕ+ n' ℕ* ℕs n)))
  unit-exp-sem₁ {+ zero} {ℕs zero} {+ .0} refl = refl
  unit-exp-sem₁ {+ zero} {ℕs (ℕs n)} {+ .(n ℕ* 0)} refl = unit-exp-sem₁ {+ zero} {ℕs n} {+ (n ℕ* 0)} refl
  unit-exp-sem₁ {+ ℕs n} {ℕs n'} {+ .(ℕs (n ℕ+ n' ℕ* ℕs n))} refl = cong (λ x → + ℕs x) (sym (P.proj₁ (ℕr.*-identity) (n ℕ+ n' ℕ* ℕs n)))

  unit-exp-sem : ∀ {n p} → (e : Lin′ (ℕs n) p) → (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ → my-k e σ Hdiv ℤ* [| proj₁ e |]e (x ∷ ρ) ≡ [| proj₁ (unit-exp e σ Hdiv) |]e ((proj₁ σ ℤ* x) ∷ ρ)
  unit-exp-sem {n} (.(val k) , val-islinn-i) σ (val-div-exp {.(ℕs n)} {k}) x ρ = ℤ*-one-l k
  unit-exp-sem {n} {p} (.(val k) , val-islinn-i {.p} {k}) σ (varn-div-exp y) x ρ = ℤ*-one-l k
  unit-exp-sem {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.p} {k} {p'} {r} y y' y0) σ (varn-div-exp y1) x ρ = subst₂ (λ x' x0 → x' ≡ x0) (sym (ℤ*-one-l ([| (k :* var p') :+ r |]e (x ∷ ρ)))) (context-simpl (proj₁ (unit-exp ((k :* var p') :+ r , var-islinn-i y y' y0) σ (varn-div-exp y1)) , y1) x (proj₁ σ ℤ* x) ρ) refl
  unit-exp-sem {n} (.((k :* var zero) :+ t) , var-islinn-i y y' y0) (σ , notnull) (var0-div-exp {.n} {.(σ , notnull)} {t} {k} (divides q H) y1) x ρ with lin-mult (+ q) (t , y1) | lin-mult-sem (+ q) (t , y1)
  ... | e' , He' | Heq = subst₂ (λ x' x0 → x' ≡ (((sign k S* sign σ) ◃ 1) ℤ* (σ ℤ* x)) ℤ+ x0) (sym ((P.proj₁ ℤr.distrib) (+ q) (k ℤ* x) ([| t |]e (x ∷ ρ)))) (context-simpl (e' , He') x (σ ℤ* x) ρ) (subst₂ (λ x' x0 → x' ℤ+ x0 ≡ (((sign k S* sign σ) ◃ 1) ℤ* (σ ℤ* x)) ℤ+ [| e' |]e (x ∷ ρ)) (ℤr.*-assoc (+ q) k x) (sym (Heq (x ∷  ρ))) (ℤ+-right  {[| e' |]e (x ∷ ρ)} {(+ q) ℤ* k ℤ* x} {((sign k S* sign σ) ◃ 1) ℤ* (σ ℤ* x)} (subst (λ x' → (+ q) ℤ* k ℤ* x ≡ x') (ℤr.*-assoc ((sign k S* sign σ) ◃ 1) σ x) (subst (λ x' → (+ q) ℤ* k ℤ* x ≡ x' ℤ* x) (unit-exp-sem₁ {k} {q} {σ} H) refl))))

  unit-exp-sem′ : ∀ {n p} → (e : Lin′ n (ℕs p))  (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ ρ → (my-k e σ Hdiv) ℤ* [| proj₁ e |]e ρ ≡ [| proj₁ (unit-exp e σ Hdiv) |]e ρ
  unit-exp-sem′ {n} (.(val k) , val-islinn-i) σ (val-div-exp {.n} {k}) ρ = P.proj₁ ℤr.*-identity k
  unit-exp-sem′ {n} {p} (.(val k) , val-islinn-i {.(ℕs p)} {k}) σ (varn-div-exp y) ρ = P.proj₁ ℤr.*-identity k
  unit-exp-sem′ {n} {p} (.((k :* var p') :+ r) , var-islinn-i {.(ℕs p)} {k} {p'} {r} y y' y0) σ (varn-div-exp y1) ρ = P.proj₁ ℤr.*-identity ((k ℤ* [| var p' |]e ρ) ℤ+ [| r |]e ρ)
  unit-exp-sem′ (.((k :* var zero) :+ t) , var-islinn-i y () y0) σ (var0-div-exp {n} {.σ} {t} {k} y1 y2) ρ

  unit-exp-eq-sem₁ : ∀ {n p} (e : Lin′ (ℕs n) p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ → [| (proj₁ e) eq (val (+ 0)) |] (x ∷ ρ) → my-k e σ Hdiv ℤ* [| proj₁ e |]e (x ∷ ρ) ≡ + 0
  unit-exp-eq-sem₁ (.(val (+ 0)) , He) σ val-div-exp x ρ refl = refl
  unit-exp-eq-sem₁ (e , He) σ (varn-div-exp y) x ρ H = subst (λ x' → x' ≡ + 0) (sym (ℤ*-one-l ([| e |]e (x ∷ ρ)))) H
  unit-exp-eq-sem₁ {n} (.((k :* var zero) :+ t) , He) (σ , notnull) (var0-div-exp {.n} {.(σ , notnull)} {t} {k} (divides q Heq) y') x ρ H = subst (λ x' → (+ q) ℤ* x' ≡ + 0) (sym H) (ℤ*-zero-r (+ q))

  unit-exp-eq-sem₂ : ∀ {n p} (e : Lin′ (ℕs n) p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ → my-k e σ Hdiv ℤ* [| proj₁ e |]e (x ∷ ρ) ≡ + 0 → [| (proj₁ e) eq (val (+ 0)) |] (x ∷ ρ)
  unit-exp-eq-sem₂ {n} (.(val k) , He) σ (val-div-exp {.(ℕs n)} {k}) x ρ H = subst (λ x' → x' ≡ + 0) (ℤ*-one-l k) H
  unit-exp-eq-sem₂ (e , He) σ (varn-div-exp y) x ρ H = subst (λ x' → x' ≡ + 0) (ℤ*-one-l ([| e |]e (x ∷ ρ))) H
  unit-exp-eq-sem₂ {n} (.((k :* var zero) :+ t) , He) (σ , notnull) (var0-div-exp {.n} {.(σ , notnull)} {t} {k} (divides zero Hq) y') x ρ H = ⊥-elim (notnull (abs-null-elim Hq))
  unit-exp-eq-sem₂ {n} (.((k :* var zero) :+ t) , He) (σ , notnull) (var0-div-exp {.n} {.(σ , notnull)} {t} {k} (divides (ℕs n') Hq) y') x ρ H = integrity {+ ℕs n'} H (λ ())

  unit-exp-eq-sem : ∀ {n p} (e : Lin′ (ℕs n) p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ → [| (proj₁ e) eq (val (+ 0)) |] (x ∷ ρ) ↔ [| (proj₁ (unit-exp e σ Hdiv)) eq (val (+ 0)) |] ((proj₁ σ ℤ* x) ∷ ρ)
  unit-exp-eq-sem (e , He) σ Hdiv x ρ = subst (λ x' → [| e eq (val (+ 0)) |] (x ∷ ρ) ↔ x' ≡ + 0) (unit-exp-sem (e , He) σ Hdiv x ρ) (P._,_ (unit-exp-eq-sem₁ (e , He) σ Hdiv x ρ) (unit-exp-eq-sem₂ (e , He) σ Hdiv x ρ))

  unit-exp-le-sem₁ : ∀ {n p} (e : Lin′ (ℕs n) p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ → [| (proj₁ e) le (val (+ 0)) |] (x ∷ ρ) → my-k e σ Hdiv ℤ* [| proj₁ e |]e (x ∷ ρ) ℤ≤ + 0
  unit-exp-le-sem₁ {n} (.(val k) , He) σ (val-div-exp {.(ℕs n)} {k}) x ρ H = subst (λ x' → x' ℤ≤ + 0) (sym (ℤ*-one-l k)) H
  unit-exp-le-sem₁ (e , He) σ (varn-div-exp y) x ρ H = subst (λ x' → x' ℤ≤ + 0) (sym (ℤ*-one-l _)) H
  unit-exp-le-sem₁ {n} (.((k :* var zero) :+ t) , var-islinn-i y y' y0) σ (var0-div-exp {.n} {.σ} {t} {k} (divides q Hq) y2) x ρ H = ℤ≤.trans (ℤ*ℤ≤-l (+≤+ {0} {q} z≤n) H) (subst (λ x' → x' ℤ≤ + 0) (sym (ℤ*-zero-r (+ q))) (+≤+ z≤n))

  unit-exp-le-sem₂ : ∀ {n p} (e : Lin′ (ℕs n) p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ → my-k e σ Hdiv ℤ* [| proj₁ e |]e (x ∷ ρ) ℤ≤ + 0 → [| (proj₁ e) le (val (+ 0)) |] (x ∷ ρ)
  unit-exp-le-sem₂ {n} (.(val k) , He) σ (val-div-exp {.(ℕs n)} {k}) x ρ H = subst (λ x' → x' ℤ≤ + 0) (ℤ*-one-l k) H
  unit-exp-le-sem₂ (e , He) σ (varn-div-exp y) x ρ H = subst (λ x' → x' ℤ≤ + 0) (ℤ*-one-l ([| e |]e (x ∷ ρ))) H
  unit-exp-le-sem₂ {n} (.((k :* var zero) :+ t) , var-islinn-i y y' y0) (σ , notnull) (var0-div-exp {.n} {.(σ , notnull)} {t} {k} (divides zero Hq) y2) x ρ H = ⊥-elim (notnull (abs-null-elim Hq))
  unit-exp-le-sem₂ {n} (.((k :* var zero) :+ t) , var-islinn-i y y' y0) (σ , notnull) (var0-div-exp {.n} {.(σ , notnull)} {t} {k} (divides (ℕs n') Hq) y2) x ρ H = ℤ*ℤ≤-l-elim {n'} (ℤ≤.trans H (subst (λ u → + 0 ℤ≤ u) (sym (P.proj₂ ℤr.zero (+ ℕs n'))) ℤ≤.refl)) 

  unit-exp-le-sem : ∀ {n p} (e : Lin′ (ℕs n) p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ → [| (proj₁ e) le (val (+ 0)) |] (x ∷ ρ) ↔ [| (proj₁ (unit-exp e σ Hdiv)) le (val (+ 0)) |] ((proj₁ σ ℤ* x) ∷ ρ)
  unit-exp-le-sem (e , He) σ Hdiv x ρ = subst (λ x' → [| e le val (+ 0) |] (x ∷ ρ) ↔ x' ℤ≤ + 0) (unit-exp-sem (e , He) σ Hdiv x ρ) (P._,_ (unit-exp-le-sem₁ (e , He) σ Hdiv x ρ) (unit-exp-le-sem₂ (e , He) σ Hdiv x ρ))

  unit-exp-dvd-sem₁ : ∀ {n p} (e : Lin′ (ℕs n) p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ k → (k ≡ + 0 → ⊥)→ [| k dvd (proj₁ e) |] (x ∷ ρ) → [| ((my-k e σ Hdiv) ℤ* k) dvd (proj₁ (unit-exp e σ Hdiv)) |] ((proj₁ σ ℤ* x) ∷ ρ)
  unit-exp-dvd-sem₁ (e , He) σ Hdiv x ρ k kneq (P._,_ l Hl) = P._,_ l (subst (λ x' → x' ≡ (my-k (e , He) σ Hdiv) ℤ* k ℤ* l) (unit-exp-sem (e , He) σ Hdiv x ρ) (subst₂ (λ x' x0 → (my-k (e , He) σ Hdiv) ℤ* x' ≡ x0) (sym Hl) (sym (ℤr.*-assoc (my-k (e , He) σ Hdiv) k l)) refl))

  unit-exp-dvd-sem₂ : ∀ {n p} (e : Lin′ (ℕs n) p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ k → (k ≡ + 0 → ⊥)→ [| k dvd (proj₁ e) |] (x ∷ ρ) ← [| ((my-k e σ Hdiv) ℤ* k) dvd (proj₁ (unit-exp e σ Hdiv)) |] ((proj₁ σ ℤ* x) ∷ ρ)
  unit-exp-dvd-sem₂ (e , He) σ Hdiv x ρ k kneq (P._,_ l Hl) = P._,_ l (ℤ*-l-elim {my-k (e , He) σ Hdiv} (subst₂ (λ x' x0 → x' ≡ x0) (sym (unit-exp-sem (e , He) σ Hdiv x ρ)) (ℤr.*-assoc (my-k (e , He) σ Hdiv) k l) Hl) (my-k-neq (e , He) σ Hdiv))

  unit-exp-dvd-sem : ∀ {n p} (e : Lin′ (ℕs n) p) (σ : Notnull) (Hdiv : div-exp σ (proj₁ e)) → ∀ x ρ k → (k ≡ + 0 → ⊥)→ [| k dvd (proj₁ e) |] (x ∷ ρ) ↔ [| ((my-k e σ Hdiv) ℤ* k) dvd (proj₁ (unit-exp e σ Hdiv)) |] ((proj₁ σ ℤ* x) ∷ ρ)
  unit-exp-dvd-sem (e , He) σ Hdiv x ρ k kneq = P._,_ (unit-exp-dvd-sem₁ (e , He) σ Hdiv x ρ k kneq) (unit-exp-dvd-sem₂ (e , He) σ Hdiv x ρ k kneq)

  unitarise-aux-sem : ∀ {n} → (φ : Lin (ℕs n)) (σ : Notnull) (Hdiv : divall σ (proj₁ φ)) → ∀ x ρ → [| proj₁ φ |] (x ∷ ρ) ↔ [| proj₁ (unitarise-aux φ σ Hdiv) |] ((proj₁ σ ℤ* x) ∷ ρ)
  unitarise-aux-sem (.T , Hφ) σ T-divall x ρ = P._,_ id id
  unitarise-aux-sem (.F , Hφ) σ F-divall x ρ = P._,_ id id
  unitarise-aux-sem (.(t₁ le val (+ 0)) , le-islin y) σ (le-divall {t₁} y') x ρ with unit-exp (t₁ , y) σ y' | unit-exp-le-sem (t₁ , y) σ y' x ρ
  ... | e' , He' | H = H
  unitarise-aux-sem (.(t₁ eq val (+ 0)) , eq-islin y) σ (eq-divall {t₁} y') x ρ with unit-exp (t₁ , y) σ y' | unit-exp-eq-sem (t₁ , y) σ y' x ρ
  ... | e' , He' | H = H
  unitarise-aux-sem (.(not (t₁ eq val (+ 0))) , neq-islin y) σ (neq-divall {t₁} y') x ρ with unit-exp (t₁ , y) σ y' | unit-exp-eq-sem (t₁ , y) σ y' x ρ
  ... | e' , He' | P._,_ H₁ H₂ = P._,_ (λ hf t → hf (H₂ t)) (λ hf t → hf (H₁ t))
  unitarise-aux-sem (.(k dvd t₁) , dvd-islin y y') σ (dvd-divall {k} {t₁} y0 y1) x ρ with unit-exp (t₁ , y') σ y1 | unit-exp-dvd-sem (t₁ , y') σ y1 x ρ k y0
  ... | e' , He' | H = H
  unitarise-aux-sem (.(not (k dvd t₁)) , ndvd-islin y y') σ (ndvd-divall {k} {t₁} y0 y1) x ρ with unit-exp (t₁ , y') σ y1 | unit-exp-dvd-sem (t₁ , y') σ y1 x ρ k y0
  ... | e' , He' | P._,_ H₁ H₂ = P._,_ (λ hf t → hf (H₂ t)) (λ hf t → hf (H₁ t))
  unitarise-aux-sem (.(φ₁ and φ₂) , and-islin y y') σ (and-divall {φ₁} {φ₂} y0 y1) x ρ with unitarise-aux-sem (φ₁ , y) σ y0 x ρ | unitarise-aux-sem (φ₂ , y') σ y1 x ρ
  ... | Heq₁ | Heq₂ with unitarise-aux (φ₁ , y) σ y0 | unitarise-aux (φ₂ , y') σ y1
  ... | ψ₁ , H₁ | ψ₂ , H₂ = P._,_ (λ x' → P._,_ (P.proj₁ Heq₁ (P.proj₁ x')) (P.proj₁ Heq₂ (P.proj₂ x'))) (λ x' → P._,_ (P.proj₂ Heq₁ (P.proj₁ x')) (P.proj₂ Heq₂ (P.proj₂ x')))
  unitarise-aux-sem (.(φ₁ or φ₂) , or-islin y y') σ (or-divall {φ₁} {φ₂} y0 y1) x ρ with unitarise-aux-sem (φ₁ , y) σ y0 x ρ | unitarise-aux-sem (φ₂ , y') σ y1 x ρ
  ... | Heq₁ | Heq₂ with unitarise-aux (φ₁ , y) σ y0 | unitarise-aux (φ₂ , y') σ y1
  ... | ψ₁ , H₁ | ψ₂ , H₂ = P._,_ [ (λ x' → inj₁ (P.proj₁ Heq₁ x')) , (λ x' → inj₂ (P.proj₁ Heq₂ x')) ]′ [ (λ x' → inj₁ (P.proj₂ Heq₁ x')) , (λ x' → inj₂ (P.proj₂ Heq₂ x')) ]′

  unitarise-sem : ∀ {n} → (φ : Lin (ℕs n)) → ∀ ρ → P.∃ (λ x → [| proj₁ φ |] (x ∷ ρ)) ↔ P.∃ (λ x → [| (((proj₁ ∘ P.proj₁ ∘ lcmφ) φ) dvd (var zero)) and ((proj₁ ∘ unitarise) φ) |] (x ∷ ρ))
  unitarise-sem φ ρ with lcmφ φ
  ... | P._,_ σ Hdiv with unitarise-aux-sem φ σ Hdiv
  ... | Hyp = P._,_ (λ h → P._,_ ((proj₁ σ) ℤ* (P.proj₁ h)) (P._,_ (P._,_ (P.proj₁ h) refl) (P.proj₁ (Hyp (P.proj₁ h) ρ) (P.proj₂ h)))) (λ h → P._,_ ((P.proj₁ ∘ P.proj₁ ∘ P.proj₂) h) (P.proj₂ (Hyp ((P.proj₁ ∘ P.proj₁ ∘ P.proj₂) h) ρ) (subst (λ u → [| proj₁ (unitarise-aux φ σ Hdiv) |] (u ∷ ρ)) ((P.proj₂ ∘ P.proj₁ ∘ P.proj₂) h) ((P.proj₂ ∘ P.proj₂) h))))