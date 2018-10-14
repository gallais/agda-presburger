module Cooper where

open import Representation
open import Properties
open import Properties-prop
open import Normalization.Linearisation
open import Normalization.Linearisation-prop
open import Semantics
open import Semantics-prop
-- open import AllmostFree-prop using (lcm-dvd ; dvd-mod)
open import Bset

open import Fin-prop
open import List-tools using (_∈_ ; ∈-ext₁ ; ∈-ext₂ ; b∈[]-elim ; b∈L-elim ; here ; there)

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)

{-
open import Data.Empty
open import Data.Unit
import Data.Product as P
open import Product
open import Data.Sum
open import Data.Vec hiding (_++_ ; [_] ; _∈_) renaming (_∷_ to _●_)
open import Data.List hiding (and ; or)
open import Data.Integer.Divisibility

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary

open import Comparisons using (ℤcompare ; less ; equal ; greater)
open import Decidability using (Fin-dec)
open import Minusinf using (minusinf ; alldvd-and-l ; alldvd-and-r ; alldvd-or-l ; alldvd-or-r ; bound-inf ; cooper₂)

open import Function

open import Algebra.Structures

private module ℤr = IsCommutativeRing IntProp.isCommutativeRing
private module ℤ≤ = DecTotalOrder Int.decTotalOrder

abstract
  neg-proj₁ : ∀ {A : Set} {n} (l₁ l₂ : List A) (P : Fin n → A → Set) → (P.∃ (λ (j : Fin n) → P.∃ (λ b → P.Σ (b ∈ (l₁ ++ l₂)) (λ _ → P j b))) → ⊥) → P.∃ (λ (j : Fin n) → P.∃ (λ b → P.Σ (b ∈ l₁) (λ _ → P j b))) → ⊥
  neg-proj₁ l₁ l₂ P H Hf = H (P._,_ (P.proj₁ Hf) (P._,_ (P.proj₁ (P.proj₂ Hf)) (P._,_ (∈-ext₁ (P.proj₁ (P.proj₂ Hf)) l₁ l₂ ((P.proj₁ ∘ P.proj₂ ∘ P.proj₂) Hf)) ((P.proj₂ ∘ P.proj₂ ∘ P.proj₂) Hf))))

  neg-proj₂ : ∀ {A : Set} {n} (l₁ l₂ : List A) (P : Fin n → A → Set) → (P.∃ (λ (j : Fin n) → P.∃ (λ b → P.Σ (b ∈ (l₁ ++ l₂)) (λ _ → P j b))) → ⊥) → P.∃ (λ (j : Fin n) → P.∃ (λ b → P.Σ (b ∈ l₂) (λ _ → P j b))) → ⊥
  neg-proj₂ l₁ l₂ P H Hf = H (P._,_ (P.proj₁ Hf) (P._,_ (P.proj₁ (P.proj₂ Hf)) (P._,_ (∈-ext₂ (P.proj₁ (P.proj₂ Hf)) l₁ l₂ ((P.proj₁ ∘ P.proj₂ ∘ P.proj₂) Hf)) ((P.proj₂ ∘ P.proj₂ ∘ P.proj₂) Hf))))

  tmp : ∀ {x p} → - x ℤ+ p ≡ + 0 → x ≡ p
  tmp { -[1+ n ]} { -[1+ n' ]} H = cong -[1+_] (⊖-opp-simpl H)
  tmp { -[1+ n ]} {+ n'} ()
  tmp {+ zero} { -[1+ n' ]} ()
  tmp {+ ℕs n} { -[1+ n' ]} ()
  tmp {+ zero} {+ .0} refl = refl
  tmp {+ ℕs n} {+ zero} ()
  tmp {+ ℕs n} {+ ℕs n'} H = cong (λ u → + ℕs u) (sym (⊖-opp-simpl H))

  step-cooper₁ : ∀ {n} (φ : Unf (ℕs n)) (δ : Dall ((proj₁ ∘ minusinf) φ)) (x : ℤ) (ρ : Vec ℤ n) (¬H : (P.∃ (λ (j : Fin (ℕs (δ-extract δ))) → P.∃ (λ b → P.Σ (b ∈ (bset φ)) (λ _ → x ≡ ([| proj₁ b |]e ((+ 0) ● ρ)) ℤ+ (+ toℕ j))))) → ⊥) (Pr : [| proj₁ φ |] (x ● ρ)) → [| proj₁ φ |] ((x ℤ- (+ (δ-extract δ))) ● ρ)
  step-cooper₁ (.T , T-isunitary) δ x ρ ¬H pr = pr
  step-cooper₁ (.F , F-isunitary) δ x ρ ¬H pr = pr
  step-cooper₁ (.(φ₁ and φ₂) , and-isunitary {φ₁} {φ₂} y y') (δ , Hδ) x ρ ¬H (P._,_ pr₁ pr₂) = P._,_ (step-cooper₁ (φ₁ , y) (δ , alldvd-and-l {_} {φ₁ , y} {φ₂ , y'} Hδ) x ρ (neg-proj₁ (bset (φ₁ , y)) (bset (φ₂ , y')) (λ j b → x ≡ [| proj₁ b |]e (+ 0 ● ρ) ℤ+ + toℕ j) ¬H) pr₁) (step-cooper₁ (φ₂ , y') (δ , alldvd-and-r {_} {φ₁ , y} {φ₂ , y'} Hδ) x ρ (neg-proj₂ (bset (φ₁ , y)) (bset (φ₂ , y')) (λ j b → x ≡ [| proj₁ b |]e (+ 0 ● ρ) ℤ+ + toℕ j) ¬H) pr₂)
  step-cooper₁ (.(φ₁ or φ₂) , or-isunitary {φ₁} {φ₂} y y') (δ , Hδ) x ρ ¬H pr = [ inj₁ ∘ (step-cooper₁ (φ₁ , y) (δ , (alldvd-or-l {_} {φ₁ , y} {φ₂ , y'} Hδ)) x ρ (neg-proj₁ (bset (φ₁ , y)) (bset (φ₂ , y')) (λ j b → x ≡ [| proj₁ b |]e (+ 0 ● ρ) ℤ+ + toℕ j) ¬H)) , inj₂ ∘ (step-cooper₁ (φ₂ , y') (δ , (alldvd-or-r {_} {φ₁ , y} {φ₂ , y'} Hδ)) x ρ (neg-proj₂ (bset (φ₁ , y)) (bset (φ₂ , y')) (λ j b → x ≡ [| proj₁ b |]e (+ 0 ● ρ) ℤ+ + toℕ j) ¬H)) ]′ pr
  step-cooper₁ {n} (.(val k le val (+ 0)) , le-isunitary (val-isunit {.(ℕs n)} {k})) δ x ρ ¬H pr = pr
  step-cooper₁ {n} (.(val k eq val (+ 0)) , eq-isunitary (val-isunit {.(ℕs n)} {k})) δ x ρ ¬H pr = pr
  step-cooper₁ {n} (.(not (val k eq val (+ 0))) , neq-isunitary (val-isunit {.(ℕs n)} {k})) δ x ρ ¬H pr = pr
  step-cooper₁ (.(t₁ le val (+ 0)) , le-isunitary {t₁} (varn-isunit y)) δ x ρ ¬H pr = subst (λ u → u ℤ≤ + 0) (context-simpl (t₁ , y) x (x ℤ- (+ δ-extract δ)) ρ) pr
  step-cooper₁ (.(t₁ eq val (+ 0)) , eq-isunitary {t₁} (varn-isunit y)) δ x ρ ¬H pr = subst (λ u → u ≡ + 0) (context-simpl (t₁ , y) x (x ℤ- (+ δ-extract δ)) ρ) pr
  step-cooper₁ (.(not (t₁ eq val (+ 0))) , neq-isunitary {t₁} (varn-isunit y)) δ x ρ ¬H pr =  subst (λ u → ¬ u ≡ + 0) (context-simpl (t₁ , y) x (x ℤ- (+ δ-extract δ)) ρ) pr
  step-cooper₁ {n} (.(((-[1+ 0 ] :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ((δ , neq) , Hδ) x ρ ¬H pr with ℤ≤._≤?_ (- x ℤ+ + ∣ δ ∣ ℤ+ [| t |]e (x ● ρ)) (+ 0)
  ... | yes P = subst₂ (λ u v → u ℤ+ v ℤ≤ + 0) (unfold-opp (x ℤ- + ∣ δ ∣)) (context-simpl (t , y') x (x ℤ- + ∣ δ ∣) ρ) (subst (λ u → - u ℤ+ [| t |]e (x ● ρ) ℤ≤ + 0) (sym (unfold-ℤ- x (+ ∣ δ ∣))) (subst (λ u → u ℤ+ [| t |]e (x ● ρ) ℤ≤ + 0) (sym (-distr-ℤ+ x (- (+ ∣ δ ∣)))) (subst (λ u → - x ℤ+ u ℤ+ [| t |]e (x ● ρ) ℤ≤ + 0) (sym (opp-invol (+ ∣ δ ∣))) P)))
  ... | no ¬P with ¬ℤ≤-is-ℤ> ¬P
  ... | Pr' with elim-bounded (- x ℤ+ ([| t |]e (x ● ρ) ℤ- (+ 1))) ∣ δ ∣ (ℤ≤.trans (subst (λ u → - x ℤ+ ([| t |]e (x ● ρ) ℤ- (+ 1)) ℤ≤ u ℤ+ [| t |]e (x ● ρ)) (unfold-opp x) (ℤ+ℤ≤-l { - x} (-ℤ≤-l ([| t |]e (x ● ρ)) 1))) pr) (ℤp-ℤ≤-compat (ℤ≤.trans Pr' (subst₂ (λ u v → u ℤ≤ v) (sym (ℤr.+-assoc (- x) (+ ∣ δ ∣) ([| t |]e (x ● ρ)))) (ℤr.+-comm (- x ℤ+ ([| t |]e (x ● ρ) ℤ- + 1) ℤ+ + ∣ δ ∣) (+ 1)) (subst (λ u → - x ℤ+ (+ ∣ δ ∣ ℤ+ [| t |]e (x ● ρ)) ℤ≤ u) (sym (ℤr.+-assoc (- x ℤ+ ([| t |]e (x ● ρ) ℤ- + 1)) (+ ∣ δ ∣) (+ 1))) (subst (λ u → - x ℤ+ (+ ∣ δ ∣ ℤ+ [| t |]e (x ● ρ)) ℤ≤ u) (sym (ℤr.+-assoc (- x) ([| t |]e (x ● ρ) ℤ- + 1) ((+ ∣ δ ∣) ℤ+ + 1))) (ℤ+ℤ≤-l { - x} (subst (λ u → + ∣ δ ∣ ℤ+ [| t |]e (x ● ρ) ℤ≤ u ℤ+ + (∣ δ ∣ ℕ+ 1)) (sym (unfold-ℤ- ([| t |]e (x ● ρ)) (+ 1))) (subst₂ (λ u v → u ℤ≤ v) (ℤr.+-comm ([| t |]e (x ● ρ)) (+ ∣ δ ∣)) (sym (ℤr.+-assoc ([| t |]e (x ● ρ)) -[1+ 0 ] ((+ ∣ δ ∣) ℤ+ + 1))) (ℤ+ℤ≤-l {[| t |]e (x ● ρ)} (subst₂ (λ u v → u ℤ≤ v) (P.proj₂ ℤr.+-identity (+ ∣ δ ∣)) (sym (ℤr.+-assoc (+ ∣ δ ∣) (+ 1) -[1+ 0 ])) ℤ≤.refl))))))))))
  ... | P._,_ j Hj with  lin-plus (t , y') (val -[1+ 0 ] , val-islinn-i) | lin-plus-sem (t , y') (val -[1+ 0 ] , val-islinn-i) (+ 0 ● ρ)
  ... | e | Heq = ⊥-elim (¬H (P._,_ j (P._,_ e  (P._,_ here (subst (λ u → x ≡ u ℤ+ + toℕ j) Heq (tmp (subst (λ u → - x ℤ+ (u ℤ+ + toℕ j) ≡ + 0) (unfold-ℤ- ([| t |]e (+ 0 ●  ρ)) (+ 1)) (subst₂ (λ u v → - x ℤ+ (u ℤ- + 1 ℤ+ + toℕ j) ≡ v) (context-simpl (t , y') x (+ 0) ρ) Hj (sym (ℤr.+-assoc (- x) ([| t |]e (x ● ρ) ℤ- + 1) (+ toℕ j)))))))))))
  step-cooper₁ {n} (.(((-[1+ 0 ] :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ((δ , neq) , Hdiv) x ρ H Pr with ∣ δ ∣ | ◃-left-inverse δ
  step-cooper₁ {n} (.(((-[1+ 0 ] :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ((.(+ 0) , neq) , Hdiv) x ρ H Pr | 0 | refl = ⊥-elim (neq refl)
  step-cooper₁ {n} (.(((-[1+ 0 ] :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) ((δ , neq) , Hdiv) x ρ H Pr | ℕs k | Hk with lin-plus (t , y') (val -[1+ 0 ] , val-islinn-i) | lin-plus-sem (t , y') (val -[1+ 0 ] , val-islinn-i) (+ 0 ● ρ)
  ... | e | Heq = ⊥-elim (H (P._,_ (Fs zero) (P._,_ e (P._,_ here (subst (λ u → x ≡ u ℤ+ + 1) Heq (subst (λ u → x ≡ u) (sym (ℤr.+-assoc ([| t |]e (+ 0 ● ρ)) -[1+ 0 ] (+ 1))) (subst (λ u → x ≡ u) (sym (P.proj₂ ℤr.+-identity ([| t |]e (+ 0 ● ρ)))) (tmp (subst₂ (λ u v → u ℤ+ v ≡ + 0) (sym (unfold-opp x)) (context-simpl (t , y') x (+ 0) ρ) Pr)) )))))))
  step-cooper₁ {n} (.(not (((-[1+ 0 ] :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {.n} {t} { -[1+ .0 ]} refl y')) δ x ρ ¬H pr = λ hf → ¬H (P._,_ (fromℕ (δ-extract δ)) (P._,_ (t , y') (P._,_ here (tmp (subst (λ u → - x ℤ+ ([| t |]e (+ 0 ● ρ) ℤ+ + u) ≡ + 0) (sym (toℕ-fromℕ-rev (δ-extract δ))) (subst (λ u → - x ℤ+ u ≡ + 0) (ℤr.+-comm (+ δ-extract δ) ([| t |]e (+ 0 ● ρ))) (subst (λ u → u ≡ + 0) (ℤr.+-assoc (- x) (+ δ-extract δ) ([| t |]e (+ 0 ● ρ))) (subst (λ u → - x ℤ+ u ℤ+ [| t |]e (+ 0 ● ρ) ≡ + 0) (opp-invol (+ δ-extract δ)) (subst (λ u → u ℤ+ [| t |]e (+ 0 ● ρ) ≡ + 0) (-distr-ℤ+ x (- (+ δ-extract δ))) (subst (λ u → - u ℤ+ [| t |]e (+ 0 ● ρ) ≡ + 0) (unfold-ℤ- x (+ δ-extract δ)) (subst₂ (λ u v → u ℤ+ v ≡ + 0) (sym (unfold-opp (x ℤ- + δ-extract δ))) (context-simpl (t , y') (x ℤ- + δ-extract δ) (+ 0) ρ) hf)))))))))))
  step-cooper₁ {n} (.((((+ 1) :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) δ x ρ ¬H pr = ℤ≤.trans (subst₂ (λ u v → u ℤ+ v ℤ≤ (+ 1) ℤ* x ℤ+ [| t |]e (x ● ρ)) (sym (P.proj₁ ℤr.*-identity (x ℤ- (+ δ-extract δ)))) (context-simpl (t , y') x (x ℤ- (+ δ-extract δ)) ρ) (ℤ+ℤ≤-r {[| t |]e (x ● ρ)} (subst (λ u → x ℤ- + δ-extract δ ℤ≤ u) (sym (P.proj₁ ℤr.*-identity x)) (-ℤ≤-l x (δ-extract δ))))) pr
  step-cooper₁ {n} (.((((+ 1) :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) ((δ , neq) , Hδ) x ρ ¬H pr with ∣ δ ∣ | ◃-left-inverse δ
  step-cooper₁ {n} (.((((+ 1) :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) ((.(+ 0) , neq) , Hδ) x ρ ¬H pr | 0 | refl = ⊥-elim (neq refl)
  step-cooper₁ {n} (.((((+ 1) :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) ((δ , neq) , Hδ) x ρ ¬H pr | ℕs k | Hk with lin-plus (lin-opp (t , y')) (val -[1+ 0 ] , val-islinn-i) | lin-opp-sem (t , y') (+ 0 ● ρ) | lin-plus-sem (lin-opp (t , y')) (val -[1+ 0 ] , val-islinn-i) (+ 0 ● ρ)
  ... | e | Heq₁ | Heq₂ = ⊥-elim (¬H (P._,_ (Fs zero) (P._,_ e (P._,_ here (subst (λ u → x ≡ u ℤ+ + 1) Heq₂ (subst (λ u → x ≡ u ℤ+ -[1+ 0 ] ℤ+ + 1) Heq₁ (subst (λ u → x ≡ u) (sym (ℤr.+-assoc (- [| t |]e (+ 0 ● ρ)) -[1+ 0 ] (+ 1))) (subst (λ u → x ≡ u) (sym (P.proj₂ ℤr.+-identity (- [| t |]e (+ 0 ● ρ)))) (sym (tmp (subst (λ u → u ℤ+ x ≡ + 0) (sym (opp-invol ([| t |]e (+ 0 ● ρ)))) (subst (λ u → u ≡ + 0) (ℤr.+-comm x ([| t |]e (+ 0 ● ρ))) (subst₂ (λ u v → u ℤ+ v ≡ + 0) (P.proj₁ ℤr.*-identity x) (context-simpl (t , y') x (+ 0) ρ) pr)))))))))))))
  step-cooper₁ {n} (.(not ((((+ 1) :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {.n} {t} {+ .1} refl y')) δ x ρ ¬H pr with lin-opp (t , y') | lin-opp-sem (t , y') (+ 0 ● ρ)
  ... | e | Heq = λ hf → ¬H (P._,_ (fromℕ (δ-extract δ)) (P._,_ e (P._,_ here (subst₂ (λ u v → x ≡ u ℤ+ + v) Heq (sym (toℕ-fromℕ-rev (δ-extract δ))) (subst₂ (λ u v → x ≡ - u ℤ+ v) (context-simpl (t , y') x (+ 0) ρ) (opp-invol (+ δ-extract δ)) (subst (λ u → x ≡ u) (-distr-ℤ+ ([| t |]e (x ● ρ)) (- (+ δ-extract δ))) (sym (tmp (subst (λ u → u ℤ+ x ≡ + 0) (sym (opp-invol ([| t |]e (x ● ρ) ℤ+ - (+ δ-extract δ)))) (subst (λ u → u ≡ + 0) (sym (ℤr.+-assoc ([| t |]e (x ● ρ)) (- (+ δ-extract δ)) x)) (subst (λ u → u ≡ + 0) (ℤr.+-comm (- (+ δ-extract δ) ℤ+ x) ([| t |]e (x ● ρ))) (subst₂ (λ u v → - (+ δ-extract δ) ℤ+ x ℤ+ u ≡ v) (context-simpl (t , y') (x ℤ- + δ-extract δ) x ρ) hf (ℤ+-right {[| t |]e ((x ℤ- + δ-extract δ) ● ρ)} (subst₂ (λ u v → u ≡ v) (ℤr.+-comm x (- (+ δ-extract δ))) (sym (P.proj₁ ℤr.*-identity (x ℤ- + δ-extract δ))) (sym (unfold-ℤ- x (+ δ-extract δ)))))))))))))))))
  step-cooper₁ (.(k dvd t₁) , dvd-isunitary {k} {t₁} y y') ((δ , neq) , dvd-alldvd y0 y1) x ρ ¬H pr with dvd-mod (t₁ , y') (abs-Notnull (δ , neq)) (k , y) y1 -[1+ 0 ] x ρ
  ... | P._,_ P Q =  subst (λ u → [| k dvd t₁ |] (u ● ρ)) (sym (unfold-ℤ- x (+ ∣ δ ∣))) (subst  (λ u → [| k dvd t₁ |] ((x ℤ+ u) ● ρ)) (sym (unfold-opp (+ ∣ δ ∣))) (P pr))
  step-cooper₁ (.(not (k dvd t₁)) , ndvd-isunitary {k} {t₁} y y') ((δ , neq) , ndvd-alldvd y0 y1) x ρ ¬H pr with dvd-mod (t₁ , y') (abs-Notnull (δ , neq)) (k , y) y1 -[1+ 0 ] x ρ
  ... | P._,_ P Q = λ hf → pr (Q (subst (λ u → [| k dvd t₁ |] (x ℤ+ u ● ρ)) (unfold-opp (+ ∣ δ ∣)) (subst (λ u → [| k dvd t₁ |] (u ● ρ)) (unfold-ℤ- x (+ ∣ δ ∣)) hf)))


  x-decomp-dec₁ : ∀ {m n} (L : List (Lin′ n 1)) (j : Fin m) → ∀ ρ x → Dec (P.∃ (λ b → P.Σ (b ∈ L) (λ _ → x ≡ ([| proj₁ b |]e ρ ℤ+ (+ toℕ j)))))
  x-decomp-dec₁ [] j ρ x = no (λ h → b∈[]-elim (P.proj₁ (P.proj₂ h)))
  x-decomp-dec₁ (x ∷ xs) j ρ x' with x' ℤ≟ ([| proj₁ x |]e ρ ℤ+ + toℕ j) | x-decomp-dec₁ xs j ρ x'
  ... | yes P₁ | _ = yes (P._,_ x (P._,_ here P₁))
  ... | _ | yes P₂ = yes (P._,_ (P.proj₁ P₂) (P._,_ (there ((P.proj₁ ∘ P.proj₂) P₂)) ((P.proj₂ ∘ P.proj₂) P₂)))
  ... | no ¬P₁ | no ¬P₂ = no (λ hf → [ (λ h → ¬P₁ (subst (λ u → x' ≡ [| proj₁ u |]e ρ ℤ+ + toℕ j) h ((P.proj₂ ∘ P.proj₂) hf))) , (λ h → ¬P₂ (P._,_ (P.proj₁ hf) (P._,_ h ((P.proj₂ ∘ P.proj₂) hf)))) ]′ (b∈L-elim (P.proj₁ (P.proj₂ hf))))

  x-decomp-dec : ∀ {m n} (L : List (Lin′ n 1)) → ∀ ρ x → Dec (P.∃ (λ (j : Fin m) → P.∃ (λ b → P.Σ (b ∈ L) (λ _ → x ≡ ([| proj₁ b |]e ρ ℤ+ (+ toℕ j))))))
  x-decomp-dec L ρ x = Fin-dec (λ a → x-decomp-dec₁ L a ρ x)

  cooper₁ : ∀ {n} (φ : Unf (ℕs n)) (δ : Dall (proj₁ (minusinf φ))) → ∀ (ρ : Vec ℤ n) → ((P.∃ (λ (j : Fin (ℕs (δ-extract δ))) → P.∃ (λ b → P.Σ (b ∈ (bset φ)) (λ _ → [| proj₁ φ |] ((([| proj₁ b |]e ((+ 0) ● ρ)) ℤ+ (+ toℕ j)) ● ρ))))) → ⊥) → ∀ x → [| proj₁ φ |] (x ● ρ) → [| proj₁ φ |] ((x ℤ- ((+ δ-extract δ))) ● ρ)
  cooper₁ φ δ ρ ¬H x φx with x-decomp-dec {ℕs ∣ proj₁ (proj₁ δ) ∣} (bset φ) (+ 0 ● ρ) x
  ... | yes (P._,_ j (P._,_ b (P._,_ b∈L Heq))) = ⊥-elim (¬H (P._,_ j (P._,_ b (P._,_ b∈L (subst (λ u → [| proj₁ φ |] (u ● ρ)) Heq φx)))))
  ... | no ¬P = step-cooper₁ φ δ x ρ ¬P φx

  cooper₁-ext : ∀ (k : ℕ) {n} (φ : Unf (ℕs n)) (ρ : Vec ℤ n) → ((P.∃ (λ (j : Fin (jset φ)) → P.∃ (λ b → P.Σ (b ∈ (bset φ)) (λ _ → [| proj₁ φ |] ((([| proj₁ b |]e ((+ 0) ● ρ)) ℤ+ (+ toℕ j)) ● ρ))))) → ⊥) → ∀ x → [| proj₁ φ |] (x ● ρ) → [| proj₁ φ |] ((x ℤ- (+ k ℤ* (+ my-δ φ))) ● ρ)
  cooper₁-ext zero φ ρ _ x φx = subst (λ u → [| proj₁ φ |] (u ● ρ)) (sym (unfold-ℤ- x (+ 0))) (subst (λ u → [| proj₁ φ |] (u ● ρ)) (sym (P.proj₂ ℤr.+-identity x)) φx)
  cooper₁-ext (ℕs k) φ ρ ¬H x φx with cooper₁-ext k φ ρ ¬H x φx
  ... | φxk = subst (λ u → [| proj₁ φ |] (x ℤ- u ● ρ)) (sym (P.proj₂ ℤr.distrib (+ my-δ φ) (+ 1) (+ k))) (subst (λ u → [| proj₁ φ |] (x ℤ- (u ℤ+ ((+ k) ℤ* (+ my-δ φ))) ● ρ)) (sym (P.proj₁ ℤr.*-identity (+ (my-δ φ)))) (subst (λ u → [| proj₁ φ |] (u ● ρ)) (sym (unfold-ℤ- x (+ (my-δ φ) ℤ+ ((+ k) ℤ* + (my-δ φ))))) (subst (λ u → [| proj₁ φ |] ((x ℤ+ - u) ● ρ)) (ℤr.+-comm ((+ k) ℤ* + (my-δ φ)) (+ (my-δ φ))) (subst (λ u → [| proj₁ φ |] ((x ℤ+ u) ● ρ)) (sym (-distr-ℤ+ ((+ k) ℤ* + (my-δ φ)) (+ (my-δ φ)))) (subst (λ u → [| proj₁ φ |] (u ● ρ)) (ℤr.+-assoc x (- ((+ k) ℤ* (+ (my-δ φ)))) (- (+ (my-δ φ)))) (subst (λ u → [| proj₁ φ |] ((u ℤ+ - (+ (my-δ φ))) ● ρ)) (unfold-ℤ- x ((+ k) ℤ* + (my-δ φ))) (subst (λ u → [| proj₁ φ |] (u ● ρ)) (unfold-ℤ- (x ℤ- ((+ k) ℤ* + (my-δ φ))) (+ (my-δ φ))) (cooper₁ φ (lcm-dvd (minusinf φ)) ρ ¬H (x ℤ- ((+ k) ℤ* + (my-δ φ))) φxk))))))))

  cooper₁-simpl : ∀ {n} (φ : Unf (ℕs n)) (ρ : Vec ℤ n) → ((P.∃ (λ (j : Fin (jset φ)) → P.∃ (λ b → P.Σ (b ∈ (bset φ)) (λ _ → [| proj₁ φ |] ((([| proj₁ b |]e ((+ 0) ● ρ)) ℤ+ (+ toℕ j)) ● ρ))))) → ⊥) → ∀ x → [| proj₁ φ |] (x ● ρ) → P.∃ (λ u → [| proj₁ (minusinf φ) |] (u ● ρ))
  cooper₁-simpl φ ρ ¬H x φx with bound-inf φ ρ | ℤcompare x (bound-inf φ ρ) | cooper₂ φ ρ
  cooper₁-simpl φ ρ ¬H x φx | z | less y | H = P._,_ x (P.proj₁ (H x (ℤ≤.trans (nℤ≤sn x) y)) φx)
  cooper₁-simpl φ ρ ¬H .z φx | z | equal refl | H = P._,_ z (P.proj₁ (H z ℤ≤.refl) φx)
  cooper₁-simpl φ ρ ¬H x φx | z | greater y | H with ℤ≤-reachability x z (proj₁ (lcm-dvd (minusinf φ))) (ℤ≤.trans (nℤ≤sn z) y)
  ... | P._,_ k Hk = P._,_ (x ℤ- ((+ k) ℤ* + my-δ φ)) (P.proj₁ (H (x ℤ- ((+ k) ℤ* + my-δ φ)) Hk) (cooper₁-ext k φ ρ ¬H x φx))
-}
