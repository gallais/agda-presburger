module Integer.Elimination where

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_)

open import Integer.Basic-Properties

open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality


import Data.Nat.Properties as NatProp

open import Relation.Binary
open import Algebra.Structures

private module ℕr = IsCommutativeSemiring NatProp.isCommutativeSemiring

abstract
  ℕ+-l-elim : ∀ {m n p} → m ℕ+ n ≡ m ℕ+ p → n ≡ p
  ℕ+-l-elim {zero} H = H
  ℕ+-l-elim {ℕs n} H = ℕ+-l-elim {n} (cong ℕp H)

  ℕ*-l-elim : ∀ {m n p} → (ℕs m) ℕ* n ≡ (ℕs m) ℕ* p → n ≡ p
  ℕ*-l-elim {m} {zero} {zero} H = refl
  ℕ*-l-elim {m} {ℕs n} {zero} H with subst (λ x → ℕs (n ℕ+ m ℕ* ℕs n) ≡ x) (proj₂ ℕr.zero m) H
  ... | ()
  ℕ*-l-elim {m} {zero} {ℕs n'} H with m ℕ* 0 | proj₂ ℕr.zero m
  ℕ*-l-elim {m} {zero} {ℕs n'} () | .0 | refl
  ℕ*-l-elim {m} {ℕs n} {ℕs n'} H with m ℕ* ℕs n | ℕ*-ℕs-simpl m n | m ℕ* ℕs n' | ℕ*-ℕs-simpl m n'
  ... | .(m ℕ+ m ℕ* n) | refl | .(m ℕ+ m ℕ* n') | refl with subst₂ (λ x x' → x ≡ x') (ℕr.+-comm n (m ℕ+ m ℕ* n)) (ℕr.+-comm n' (m ℕ+ m ℕ* n')) (cong ℕp H)
  ... | H' with ℕ+-l-elim {m} (subst₂ (λ x x' → x ≡ x') (ℕr.+-assoc m (m ℕ* n) n) (ℕr.+-assoc m (m ℕ* n') n') H')
  ... | H'' = cong ℕs (ℕ*-l-elim {m} {n} {n'} (subst₂ (λ x x' → x ≡ x') (ℕr.+-comm (m ℕ* n) n) (ℕr.+-comm (m ℕ* n') n') H''))

  ℤ≡-ℕ≡-pos : ∀ {m n} → + m ≡ + n → m ≡ n
  ℤ≡-ℕ≡-pos refl = refl

  ℤ≡-ℕ≡-neg : ∀ {m n} → -[1+ m ] ≡ -[1+ n ] → m ≡ n
  ℤ≡-ℕ≡-neg refl = refl

  ℤ*-l-elim₁ : ∀ {m n p} → (+ ℕs m) ℤ* n ≡ (+ ℕs m) ℤ* p → n ≡ p
  ℤ*-l-elim₁ {m} { -[1+ n ]} { -[1+ n' ]} H with ℕ*-l-elim {m} {ℕs n} {ℕs n'} (cong ℕs (ℤ≡-ℕ≡-neg H))
  ℤ*-l-elim₁ {m} { -[1+ .n' ]} { -[1+ n' ]} H | refl = refl
  ℤ*-l-elim₁ {m} {+ zero} { -[1+ n' ]} H with m ℕ* 0 | proj₂ ℕr.zero m
  ℤ*-l-elim₁ {m} {+ zero} { -[1+ n' ]} () | .0 | refl
  ℤ*-l-elim₁ {m} {+ ℕs n} { -[1+ n' ]} ()
  ℤ*-l-elim₁ {m} { -[1+ n ]} {+ zero} H with m ℕ* 0 | proj₂ ℕr.zero m
  ℤ*-l-elim₁ {m} { -[1+ n ]} {+ zero} () | .0 | refl
  ℤ*-l-elim₁ {m} { -[1+ n ]} {+ ℕs n'} ()
  ℤ*-l-elim₁ {m} {+ zero} {+ zero} H = refl
  ℤ*-l-elim₁ {m} {+ zero} {+ ℕs n} H with m ℕ* 0 | proj₂ ℕr.zero m
  ℤ*-l-elim₁ {m} {+ zero} {+ ℕs n} () | .0 | refl
  ℤ*-l-elim₁ {m} {+ ℕs n} {+ zero} H with m ℕ* 0 | proj₂ ℕr.zero m
  ℤ*-l-elim₁ {m} {+ ℕs n} {+ zero} () | .0 | refl
  ℤ*-l-elim₁ {m} {+ ℕs n} {+ ℕs n'} H = cong (λ x → + x) (ℕ*-l-elim {m} (ℤ≡-ℕ≡-pos H))

  ℤ-ℤ* : ∀ m n → - (-[1+ m ] ℤ* n) ≡ + ℕs m ℤ* n
  ℤ-ℤ* m -[1+ n ] = refl
  ℤ-ℤ* m (+ zero) with m ℕ* 0 | proj₂ ℕr.zero m
  ... | .0 | refl = refl
  ℤ-ℤ* m (+ ℕs n) = refl

  ℤ--elim : ∀ {m n} → m ≡ n → - m ≡ - n
  ℤ--elim refl = refl

  ℤ*-l-elim₂ : ∀ {m n p} → -[1+ m ] ℤ* n ≡ -[1+ m ] ℤ* p → n ≡ p
  ℤ*-l-elim₂ {m} {n} {p} H with subst₂ (λ x x' → x ≡ x') (ℤ-ℤ* m n) (ℤ-ℤ* m p) (ℤ--elim H)
  ... | H' = ℤ*-l-elim₁ {m} H'

  ℤ*-l-elim : ∀ {m n p} → m ℤ* n ≡ m ℤ* p → (m ≡ + 0 → ⊥) → n ≡ p
  ℤ*-l-elim { -[1+ m ]} H m-neq = ℤ*-l-elim₂ {m} H
  ℤ*-l-elim {+ zero} H m-neq = ⊥-elim (m-neq refl)
  ℤ*-l-elim {+ ℕs m} H m-neq = ℤ*-l-elim₁ {m} H