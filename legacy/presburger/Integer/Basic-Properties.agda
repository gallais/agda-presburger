module Integer.Basic-Properties where

open import Relation.Binary.PropositionalEquality
open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_)
open import Data.Sign renaming (+ to S+ ; - to S- ; _*_ to _S*_)
open import Data.Nat.Properties as NatProp
open import Data.Integer.Properties

open import Data.Nat.Divisibility renaming (_∣_ to _ℕdiv_)

open import Data.Product
open import Data.Sign renaming (- to S- ; + to S+)

open import Algebra
open import Algebra.Structures
open import Function

open import Relation.Binary
private module ℕr = IsCommutativeSemiring NatProp.isCommutativeSemiring
private module ℕ* = IsCommutativeMonoid ℕr.*-isCommutativeMonoid


-----
-- ℕ+
-----

abstract
  m+1+n≡1+m+n : ∀ m n → m ℕ+ ℕs n ≡ ℕs (m ℕ+ n)
  m+1+n≡1+m+n m n with m ℕ+ ℕs n | ℕr.+-assoc m 1 n | ℕr.+-comm 1 m
  ... | .(m ℕ+ 1 ℕ+ n) | refl | H = subst (λ x → x ℕ+ n ≡ ℕs (m ℕ+ n)) H refl

  ℕ+-left : ∀ {p q r} → q ≡ r → p ℕ+ q ≡ p ℕ+ r
  ℕ+-left refl = refl

  ℕ+-right : ∀ {p q r} → q ≡ r → q ℕ+ p ≡ r ℕ+ p
  ℕ+-right refl = refl

  ℕ+-≡ : ∀ p q r → p ℕ+ q ≡ p ℕ+ r → q ≡ r
  ℕ+-≡ zero q r H = H
  ℕ+-≡ (ℕs n) q r H = ℕ+-≡ n q r (cong ℕp H)

  ℕ+-ℤ+ : ∀ m n → + (m ℕ+ n) ≡ (+ m) ℤ+ (+ n)
  ℕ+-ℤ+ m n = refl

  ℕ*-ℤ* : ∀ m n → + (m ℕ* n) ≡ (+ m) ℤ* (+ n)
  ℕ*-ℤ* zero n = refl
  ℕ*-ℤ* (ℕs n) zero with n ℕ* 0 | proj₂ ℕr.zero n
  ... | .0 | refl = refl
  ℕ*-ℤ* (ℕs n) (ℕs n') = refl

-----
-- ℕ*
-----

  ℕ*-ℕs-simpl : ∀ m n → m ℕ* (ℕs n) ≡ m ℕ+ (m ℕ* n)
  ℕ*-ℕs-simpl zero n = refl
  ℕ*-ℕs-simpl (ℕs n) n' with ℕ*-ℕs-simpl n n'
  ... | Heq = cong ℕs (subst (λ u → n' ℕ+ u ≡ n ℕ+ ((ℕs n) ℕ* n')) (sym Heq) (subst₂ (λ u v → u ≡ v) (ℕr.+-assoc n' n (n ℕ* n')) (ℕr.+-assoc n n' (n ℕ* n')) (ℕ+-right (ℕr.+-comm n' n))))

-----
-- ⊖
-----

  -⊖-compat : ∀ m n → - (m ⊖ n) ≡ n ⊖ m
  -⊖-compat zero zero = refl
  -⊖-compat zero (ℕs n) = refl
  -⊖-compat (ℕs n) zero = refl
  -⊖-compat (ℕs n) (ℕs n') = -⊖-compat n n'

  n⊖n : ∀ n → n ⊖ n ≡ + 0
  n⊖n zero = refl
  n⊖n (ℕs n) = n⊖n n

  ⊖-opp-simpl : ∀ {m n} → m ⊖ n ≡ + 0 → m ≡ n
  ⊖-opp-simpl {zero} {zero} H = refl
  ⊖-opp-simpl {zero} {ℕs n} ()
  ⊖-opp-simpl {ℕs n} {zero} ()
  ⊖-opp-simpl {ℕs n} {ℕs n'} H = cong ℕs (⊖-opp-simpl H)

-----
-- ℤ≡
-----

  ℤ≡-ext : ∀ {p q} → sign p ≡ sign q → ∣ p ∣ ≡ ∣ q ∣ → p ≡ q
  ℤ≡-ext { -[1+ .n' ]} { -[1+ n' ]} Hsign refl = refl
  ℤ≡-ext { -[1+ n ]} {+ n'} () Habs
  ℤ≡-ext {+ n} { -[1+ n' ]} () Habs
  ℤ≡-ext {+ .n'} {+ n'} Hsign refl = refl

-----
-- ℤ+
-----

  ℤ+-comm : ∀ (p q : ℤ) → p ℤ+ q ≡ q ℤ+ p
  ℤ+-comm -[1+ n ] -[1+ n' ] = cong (λ x → -[1+ ℕs x ]) (ℕr.+-comm n n')
  ℤ+-comm -[1+ n ] (+ zero) = refl
  ℤ+-comm -[1+ n ] (+ ℕs n') = refl
  ℤ+-comm (+ n) -[1+ n' ] = refl
  ℤ+-comm (+ n) (+ n') = cong (λ x → + x) (ℕr.+-comm n n')

  ℤ+-left : ∀ {p q r : ℤ} → q ≡ r → p ℤ+ q ≡ p ℤ+ r
  ℤ+-left {_} {q} {.q} refl = refl

  ℤ+-right : ∀ {p q r : ℤ} → q ≡ r → q ℤ+ p ≡ r ℤ+ p
  ℤ+-right {_} {q} {.q} refl = refl

  ℤ+-zero-l : ∀ p → + 0 ℤ+ p ≡ p
  ℤ+-zero-l -[1+ n ] = refl
  ℤ+-zero-l (+ n) = refl

  ℤ+-zero-r : ∀ p → p ℤ+ + 0 ≡ p
  ℤ+-zero-r -[1+ n ] = refl
  ℤ+-zero-r (+ n) = cong (λ x → + x) ((proj₂ ℕr.+-identity) n)

  ℤ+-opp-l : ∀ p → - p ℤ+ p ≡ + 0
  ℤ+-opp-l -[1+ n ] = n⊖n n
  ℤ+-opp-l (+ zero) = refl
  ℤ+-opp-l (+ ℕs n) = n⊖n n

  ℤ+-opp-r : ∀ p → p ℤ+ - p ≡ + 0
  ℤ+-opp-r p with p ℤ+ - p | ℤ+-comm p (- p)
  ... | .(- p ℤ+ p) | refl = ℤ+-opp-l p

  ℤ+-opp-simpl : ∀ {p₁ p₂} → p₁ ℤ+ - p₂ ≡ + 0 → p₁ ≡ p₂
  ℤ+-opp-simpl { -[1+ n ]} { -[1+ n' ]} H = cong (λ x → -[1+ x ]) (sym (⊖-opp-simpl H))
  ℤ+-opp-simpl { -[1+ n ]} {+ zero} ()
  ℤ+-opp-simpl { -[1+ n ]} {+ ℕs n'} ()
  ℤ+-opp-simpl {+ zero} { -[1+ n' ]} ()
  ℤ+-opp-simpl {+ ℕs n} { -[1+ n' ]} ()
  ℤ+-opp-simpl {+ zero} {+ zero} H = refl
  ℤ+-opp-simpl {+ zero} {+ ℕs n} ()
  ℤ+-opp-simpl {+ ℕs n} {+ zero} ()
  ℤ+-opp-simpl {+ ℕs n} {+ ℕs n'} H =  cong (λ x → + ℕs x) (⊖-opp-simpl H)

-----
-- ℤ-
-----

  -[1+]-elim : ∀ m n → -[1+ m ] ≡ -[1+ n ] → m ≡ n
  -[1+]-elim m .m refl = refl

  unfold-ℤ- : ∀ p q → p ℤ- q ≡ p ℤ+ - q
  unfold-ℤ- -[1+ n ] -[1+ n' ] = refl
  unfold-ℤ- -[1+ n ] (+ zero) = refl
  unfold-ℤ- -[1+ n ] (+ ℕs n') = cong (-[1+_] ∘ ℕs) (ℕr.+-comm n' n)
  unfold-ℤ- (+ n) -[1+ n' ] = cong (λ x → + x) (ℕr.+-comm (ℕs n') n)
  unfold-ℤ- (+ n) (+ zero) = cong (λ x → + x) (sym ((proj₂ ℕr.+-identity) n))
  unfold-ℤ- (+ n) (+ ℕs n') = refl

  opp-invol : ∀ p → - (- p) ≡ p
  opp-invol -[1+ n ] = refl
  opp-invol (+ zero) = refl
  opp-invol (+ ℕs n) = refl

  unfold-opp : ∀ p → - p ≡ -[1+ 0 ] ℤ* p
  unfold-opp -[1+ n ] = cong (λ x → + ℕs x) (sym (proj₂ ℕr.+-identity n))
  unfold-opp (+ zero) = refl
  unfold-opp (+ ℕs n) = cong -[1+_] (sym (proj₂ ℕr.+-identity n))

-----
-- ℤ*
-----

  ℤ*-comm-sign : ∀ x y → sign (x ℤ* y) ≡ sign (y ℤ* x)
  ℤ*-comm-sign (+ zero) q with ∣ q ∣ ℕ* 0 | proj₂ ℕr.zero ∣ q ∣
  ... | .0 | refl = refl
  ℤ*-comm-sign p (+ zero) with ∣ p ∣ ℕ* 0 | proj₂ ℕr.zero ∣ p ∣
  ... | .0 | refl = refl
  ℤ*-comm-sign -[1+ n ] -[1+ n' ] = refl
  ℤ*-comm-sign -[1+ n ] (+ ℕs n') = refl
  ℤ*-comm-sign (+ ℕs n) (-[1+ n' ]) = refl
  ℤ*-comm-sign (+ ℕs n) (+ ℕs n') = refl

  ℤ*-comm-val : ∀ x y → ∣ x ℤ* y ∣ ≡ ∣ y ℤ* x ∣
  ℤ*-comm-val -[1+ n ] -[1+ n' ] = ℕr.*-comm (ℕs n) (ℕs n')
  ℤ*-comm-val -[1+ n ] (+ n') with n' ℕ* ℕs n | ℕr.*-comm n' (ℕs n)
  ... | .(ℕs n ℕ* n') | refl = refl
  ℤ*-comm-val (+ n) -[1+ n' ] with n ℕ* ℕs n' | ℕr.*-comm n (ℕs n')
  ... | .(ℕs n' ℕ* n) | refl = refl
  ℤ*-comm-val (+ n) (+ n') with n ℕ* n' | ℕr.*-comm n n'
  ... | .(n' ℕ* n) | refl = refl

  ℤ*-comm : ∀ x y → x ℤ* y ≡ y ℤ* x
  ℤ*-comm x y = ℤ≡-ext (ℤ*-comm-sign x y) (ℤ*-comm-val x y)

  ℤ*-zero-r : ∀ p → p ℤ* (+ 0) ≡ + 0
  ℤ*-zero-r p with p ℤ* + 0 | ℤ*-comm (+ 0) p
  ... | .(+ 0) | refl = refl

  ℤ*-one-r : ∀ p → p ℤ* + 1 ≡ p
  ℤ*-one-r -[1+ n ] with n ℕ* 1 | proj₂ ℕ*.identity n
  ... | .n | refl = refl
  ℤ*-one-r (+ n) with n ℕ* 1 | proj₂ ℕ*.identity n
  ℤ*-one-r (+ zero) | .0 | refl = refl
  ℤ*-one-r (+ ℕs n) | .(ℕs n) | refl = refl

  ℤ*-one-l : ∀ p → + 1 ℤ* p ≡ p
  ℤ*-one-l p with + 1 ℤ* p | ℤ*-comm (+ 1) p
  ... | .(p ℤ* + 1) | refl = ℤ*-one-r p

-----
-- Distributivity
-----

  -distr-ℤ+ : ∀ p q → - (p ℤ+ q) ≡ - p ℤ+ - q
  -distr-ℤ+ -[1+ n ] -[1+ n' ] = cong (λ x → + ℕs x) (sym (m+1+n≡1+m+n n n'))
  -distr-ℤ+ -[1+ n ] (+ zero) = cong (λ x → + ℕs x) (sym ((proj₂ ℕr.+-identity) n))
  -distr-ℤ+ -[1+ n ] (+ ℕs n') = -⊖-compat n' n
  -distr-ℤ+ (+ zero) -[1+ n' ] = refl
  -distr-ℤ+ (+ ℕs n) -[1+ n' ] = -⊖-compat n n'
  -distr-ℤ+ (+ zero) (+ zero) = refl
  -distr-ℤ+ (+ zero) (+ ℕs n) = refl
  -distr-ℤ+ (+ ℕs n) (+ zero) = cong -[1+_] ((proj₂ ℕr.+-identity) n)
  -distr-ℤ+ (+ ℕs n) (+ ℕs n') = cong -[1+_] (m+1+n≡1+m+n n n')

  -distr-ℤ+' : ∀ p q → - (p ℤ+ q) ≡ - p ℤ- q
  -distr-ℤ+' p q with - p ℤ- q | unfold-ℤ- (- p) q
  ... | .(- p ℤ+ - q) |  refl = -distr-ℤ+ p q

  -distr-ℤ*-l : ∀ p q → - (p ℤ* q) ≡ - p ℤ* q
  -distr-ℤ*-l p (+ zero) with ∣ p ∣ ℕ* 0 | proj₂ (ℕr.zero) ∣ p ∣ | ∣ - p ∣ ℕ* 0 | proj₂ (ℕr.zero) ∣ - p ∣
  ... | .0 | refl | .0 | refl = refl
  -distr-ℤ*-l (+ zero) q = refl
  -distr-ℤ*-l -[1+ n ] -[1+ n' ] = refl
  -distr-ℤ*-l -[1+ n ] (+ ℕs n') = refl
  -distr-ℤ*-l (+ ℕs n) -[1+ n' ] = refl
  -distr-ℤ*-l (+ ℕs n) (+ ℕs n') = refl

  abs-distr-ℤ* : ∀ p q → ∣ p ℤ* q ∣ ≡ ∣ p ∣ ℕ* ∣ q ∣
  abs-distr-ℤ* -[1+ n ] -[1+ n' ] = refl
  abs-distr-ℤ* -[1+ n ] (+ zero) with n ℕ* 0 | proj₂ ℕr.zero n
  ... | .0 | refl = refl
  abs-distr-ℤ* -[1+ n ] (+ ℕs n') = refl
  abs-distr-ℤ* (+ zero) -[1+ n' ] = refl
  abs-distr-ℤ* (+ ℕs n) -[1+ n' ] = refl
  abs-distr-ℤ* (+ zero) (+ n') = refl
  abs-distr-ℤ* (+ ℕs n) (+ zero) with n ℕ* 0 | proj₂ ℕr.zero n
  ... | .0 | refl = refl
  abs-distr-ℤ* (+ ℕs n) (+ ℕs n') = refl

  ℤ*ℤ-equiv : ∀ p q → p ℤ* q ≡ (- p) ℤ* (- q)
  ℤ*ℤ-equiv -[1+ n ] -[1+ n' ] = refl
  ℤ*ℤ-equiv -[1+ zero ] (+ zero) = refl
  ℤ*ℤ-equiv -[1+ ℕs n ] (+ zero) = ℤ*ℤ-equiv -[1+ n ] (+ 0)
  ℤ*ℤ-equiv -[1+ n ] (+ ℕs n') = refl
  ℤ*ℤ-equiv (+ zero) -[1+ n' ] = refl
  ℤ*ℤ-equiv (+ ℕs n) -[1+ n' ] = refl
  ℤ*ℤ-equiv (+ zero) (+ n') = refl
  ℤ*ℤ-equiv (+ ℕs zero) (+ zero) = refl
  ℤ*ℤ-equiv (+ ℕs (ℕs n)) (+ zero) = ℤ*ℤ-equiv (+ ℕs n) (+ 0)
  ℤ*ℤ-equiv (+ ℕs n) (+ ℕs n') = refl

-----
-- ∣_∣
-----

  abs-null-elim : ∀ {p} → ∣ p ∣ ≡ 0 → p ≡ + 0
  abs-null-elim { -[1+ n ]} ()
  abs-null-elim {+ ℕs n} ()
  abs-null-elim {+ 0} _ = refl

  abs-opp-simpl : ∀ p → ∣ - p ∣ ≡ ∣ p ∣
  abs-opp-simpl -[1+ n ] = refl
  abs-opp-simpl (+ zero) = refl
  abs-opp-simpl (+ ℕs n) = refl

-----
-- ℕdiv
-----

  div-elim₁ : ∀ {t u q} → ∣ u ∣ ≡ q ℕ* ∣ t ∣ → u ≡  (sign t S* sign u ◃ q) ℤ* t
  div-elim₁ {t} { -[1+ n ]} {zero} ()
  div-elim₁ {t} {+ .0} {zero} refl = refl
  div-elim₁ { -[1+ n ]} { -[1+ .(n ℕ+ n0 ℕ* ℕs n) ]} {ℕs n0} refl = refl
  div-elim₁ {+ zero} { -[1+ n' ]} {ℕs n0} H with n0 ℕ* 0 | proj₂ ℕr.zero n0
  div-elim₁ {+ zero} { -[1+ n' ]} {ℕs n0} () | .0 | refl
  div-elim₁ {+ ℕs n} { -[1+ .(n ℕ+ n0 ℕ* ℕs n) ]} {ℕs n0} refl = refl
  div-elim₁ { -[1+ n ]} {+ n'} {ℕs n0} H = cong (λ x → + x) H
  div-elim₁ {+ zero} {+ n'} {ℕs n0} H with n0 ℕ* 0 | proj₂ ℕr.zero n0
  ... | .0 | refl = cong (λ x → + x) H
  div-elim₁ {+ ℕs n} {+ n'} {ℕs n0} H = cong (λ x → + x) H

  div-elim : ∀ p q → ∣ p ∣ ℕdiv ∣ q ∣ → Σ ℤ (λ x → q ≡ x ℤ* p)
  div-elim t u (divides q Hq) = ((sign t S* sign u) ◃ q) , div-elim₁ {t} {u} {q} Hq