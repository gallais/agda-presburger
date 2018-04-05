{-# OPTIONS --termination-depth=2 #-}

module Integer.Order-Properties where

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

open import Data.Sign renaming (- to S- ; + to S+ ; _*_ to _S*_)

open import Data.Empty
open import Data.Product

import Product as P
open import Comparisons
open import Properties
open import Integer.Basic-Properties

open import Relation.Binary.PropositionalEquality

open import Algebra.Structures
import Data.Nat.Properties as NatProp
import Integer.Structures as IntProp

open import Relation.Binary
private module ℕr = IsCommutativeSemiring NatProp.isCommutativeSemiring
private module ℤr = IsCommutativeRing IntProp.isCommutativeRing
private module ℕ≤ = DecTotalOrder Nat.decTotalOrder
private module ℤ≤ = DecTotalOrder Int.decTotalOrder
private module ℕ⊔⊓ = IsDistributiveLattice NatProp.isDistributiveLattice

abstract

-----
-- ℕ≤ basic properties
-----

  ℕ<-irrefl : ∀ n → ℕs n ℕ≤ n → ⊥
  ℕ<-irrefl zero ()
  ℕ<-irrefl (ℕs n) (s≤s m≤n) = ℕ<-irrefl n m≤n 

  nℕ≤sn : ∀ n → n ℕ≤ ℕs n
  nℕ≤sn zero = z≤n
  nℕ≤sn (ℕs n) = s≤s (nℕ≤sn n)

-----
-- ℕ≤ & ℤ≤ relation
-----

  ℕ≤-ℤ≤-inj₁ : ∀ (p q : ℕ) → p ℕ≤ q → p ⊖ q ℤ≤ + 0
  ℕ≤-ℤ≤-inj₁ .0 zero z≤n = +≤+ z≤n
  ℕ≤-ℤ≤-inj₁ .0 (ℕs n) z≤n = -≤+
  ℕ≤-ℤ≤-inj₁ .(ℕs m) .(ℕs n) (s≤s {m} {n} m≤n) = ℕ≤-ℤ≤-inj₁ m n m≤n

  ℤ≤-ℕ≤-inj₁ : ∀ (p q : ℕ) → p ⊖ q ℤ≤ + 0 → p ℕ≤ q
  ℤ≤-ℕ≤-inj₁  p zero (+≤+ m≤n) = m≤n
  ℤ≤-ℕ≤-inj₁  zero (ℕs n) H = z≤n
  ℤ≤-ℕ≤-inj₁  (ℕs n) (ℕs n') H = s≤s (ℤ≤-ℕ≤-inj₁ n n' H)

-----
-- Basic Properties
-----

  ℤs-ℤp-inv : ∀ p → ℤs (ℤp p) ≡ p
  ℤs-ℤp-inv p = subst (λ u → + 1 ℤ+ u ≡ p) (sym (unfold-ℤ- p (+ 1))) (subst (λ u → + 1 ℤ+ u ≡ p) (ℤr.+-comm -[1+ 0 ] p) (subst (λ u → u ≡ p) (ℤr.+-assoc (+ 1) -[1+ 0 ] p) (proj₁ ℤr.+-identity p)))

  ℤp-ℤ≤-compat : ∀ {p q : ℤ} → ℤs p ℤ≤ ℤs q → p ℤ≤ q
  ℤp-ℤ≤-compat { -[1+ zero ]} { -[1+ zero ]} H = -≤- z≤n
  ℤp-ℤ≤-compat { -[1+ zero ]} { -[1+ ℕs n ]} ()
  ℤp-ℤ≤-compat { -[1+ ℕs n ]} { -[1+ zero ]} H = -≤- z≤n
  ℤp-ℤ≤-compat { -[1+ ℕs n ]} { -[1+ ℕs n' ]} (-≤- n≤m) = -≤- (s≤s n≤m)
  ℤp-ℤ≤-compat {+ n} { -[1+ zero ]} (+≤+ ())
  ℤp-ℤ≤-compat {+ n} { -[1+ ℕs n' ]} ()
  ℤp-ℤ≤-compat { -[1+ n ]} {+ n'} H = -≤+
  ℤp-ℤ≤-compat {+ n} {+ n'} (+≤+ (s≤s m≤n)) = +≤+ m≤n

  ℤs-ℤ≤-compat : ∀ {p q : ℤ} → p ℤ≤ q → ℤs p ℤ≤ ℤs q
  ℤs-ℤ≤-compat { -[1+ zero ]} { -[1+ .0 ]} (-≤- z≤n) = ℤ≤.refl
  ℤs-ℤ≤-compat { -[1+ ℕs n ]} { -[1+ .0 ]} (-≤- z≤n) = -≤+
  ℤs-ℤ≤-compat { -[1+ ℕs n ]} { -[1+ ℕs m ]} (-≤- (s≤s m≤n)) = -≤- m≤n
  ℤs-ℤ≤-compat { -[1+ zero ]} {+ n'} -≤+ = +≤+ z≤n
  ℤs-ℤ≤-compat { -[1+ ℕs n ]} {+ n'} -≤+ = -≤+
  ℤs-ℤ≤-compat {+ n} { -[1+ n' ]} ()
  ℤs-ℤ≤-compat {+ n} {+ n'} (+≤+ m≤n) = +≤+ (s≤s m≤n)

  ℤs-ℤ≤-compat′ : ∀ {p q : ℤ} → ℤp p ℤ≤ ℤp q → p ℤ≤ q
  ℤs-ℤ≤-compat′ {p} {q} H = subst₂ (λ u v → u ℤ≤ v) (ℤs-ℤp-inv p) (ℤs-ℤp-inv q) (ℤs-ℤ≤-compat H)

  ℤ<-irrefl : ∀ p → + 1 ℤ+ p ℤ≤ p → ⊥
  ℤ<-irrefl -[1+ zero ] ()
  ℤ<-irrefl -[1+ ℕs n ] (-≤- n≤m) = ℕ<-irrefl n n≤m
  ℤ<-irrefl (+ n) (+≤+ m≤n) = ℕ<-irrefl n m≤n

  ℤ<-irrefl' : ∀ p →  p ℤ≤ -[1+ 0 ] ℤ+ p → ⊥
  ℤ<-irrefl' -[1+ n ] (-≤- n≤m) = ℕ<-irrefl n n≤m
  ℤ<-irrefl' (+ zero) ()
  ℤ<-irrefl' (+ ℕs n) (+≤+ m≤n) = ℕ<-irrefl n m≤n

  nℤ≤sn : ∀ n → n ℤ≤ ℤs n
  nℤ≤sn -[1+ zero ] = -≤+
  nℤ≤sn -[1+ ℕs n ] = -≤- (nℕ≤sn n)
  nℤ≤sn (+ n) = +≤+ (nℕ≤sn n)

-----
-- Transformations
-----
 
  ℤ≤-simpl₁ : ∀ (p q : ℤ) → p ℤ≤ q → p ℤ+ - q ℤ≤ + 0
  ℤ≤-simpl₁ .(-[1+ m ]) .(+ 0) (-≤+ {m} {zero}) = -≤+
  ℤ≤-simpl₁ .(-[1+ m ]) .(+ ℕs n) (-≤+ {m} {ℕs n}) = -≤+
  ℤ≤-simpl₁ .(-[1+ m ]) .(-[1+ n ]) (-≤- {m} {n} n≤m) = ℕ≤-ℤ≤-inj₁ n m n≤m
  ℤ≤-simpl₁ .(+ 0) .(+ 0) (+≤+ {.0} {zero} z≤n) = +≤+ z≤n
  ℤ≤-simpl₁ .(+ 0) .(+ ℕs n) (+≤+ {.0} {ℕs n} z≤n) = -≤+
  ℤ≤-simpl₁ .(+ ℕs m) .(+ ℕs n) (+≤+ (s≤s {m} {n} m≤n)) = ℕ≤-ℤ≤-inj₁ m n m≤n 

  ℤ≤-simpl₁' : ∀ (p q : ℤ) → q ℤ≤ p → + 0 ℤ≤ p ℤ+ - q
  ℤ≤-simpl₁' .(+ n) .(-[1+ m ]) (-≤+ {m} {n}) = +≤+ z≤n
  ℤ≤-simpl₁' .(-[1+ 0 ]) .(-[1+ m ]) (-≤- {m} {zero} n≤m) = +≤+ z≤n
  ℤ≤-simpl₁' .(-[1+ ℕs n ]) .(-[1+ 0 ]) (-≤- {zero} {ℕs n} ())
  ℤ≤-simpl₁' .(-[1+ ℕs n' ]) .(-[1+ ℕs n ]) (-≤- {ℕs n} {ℕs n'} (s≤s m≤n)) = ℤ≤-simpl₁' (-[1+ n' ]) (-[1+ n ]) (-≤- m≤n)
  ℤ≤-simpl₁' .(+ 0) .(+ 0) (+≤+ {.0} {zero} z≤n) = ℤ≤.refl
  ℤ≤-simpl₁' .(+ ℕs n) .(+ 0) (+≤+ {zero} {ℕs n} m≤n) = +≤+ z≤n
  ℤ≤-simpl₁' .(+ ℕs n') .(+ 1) (+≤+ {ℕs zero} {ℕs n'} (s≤s m≤n)) = +≤+ m≤n
  ℤ≤-simpl₁' .(+ ℕs (ℕs n')) .(+ ℕs (ℕs n)) (+≤+ {ℕs (ℕs n)} {ℕs .(ℕs n')} (s≤s (s≤s {.n} {n'} m≤n))) = ℤ≤-simpl₁' (+ ℕs n') (+ ℕs n) (+≤+ (s≤s m≤n))

  ℤ≤-simpl₂ : ∀ (p q : ℤ) → p ℤ+ - q ℤ≤ + 0 → p ℤ≤ q
  ℤ≤-simpl₂ -[1+ n ] -[1+ n' ] H = -≤- (ℤ≤-ℕ≤-inj₁ n' n H)
  ℤ≤-simpl₂ -[1+ n ] (+ n') H = -≤+
  ℤ≤-simpl₂ (+ zero) -[1+ n' ] (+≤+ ())
  ℤ≤-simpl₂ (+ ℕs n) -[1+ n' ] (+≤+ ())
  ℤ≤-simpl₂ (+ zero) (+ zero) H = +≤+ z≤n
  ℤ≤-simpl₂ (+ zero) (+ ℕs n) H = +≤+ z≤n
  ℤ≤-simpl₂ (+ ℕs n) (+ zero) (+≤+ ())
  ℤ≤-simpl₂ (+ ℕs n) (+ ℕs n') H = +≤+ (s≤s (ℤ≤-ℕ≤-inj₁ n n' H))

  ¬ℤ<-is-ℤ≥ : ∀ {p q : ℤ} → (+ 1 ℤ+ p ℤ≤ q → ⊥) → q ℤ≤ p
  ¬ℤ<-is-ℤ≥ {p} {q} H with ℤcompare p q
  ¬ℤ<-is-ℤ≥ H | less y = ⊥-elim (H y)
  ¬ℤ<-is-ℤ≥ H | equal refl = ℤ≤.refl
  ¬ℤ<-is-ℤ≥ H | greater y = ℤ≤.trans (nℤ≤sn _) y

  ¬ℤ≤-is-ℤ> : ∀ {p q : ℤ} → (p ℤ≤ q → ⊥) → ℤs q ℤ≤ p
  ¬ℤ≤-is-ℤ> {p} {q} H with ℤcompare p q
  ¬ℤ≤-is-ℤ> {p} H | less y = ⊥-elim (H (ℤ≤.trans (nℤ≤sn p) y))
  ¬ℤ≤-is-ℤ> {p} H | equal y = ⊥-elim (H (subst (λ u → p ℤ≤ u) y ℤ≤.refl))
  ¬ℤ≤-is-ℤ> H | greater y = y

-----
-- ℤ≤ is compatible with common operators
-----

  ℤ+ℤ≤-l₁₁ : ∀ p n → ℤs (-[1+ ℕs n ] ℤ+ p) ≡ -[1+ n ] ℤ+ p
  ℤ+ℤ≤-l₁₁ -[1+ n ] n' = refl
  ℤ+ℤ≤-l₁₁ (+ zero) n' = refl
  ℤ+ℤ≤-l₁₁ (+ ℕs zero) zero = refl
  ℤ+ℤ≤-l₁₁ (+ ℕs (ℕs n)) zero = refl
  ℤ+ℤ≤-l₁₁ (+ ℕs n) (ℕs n') = ℤ+ℤ≤-l₁₁ (+ n) n'


  ℤ+ℤ≤-l₃ : ∀ p n → -[1+ n ] ℤ+ p ℤ≤ p
  ℤ+ℤ≤-l₃  -[1+ n ] zero = -≤- (nℕ≤sn n)
  ℤ+ℤ≤-l₃ (+ zero) zero = -≤+
  ℤ+ℤ≤-l₃ (+ ℕs n) zero = +≤+ (nℕ≤sn n)
  ℤ+ℤ≤-l₃ p (ℕs n) = ℤ≤.trans (subst (λ x → -[1+ ℕs n ] ℤ+ p ℤ≤ x) (ℤ+ℤ≤-l₁₁ p n) (nℤ≤sn (-[1+ ℕs n ] ℤ+ p))) (ℤ+ℤ≤-l₃ p n)


  ℤ+ℤ≤-l₂₁ : ∀ p n → ℤs (+ n ℤ+ p) ≡ (+ ℕs n) ℤ+ p
  ℤ+ℤ≤-l₂₁ -[1+ n ] zero = refl
  ℤ+ℤ≤-l₂₁ -[1+ zero ] (ℕs n') = refl
  ℤ+ℤ≤-l₂₁ -[1+ ℕs n ] (ℕs n') = ℤ+ℤ≤-l₂₁ -[1+ n ] n'
  ℤ+ℤ≤-l₂₁ (+ n) n' = refl

  ℤ+ℤ≤-l₄ : ∀ p n → p ℤ≤ + n ℤ+ p
  ℤ+ℤ≤-l₄ p zero with + 0 ℤ+ p | proj₁ ℤr.+-identity p
  ... | .p | refl = ℤ≤.refl
  ℤ+ℤ≤-l₄ p (ℕs n) = ℤ≤.trans (ℤ+ℤ≤-l₄ p  n) (subst (λ x → + n ℤ+ p ℤ≤ x) (ℤ+ℤ≤-l₂₁ p n) (nℤ≤sn (+ n ℤ+ p)))

  ℕ+ℕ≤-l : ∀ m n p → n ℕ≤ p → m ℕ+ n ℕ≤ m ℕ+ p
  ℕ+ℕ≤-l zero n p H = H
  ℕ+ℕ≤-l (ℕs n) n' p H = s≤s (ℕ+ℕ≤-l n n' p H)

  ℕ+ℕ≤-r : ∀ m n p → n ℕ≤ p → n ℕ+ m ℕ≤ p ℕ+ m
  ℕ+ℕ≤-r m n p H = subst₂ (λ x x' → x ℕ≤ x') (ℕr.+-comm m n) (ℕr.+-comm m p) (ℕ+ℕ≤-l m n p H)

  sign-distr : ∀ s n₁ n₂ → s ◃ (n₁ ℕ+ n₂) ≡ (s ◃ n₁) ℤ+ (s ◃ n₂)
  sign-distr s zero n₂ = sym (proj₁ ℤr.+-identity (s ◃ n₂))
  sign-distr s n₁ zero with n₁ ℕ+ 0 | proj₂ ℕr.+-identity n₁
  ... | .n₁ | refl = sym (proj₂ ℤr.+-identity (s ◃ n₁))
  sign-distr S- (ℕs n) (ℕs n') = cong -[1+_] (m+1+n≡1+m+n n n')
  sign-distr S+ (ℕs n) (ℕs n') = refl
  
  simpl-ℤ*ℕs : ∀ n p → (+ ℕs n) ℤ* p ≡ p ℤ+ ((+ n) ℤ* p)
  simpl-ℤ*ℕs zero p with ∣ p ∣ ℕ+ 0 | proj₂ ℕr.+-identity ∣ p ∣ | p ℤ+ + 0 | proj₂ ℤr.+-identity p
  ... | .(∣ p ∣) | refl | .p | refl = ◃-left-inverse p
  simpl-ℤ*ℕs (ℕs n) p = subst (λ x → x ≡ p ℤ+ ((+ ℕs n) ℤ* p)) (sym (sign-distr (sign p) ∣ p ∣ (∣ p ∣ ℕ+ n ℕ* ∣ p ∣))) (ℤ+-right (◃-left-inverse p))

  ℤ+ℤ≤-l₁ : ∀ n q r → q ℤ≤ r → -[1+ n ] ℤ+ q ℤ≤ -[1+ n ] ℤ+ r
  ℤ+ℤ≤-l₁ zero -[1+ n ] -[1+ n' ] (-≤- n≤m) = -≤- (s≤s n≤m)
  ℤ+ℤ≤-l₁ zero -[1+ n ] (+ zero) -≤+ = -≤- z≤n
  ℤ+ℤ≤-l₁ zero -[1+ n ] (+ ℕs n') -≤+ = -≤+
  ℤ+ℤ≤-l₁ zero (+ n) -[1+ n' ] ()
  ℤ+ℤ≤-l₁ zero (+ zero) (+ zero) H = -≤- z≤n
  ℤ+ℤ≤-l₁ zero (+ zero) (+ ℕs n) H = -≤+
  ℤ+ℤ≤-l₁ zero (+ ℕs n) (+ zero) (+≤+ ())
  ℤ+ℤ≤-l₁ zero (+ ℕs n) (+ ℕs n') (+≤+ (s≤s m≤n)) = +≤+ m≤n
  ℤ+ℤ≤-l₁ (ℕs n) q r H = ℤp-ℤ≤-compat (subst₂ (λ x x' → x ℤ≤ x') (sym (ℤ+ℤ≤-l₁₁ q n)) (sym (ℤ+ℤ≤-l₁₁ r n)) (ℤ+ℤ≤-l₁ n q r H))

  ℤ+ℤ≤-l₂ : ∀ n q r → q ℤ≤ r → + n ℤ+ q ℤ≤ + n ℤ+ r
  ℤ+ℤ≤-l₂ zero q r H with + 0 ℤ+ q | + 0 ℤ+ r | proj₁ ℤr.+-identity q | proj₁ ℤr.+-identity r
  ... | .q | .r | refl | refl = H
  ℤ+ℤ≤-l₂ (ℕs n) q r H = subst₂ (λ x x' → x ℤ≤ x') (ℤ+ℤ≤-l₂₁ q n) (ℤ+ℤ≤-l₂₁ r n) (ℤs-ℤ≤-compat (ℤ+ℤ≤-l₂ n q r H))

  ℤ+ℤ≤-l : ∀ {p q r} → q ℤ≤ r → p ℤ+ q ℤ≤ p ℤ+ r
  ℤ+ℤ≤-l { -[1+ n ]} H = ℤ+ℤ≤-l₁ n _ _ H
  ℤ+ℤ≤-l {+ n} H = ℤ+ℤ≤-l₂ n _ _ H

  ℤ+ℤ≤-r : ∀ {p q r} → q ℤ≤ r → q ℤ+ p ℤ≤ r ℤ+ p
  ℤ+ℤ≤-r {p} {q} {r} H = subst₂ (λ x x' → x ℤ≤ x') (ℤr.+-comm p q) (ℤr.+-comm p r) (ℤ+ℤ≤-l {p} H)

  -ℤ≤-l : ∀ p n → p ℤ- (+ n) ℤ≤ p
  -ℤ≤-l p zero = subst₂ (λ u v → u ℤ≤ v) (sym (unfold-ℤ- p (+ 0))) (proj₂ ℤr.+-identity p) ℤ≤.refl 
  -ℤ≤-l p (ℕs n) = subst₂ (λ u v → u ℤ≤ v) (sym (unfold-ℤ- p (+ ℕs n))) (proj₂ ℤr.+-identity p) (ℤ+ℤ≤-l {p} -≤+)

  +-ℤ≤-r : ∀ p n → p ℤ≤ p ℤ+ (+ n)
  +-ℤ≤-r p n = subst (λ u → u ℤ≤ p ℤ+ (+ n)) (proj₂ ℤr.+-identity p) (ℤ+ℤ≤-l {p} (+≤+ z≤n))

  ℤ*ℤ≤-l : ∀ {p q r} → + 0 ℤ≤ p → q ℤ≤ r → p ℤ* q ℤ≤ p ℤ* r
  ℤ*ℤ≤-l { -[1+ n ]} () H
  ℤ*ℤ≤-l {+ zero} p-pos H = ℤ≤.refl
  ℤ*ℤ≤-l {+ ℕs n} {q} {r} p-pos H with (+ ℕs n) ℤ* q | simpl-ℤ*ℕs n q | (+ ℕs n) ℤ* r | simpl-ℤ*ℕs n r
  ... | .(q ℤ+ (+ n ℤ* q)) | refl | .(r ℤ+ (+ n ℤ* r)) | refl = ℤ≤.trans (ℤ+ℤ≤-l {q} (ℤ*ℤ≤-l {+ n} (+≤+ z≤n) H)) (ℤ+ℤ≤-r H)

  ℕ*-ℕ≤-l : ∀ {n p q} → p ℕ≤ q → n ℕ* p ℕ≤ n ℕ* q
  ℕ*-ℕ≤-l {zero} H = ℕ≤.refl
  ℕ*-ℕ≤-l {ℕs n} {p} {q} H = ℕ≤.trans (ℕ+ℕ≤-r (n ℕ* p) p q H) (ℕ+ℕ≤-l q (n ℕ* p) (n ℕ* q) (ℕ*-ℕ≤-l {n} H))

  ℕ*ℕ≤-l-elim : ∀ {n p q} → (ℕs n) ℕ* p ℕ≤ (ℕs n) ℕ* q → p ℕ≤ q
  ℕ*ℕ≤-l-elim {n} {p} {q} H with ℕcompare p q
  ℕ*ℕ≤-l-elim {n} {p} H | less y = ℕ≤.trans (nℕ≤sn p) y
  ℕ*ℕ≤-l-elim H | equal refl = ℕ≤.refl
  ℕ*ℕ≤-l-elim {n} {p} {q} H | greater y with ℕ*-ℕ≤-l {ℕs n} y | ℕ*-ℕ≤-l {n} (nℕ≤sn q)
  ... | h | h' = ⊥-elim (ℕ<-irrefl ((ℕs n) ℕ* q) (ℕ≤.trans (s≤s (ℕ+ℕ≤-l q _ _ h')) (ℕ≤.trans h H)))

  ℤ*ℤ≤-l-elim : ∀ {n p q} → (+ ℕs n) ℤ* p ℤ≤ (+ ℕs n) ℤ* q → p ℤ≤ q
  ℤ*ℤ≤-l-elim {zero} {p} {q} H = subst₂ (λ u v → u ℤ≤ v) (proj₁ ℤr.*-identity p) (proj₁ ℤr.*-identity q) H
  ℤ*ℤ≤-l-elim {ℕs n} { -[1+ n' ]} { -[1+ n0 ]} (-≤- n≤m) with ℕ*ℕ≤-l-elim {ℕs n} {ℕs n0} {ℕs n'} (s≤s n≤m)
  ℤ*ℤ≤-l-elim {ℕs n} { -[1+ n' ]} { -[1+ n0 ]} (-≤- n≤m) | (s≤s H) = -≤- H
  ℤ*ℤ≤-l-elim {ℕs n} {+ zero} { -[1+ n0 ]} H with n ℕ* 0 | proj₂ ℕr.zero n
  ℤ*ℤ≤-l-elim {ℕs n} {+ zero} { -[1+ n0 ]} () | .0 | refl
  ℤ*ℤ≤-l-elim {ℕs n} {+ ℕs n'} { -[1+ n0 ]} ()
  ℤ*ℤ≤-l-elim {ℕs n} { -[1+ n' ]} {+ n0} H = -≤+
  ℤ*ℤ≤-l-elim {ℕs n} {+ zero} {+ n0} H = +≤+ z≤n
  ℤ*ℤ≤-l-elim {ℕs n} {+ ℕs n'} {+ zero} H with n ℕ* 0 | proj₂ ℕr.zero n
  ℤ*ℤ≤-l-elim {ℕs n} {+ ℕs n'} {+ zero} (+≤+ ()) | .0 | refl
  ℤ*ℤ≤-l-elim {ℕs n} {+ ℕs n'} {+ ℕs n0} (+≤+ m≤n)  with ℕ*ℕ≤-l-elim {ℕs n} {ℕs n'} {ℕs n0} m≤n
  ... | H = +≤+ H

-----
-- ℤ⊔ & ℤ⊓
-----

  ℤ⊓-comm : ∀ x₁ x₂ → x₁ ℤ⊓ x₂ ≡ x₂ ℤ⊓ x₁
  ℤ⊓-comm -[1+ n₁ ] -[1+ n₂ ] = cong -[1+_] (ℕ⊔⊓.∧-comm n₁ n₂)
  ℤ⊓-comm -[1+ n₁ ] (+ n₂) = refl
  ℤ⊓-comm (+ n₁) -[1+ n₂ ] = refl
  ℤ⊓-comm (+ n₁) (+ n₂) = cong (λ x → + x) (ℕ⊔⊓.∨-comm n₁ n₂)

  ℤ⊔-comm : ∀ x₁ x₂ → x₁ ℤ⊔ x₂ ≡ x₂ ℤ⊔ x₁
  ℤ⊔-comm -[1+ n₁ ] -[1+ n₂ ] = cong -[1+_] (ℕ⊔⊓.∨-comm n₁ n₂)
  ℤ⊔-comm -[1+ n₁ ] (+ n₂) = refl
  ℤ⊔-comm (+ n₁) -[1+ n₂ ] = refl
  ℤ⊔-comm (+ n₁) (+ n₂) = cong (λ x → + x)  (ℕ⊔⊓.∧-comm n₁ n₂)

  ℕ⊓-ℕ≤-l : ∀ n₁ n₂ → n₁ ℕ⊓ n₂ ℕ≤ n₁
  ℕ⊓-ℕ≤-l zero n₂ = ℕ≤.refl
  ℕ⊓-ℕ≤-l (ℕs n₁) zero = z≤n
  ℕ⊓-ℕ≤-l (ℕs n₁) (ℕs n₂) = s≤s (ℕ⊓-ℕ≤-l n₁ n₂)

  ℕ⊔-ℕ≤-l : ∀ n₁ n₂ → n₁ ℕ≤ n₁ ℕ⊔ n₂
  ℕ⊔-ℕ≤-l zero n₂ = z≤n
  ℕ⊔-ℕ≤-l (ℕs n₁) zero = ℕ≤.refl
  ℕ⊔-ℕ≤-l (ℕs n₁) (ℕs n₂) = s≤s (ℕ⊔-ℕ≤-l n₁ n₂)

  ℤ⊓-ℤ≤-l : ∀ x₁ x₂ → x₁ ℤ⊓ x₂ ℤ≤ x₁
  ℤ⊓-ℤ≤-l -[1+ n₁ ] -[1+ n₂ ] = -≤- (ℕ⊔-ℕ≤-l n₁ n₂)
  ℤ⊓-ℤ≤-l -[1+ n₁ ] (+ n₂) = ℤ≤.refl
  ℤ⊓-ℤ≤-l (+ n₁) -[1+ n₂ ] = -≤+
  ℤ⊓-ℤ≤-l (+ n₁) (+ n₂) = +≤+ (ℕ⊓-ℕ≤-l n₁ n₂)

  ℤ⊓-ℤ≤-r : ∀ x₁ x₂ → x₁ ℤ⊓ x₂ ℤ≤ x₂
  ℤ⊓-ℤ≤-r x₁ x₂ with x₁ ℤ⊓ x₂ | ℤ⊓-comm x₁ x₂
  ... | .(x₂ ℤ⊓ x₁) | refl = ℤ⊓-ℤ≤-l x₂ x₁

  ℤ⊔-ℤ≤-l : ∀ x₁ x₂ → x₁ ℤ≤ x₁ ℤ⊔ x₂
  ℤ⊔-ℤ≤-l -[1+ n₁ ] -[1+ n₂ ] = -≤- (ℕ⊓-ℕ≤-l n₁ n₂)
  ℤ⊔-ℤ≤-l -[1+ n₁ ] (+ n₂) = -≤+
  ℤ⊔-ℤ≤-l (+ n₁) -[1+ n₂ ] = ℤ≤.refl
  ℤ⊔-ℤ≤-l (+ n₁) (+ n₂) = +≤+ (ℕ⊔-ℕ≤-l n₁ n₂)

  ℤ⊔-ℤ≤-r : ∀ x₁ x₂ → x₂ ℤ≤ x₁ ℤ⊔ x₂
  ℤ⊔-ℤ≤-r x₁ x₂ with x₁ ℤ⊔ x₂ | ℤ⊔-comm x₁ x₂
  ... | .(x₂ ℤ⊔ x₁) | refl = ℤ⊔-ℤ≤-l x₂ x₁

-----
-- Bounded & Fin
-----

  elim-bounded : ∀ x d → x ℤ≤ + 0 → + 0 ℤ≤ x ℤ+ (+ d) → ∃ (λ (j : Fin (ℕs d)) → x ℤ+ (+ toℕ j) ≡ + 0)
  elim-bounded -[1+ n ] zero h₁ ()
  elim-bounded -[1+ zero ] (ℕs n') h₁ h₂ = Fs zero , refl
  elim-bounded -[1+ ℕs n ] (ℕs n') h₁ h₂ with elim-bounded -[1+ n ] n' -≤+ h₂
  ... | j , Hj = Fs j , Hj
  elim-bounded (+ .0) d (+≤+ z≤n) h₂ = zero , refl


  postulate ℤ≤-reachability : ∀ x z (δ : Notnull) → z ℤ≤ x → Σ ℕ (λ k → x ℤ- (+ k) ℤ* + ∣ P.proj₁ δ ∣ ℤ≤ z)