module Comparisons where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_)
open import Data.Fin renaming (suc to Fs ; pred to Fp ; _≤_ to _F≤_)

data Fordering {n : ℕ} (i j : Fin n) : Set where
  less : Fs i F≤ (inject₁ j) → Fordering i j
  equal : i ≡ j → Fordering i j
  greater : Fs j F≤ (inject₁ i) → Fordering i j

Fcompare : ∀ {n} (i j : Fin n) → Fordering i j
Fcompare zero zero = equal refl
Fcompare zero (Fs i) = less (s≤s z≤n)
Fcompare (Fs i) zero = greater (s≤s z≤n)
Fcompare {ℕs n} (Fs i) (Fs i') with Fcompare i i'
Fcompare {ℕs zero} (Fs ()) (Fs i') | less y
Fcompare {ℕs (ℕs n)} (Fs i) (Fs zero) | less ()
Fcompare {ℕs (ℕs n)} (Fs i) (Fs (Fs i')) | less (s≤s m≤n) = less (s≤s (s≤s m≤n))
Fcompare {ℕs n} (Fs i) (Fs .i) | equal refl = equal refl
Fcompare {ℕs zero} (Fs ()) (Fs i') | greater y
Fcompare {ℕs (ℕs n)} (Fs zero) (Fs i') | greater ()
Fcompare {ℕs (ℕs n)} (Fs (Fs i)) (Fs i') | greater (s≤s m≤n) = greater (s≤s (s≤s m≤n))

data ℕordering (i j : ℕ) : Set where
  less : ℕs i ℕ≤ j → ℕordering i j
  equal : i ≡ j → ℕordering i j
  greater : ℕs j ℕ≤ i → ℕordering i j

ℕcompare : ∀ i j → ℕordering i j
ℕcompare zero zero = equal refl
ℕcompare zero (ℕs n) = less (s≤s z≤n)
ℕcompare (ℕs n) zero = greater (s≤s z≤n)
ℕcompare (ℕs n) (ℕs n') with ℕcompare n n'
ℕcompare (ℕs n) (ℕs n') | less y = less (s≤s y)
ℕcompare (ℕs .n') (ℕs n') | equal refl = equal refl
ℕcompare (ℕs n) (ℕs n') | greater y = greater (s≤s y)

data ℤordering (i j : ℤ) : Set where
  less : ℤs i ℤ≤ j → ℤordering i j
  equal : i ≡ j → ℤordering i j
  greater : ℤs j ℤ≤ i → ℤordering i j

ℤcompare : ∀ (i j : ℤ) → ℤordering i j
ℤcompare -[1+ zero ] -[1+ zero ] = equal refl
ℤcompare -[1+ zero ] -[1+ ℕs n ] = greater (-≤- z≤n)
ℤcompare -[1+ ℕs n ] -[1+ zero ] = less (-≤- z≤n)
ℤcompare -[1+ ℕs n ] -[1+ ℕs n' ] with ℤcompare -[1+ n ] -[1+ n' ]
ℤcompare -[1+ ℕs zero ] -[1+ ℕs n' ] | less ()
ℤcompare -[1+ ℕs (ℕs n) ] -[1+ ℕs n' ] | less (-≤- n≤m) = less (-≤- (s≤s n≤m))
ℤcompare -[1+ ℕs .n' ] -[1+ ℕs n' ] | equal refl = equal refl
ℤcompare -[1+ ℕs n ] -[1+ ℕs zero ] | greater ()
ℤcompare -[1+ ℕs n ] -[1+ ℕs (ℕs n') ] | greater (-≤- n≤m) = greater (-≤- (s≤s n≤m))
ℤcompare -[1+ zero ] (+ n') = less (+≤+ z≤n)
ℤcompare -[1+ ℕs n ] (+ n') = less -≤+
ℤcompare (+ n) -[1+ zero ] = greater (+≤+ z≤n)
ℤcompare (+ n) -[1+ ℕs n' ] = greater -≤+
ℤcompare (+ zero) (+ zero) = equal refl
ℤcompare (+ zero) (+ ℕs n) = less (+≤+ (s≤s z≤n))
ℤcompare (+ ℕs n) (+ zero) = greater (+≤+ (s≤s z≤n))
ℤcompare (+ ℕs n) (+ ℕs n') with ℤcompare (+ n) (+ n')
ℤcompare (+ ℕs n) (+ ℕs n') | less (+≤+ m≤n) = less (+≤+ (s≤s m≤n))
ℤcompare (+ ℕs .n') (+ ℕs n') | equal refl = equal refl
ℤcompare (+ ℕs n) (+ ℕs n') | greater (+≤+ m≤n) = greater (+≤+ (s≤s m≤n))

ℕ≡-dec : ∀ (m n : ℕ) → Dec (m ≡ n)
ℕ≡-dec zero zero = yes refl
ℕ≡-dec zero (ℕs n) = no (λ ())
ℕ≡-dec (ℕs n) zero = no (λ ())
ℕ≡-dec (ℕs n) (ℕs n') with ℕ≡-dec n n'
... | yes P = yes (cong ℕs P)
... | no ¬P = no (λ x → ¬P (cong ℕp x))

ℤ≡-dec₁ : ∀ {n n' : ℕ} → -[1+ n ] ≡ -[1+ n' ] → n ≡ n'
ℤ≡-dec₁ {n} {.n} refl = refl

ℤ≡-dec₂ : ∀ {n n' : ℕ} → + n ≡ + n' → n ≡ n'
ℤ≡-dec₂ {n} {.n} refl = refl

ℤ≡-dec : ∀ (p q : ℤ) → Dec (p ≡ q)
ℤ≡-dec -[1+ n ] -[1+ n' ] with ℕ≡-dec n n'
ℤ≡-dec -[1+ .n' ] -[1+ n' ] | yes refl = yes refl
... | no ¬P = no (λ x → ¬P (ℤ≡-dec₁ x))
ℤ≡-dec -[1+ n ] (+ n') = no (λ ())
ℤ≡-dec (+ n) -[1+ n' ] = no (λ ())
ℤ≡-dec (+ n) (+ n') with ℕ≡-dec n n'
... | yes P = yes (cong (λ p → + p) P)
... | no ¬P = no (λ x → ¬P (ℤ≡-dec₂ x))

F≡-dec₁ : ∀ {n} (i i' : Fin n) → Fs i ≡ Fs i' → i ≡ i'
F≡-dec₁ .i' i' refl = refl

F≡-dec : ∀ {n} (p q : Fin n) → Dec (p ≡ q)
F≡-dec zero zero = yes refl
F≡-dec zero (Fs i) = no (λ ())
F≡-dec (Fs i) zero = no (λ ())
F≡-dec (Fs i) (Fs i') with F≡-dec i i'
... | yes Heq = yes (subst (λ x → Fs i ≡ Fs x) Heq refl)
... | no ¬Heq = no (λ x → ¬Heq (F≡-dec₁ i i' x))

ℤnull-dec : ∀ n → Dec (n ≡ + 0)
ℤnull-dec n = ℤ≡-dec n (+ 0)