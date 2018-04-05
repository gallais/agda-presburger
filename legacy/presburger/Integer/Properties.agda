module Integer.Properties where

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_)

open import Data.Nat.Properties as NatProp
open import Data.Integer.Properties

open import Data.Product
open import Data.Empty

open import Algebra
open import Algebra.Structures
open import Function

open import Relation.Binary
private module ℕ≤ = DecTotalOrder Int.decTotalOrder
private module ℕr = IsCommutativeSemiring NatProp.isCommutativeSemiring

open import Relation.Unary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_ ; _≢_ ; refl ; sym ; cong ; cong₂ ; subst ; subst₂)
open import Relation.Binary.PropositionalEquality.Core using (isEquivalence)

open import Integer.Basic-Properties

abstract

  lemma : ∀ n n' n0 → n ℕ+ ℕs (n' ℕ+ n0) ≡ ℕs (n ℕ+ n' ℕ+ n0)
  lemma n n' n0 = subst₂ (λ x x' → x ≡ ℕs x') (sym (m+1+n≡1+m+n n (n' ℕ+ n0))) (sym (ℕr.+-assoc n n' n0)) refl

  ℕs⊖-simpl : ∀ m n → ℕs m ⊖ n ≡ ℤs (m ⊖ n)
  ℕs⊖-simpl m zero = refl
  ℕs⊖-simpl zero (ℕs n) = refl
  ℕs⊖-simpl (ℕs n) (ℕs n') = ℕs⊖-simpl n n'

  ⊖ℕs-simpl₁ : ∀ x → x ≡ -[1+ 0 ] ℤ+ (+ 1 ℤ+ x)
  ⊖ℕs-simpl₁ -[1+ zero ] = refl
  ⊖ℕs-simpl₁ -[1+ ℕs n ] = refl
  ⊖ℕs-simpl₁ (+ n) = refl

  ⊖ℕs-simpl : ∀ m n → m ⊖ ℕs n ≡ -[1+ 0 ] ℤ+ (m ⊖ n)
  ⊖ℕs-simpl zero zero = refl
  ⊖ℕs-simpl zero (ℕs n) = refl
  ⊖ℕs-simpl (ℕs n) n' = subst (λ x → n ⊖ n' ≡ -[1+ 0 ] ℤ+ x) (sym (ℕs⊖-simpl n n')) (⊖ℕs-simpl₁ (n ⊖ n'))

  ℤs-simpl : ∀ n → + (ℕs n) ≡ ℤs (+ n)
  ℤs-simpl = λ _ → refl

  ℤs+-simpl : ∀ m n → + (ℕs m) ℤ+ n ≡ ℤs (+ m ℤ+ n)
  ℤs+-simpl zero -[1+ n' ] = refl
  ℤs+-simpl (ℕs n) -[1+ n' ] = ℕs⊖-simpl n n'
  ℤs+-simpl n (+ n') = refl

  ℤ+-assoc1₁ : ∀ y z → (+ 1 ℤ+ (y ℤ+ z) ≡ + 1 ℤ+ y ℤ+ z)
  ℤ+-assoc1₁ -[1+ zero ] -[1+ n ] = refl
  ℤ+-assoc1₁ -[1+ zero ] (+ zero) = refl
  ℤ+-assoc1₁ -[1+ zero ] (+ ℕs n) = refl
  ℤ+-assoc1₁ -[1+ ℕs n ] -[1+ n' ] = refl
  ℤ+-assoc1₁ -[1+ ℕs n ] (+ zero) = refl
  ℤ+-assoc1₁ -[1+ ℕs n ] (+ ℕs zero) = refl
  ℤ+-assoc1₁ -[1+ ℕs n ] (+ ℕs (ℕs n')) = sym (ℕs⊖-simpl n' n)
  ℤ+-assoc1₁ (+ n) z = sym (ℤs+-simpl n z)

  ℤ+-assoc1 : ∀ n y z → + n ℤ+ (y ℤ+ z) ≡ + n ℤ+ y ℤ+ z
  ℤ+-assoc1 zero -[1+ n ] z = subst (λ x → x ≡ -[1+ n ] ℤ+ z) (sym (ℤ+-zero-l (-[1+ n ] ℤ+ z))) refl
  ℤ+-assoc1 zero (+ n) z = subst (λ x → x ≡ + n ℤ+ z) (sym (ℤ+-zero-l (+ n ℤ+ z))) refl
  ℤ+-assoc1 (ℕs n) y z with ℤ+-assoc1 n y z
  ... | eq = subst (λ x → x ≡ + ℕs n ℤ+ y ℤ+ z) (sym (ℤs+-simpl n (y ℤ+ z))) (subst₂ (λ x x' → + 1 ℤ+ x ≡ x' ℤ+ z) (sym eq) (sym (ℤs+-simpl n y)) (ℤ+-assoc1₁ (+ n ℤ+ y) z))

  ℤ+-assoc2₁ : ∀ n n' n0 → -[1+ ℕs n ] ℤ+ (ℕs n0 ⊖ n') ≡ n0 ⊖ ℕs (n ℕ+ n')
  ℤ+-assoc2₁ n zero zero = cong -[1+_] (sym ((proj₂ ℕr.+-identity) n))
  ℤ+-assoc2₁ n (ℕs zero) zero = cong -[1+_] (ℕr.+-comm 1 n)
  ℤ+-assoc2₁ n (ℕs (ℕs n')) zero with ℕr.+-comm (ℕs (ℕs n')) n | ℕr.+-comm n' n 
  ... | h₁ | h₂ = subst₂ (λ x x' → -[1+ ℕs (ℕs x)] ≡ -[1+ x' ]) h₂ h₁ refl 
  ℤ+-assoc2₁ n zero (ℕs n0) = cong (λ x → n0 ⊖ x) (sym ((proj₂ ℕr.+-identity n)))
  ℤ+-assoc2₁ n (ℕs n') (ℕs n0) with ℤ+-assoc2₁ n n' n0
  ... | eq = subst (λ x → x ≡ n0 ⊖ (n ℕ+ ℕs n')) (sym eq) (cong (λ x → n0 ⊖ x) (sym (m+1+n≡1+m+n n n')))

  ℤ+-assoc2₂₁ : ∀ n n' z → -[1+ ℕs n ] ℤ+ (+ ℕs (ℕs n') ℤ+ z) ≡ -[1+ n ] ℤ+ (+ ℕs n' ℤ+ z)
  ℤ+-assoc2₂₁ n n' -[1+ zero ] = refl
  ℤ+-assoc2₂₁ n zero -[1+ ℕs zero ] = cong (-[1+_] ∘ ℕs) (sym ((proj₂ ℕr.+-identity) n))
  ℤ+-assoc2₂₁ n zero -[1+ ℕs (ℕs n') ] = cong (-[1+_] ∘ ℕs) (sym (m+1+n≡1+m+n n n'))
  ℤ+-assoc2₂₁ n (ℕs n') -[1+ ℕs n0 ] = ℤ+-assoc2₂₁ n n' -[1+ n0 ]
  ℤ+-assoc2₂₁ n n' (+ n0) = refl

  tmp : ∀ n n' n0 → ℕs n' ⊖ n ℤ+ -[1+ ℕs n0 ] ≡ ℕs (ℕs n') ⊖ n ℤ+ -[1+ ℕs (ℕs n0) ]
  tmp zero n' n0 = refl
  tmp (ℕs zero) zero n0 = refl
  tmp (ℕs (ℕs zero)) zero n0 = refl
  tmp (ℕs (ℕs (ℕs n))) zero n0 = cong (-[1+_] ∘ ℕs) (sym (m+1+n≡1+m+n n (ℕs n0)))
  tmp (ℕs n) (ℕs n') n0 = tmp n n' n0

  ℤ+-assoc2₂₂ : ∀ n n' n0 → -[1+ ℕs n ] ℤ+ (ℕs n' ⊖ n0) ≡ ℕs n' ⊖ n ℤ+ -[1+ ℕs n0 ]
  ℤ+-assoc2₂₂ zero n' zero = refl
  ℤ+-assoc2₂₂ (ℕs zero) zero zero = refl
  ℤ+-assoc2₂₂ (ℕs (ℕs n)) zero zero = cong (-[1+_] ∘ ℕs) (ℕr.+-comm 1 n)
  ℤ+-assoc2₂₂ (ℕs n) (ℕs n') zero = ℤ+-assoc2₂₂ n n' zero
  ℤ+-assoc2₂₂ zero zero (ℕs zero) = refl
  ℤ+-assoc2₂₂ zero zero (ℕs (ℕs n)) = refl
  ℤ+-assoc2₂₂ (ℕs zero) zero (ℕs zero) = refl
  ℤ+-assoc2₂₂ (ℕs zero) zero (ℕs (ℕs n)) = refl
  ℤ+-assoc2₂₂ (ℕs (ℕs n)) zero (ℕs zero) = cong (-[1+_] ∘ ℕs) (ℕr.+-comm 2 n)
  ℤ+-assoc2₂₂ (ℕs (ℕs n)) zero (ℕs (ℕs n')) = cong (-[1+_] ∘ ℕs) (subst₂ (λ x x' → ℕs (ℕs x) ≡ x') (m+1+n≡1+m+n n n') (sym (m+1+n≡1+m+n n (ℕs (ℕs n')))) (cong ℕs (sym (m+1+n≡1+m+n n (ℕs n')))))
  ℤ+-assoc2₂₂ n (ℕs n') (ℕs n0) with ℤ+-assoc2₂₂ n n' n0
  ... | eq = subst (λ x → x ≡ ℕs (ℕs n') ⊖ n ℤ+ -[1+ ℕs (ℕs n0) ]) (sym eq) (tmp n n' n0)

  ℤ+-assoc2₂ : ∀ n n' z → -[1+ n ] ℤ+ (+ ℕs n' ℤ+ z) ≡ n' ⊖ n ℤ+ z
  ℤ+-assoc2₂ zero n' -[1+ n ] = sym (⊖ℕs-simpl n' n)
  ℤ+-assoc2₂ zero n' (+ n) = refl
  ℤ+-assoc2₂ (ℕs n) zero -[1+ zero ] = cong (-[1+_] ∘ ℕs) (sym (proj₂ (ℕr.+-identity) n))
  ℤ+-assoc2₂ (ℕs n) zero -[1+ ℕs n' ] = cong (-[1+_] ∘ ℕs) (sym (m+1+n≡1+m+n n n'))
  ℤ+-assoc2₂ (ℕs n) zero (+ n') = refl
  ℤ+-assoc2₂ (ℕs n) (ℕs n') z with ℤ+-assoc2₂ n n' z
  ℤ+-assoc2₂ (ℕs n) (ℕs zero) -[1+ zero ] | eq = eq
  ℤ+-assoc2₂ (ℕs n) (ℕs zero) -[1+ ℕs zero ] | eq = subst (λ x → -[1+ ℕs n ] ≡ x) eq (cong (-[1+_] ∘ ℕs) (sym ((proj₂ ℕr.+-identity) n)))
  ℤ+-assoc2₂ (ℕs n) (ℕs zero) -[1+ ℕs (ℕs n') ] | eq = subst (λ x → -[1+ ℕs (ℕs n ℕ+ n') ] ≡ x) eq (cong (-[1+_] ∘ ℕs) (sym (m+1+n≡1+m+n n n')))
  ℤ+-assoc2₂ (ℕs n) (ℕs (ℕs n')) -[1+ zero ] | eq = eq
  ℤ+-assoc2₂ (ℕs n) (ℕs (ℕs n')) -[1+ ℕs n0 ] | eq = ℤ+-assoc2₂₂ n n' n0
  ℤ+-assoc2₂ (ℕs n) (ℕs n') (+ n0) | eq = eq

  ℤ+-assoc2 : ∀ n y z → -[1+ n ] ℤ+ (y ℤ+ z) ≡ -[1+ n ] ℤ+ y ℤ+ z
  ℤ+-assoc2 zero -[1+ n ] -[1+ n' ] = refl
  ℤ+-assoc2 zero -[1+ n ] (+ zero) = refl
  ℤ+-assoc2 zero -[1+ n ] (+ ℕs n') = sym (⊖ℕs-simpl n' n)
  ℤ+-assoc2 zero (+ zero) -[1+ n' ] = refl
  ℤ+-assoc2 zero (+ ℕs n) -[1+ n' ] = sym (⊖ℕs-simpl n n')
  ℤ+-assoc2 zero (+ zero) (+ n') = refl
  ℤ+-assoc2 zero (+ ℕs n) (+ n') = refl
  ℤ+-assoc2 (ℕs n) -[1+ n' ] -[1+ n0 ] = cong (-[1+_] ∘ ℕs ∘ ℕs) (lemma n n' n0)
  ℤ+-assoc2 (ℕs n) -[1+ n' ] (+ zero) = refl
  ℤ+-assoc2 (ℕs n) -[1+ zero ] (+ ℕs zero) = cong (-[1+_] ∘ ℕs) (sym ((proj₂ ℕr.+-identity) n))
  ℤ+-assoc2 (ℕs n) -[1+ ℕs n' ] (+ ℕs zero) = cong (-[1+_] ∘ ℕs) (sym (m+1+n≡1+m+n n n'))
  ℤ+-assoc2 (ℕs n) -[1+ n' ] (+ ℕs (ℕs n0)) = ℤ+-assoc2₁ n n' n0
  ℤ+-assoc2 (ℕs n) (+ zero) z = ℤ+-left { -[1+ ℕs n ]} (ℤ+-zero-l z)
  ℤ+-assoc2 (ℕs n) (+ ℕs n') z  = ℤ+-assoc2₂ (ℕs n) n' z

  ℤ+-assoc : ∀ (x y z : ℤ) → x ℤ+ (y ℤ+ z) ≡ x ℤ+ y ℤ+ z
  ℤ+-assoc -[1+ n ] y z = ℤ+-assoc2 n y z
  ℤ+-assoc (+ n) y z = ℤ+-assoc1 n y z

  ℤ+-cong : {x : ℤ} {y : ℤ} {u : ℤ} {v : ℤ} → x ≡ y → u ≡ v → x ℤ+ u ≡ y ℤ+ v
  ℤ+-cong refl refl = refl

  ℤ+-inv : Σ ((x : ℤ) → - x ℤ+ x ≡ + 0) (λ _ → (x : ℤ) → x ℤ+ - x ≡ + 0)
  ℤ+-inv = ℤ+-opp-l , ℤ+-opp-r

  ℤ--cong : {i : ℤ} {j : ℤ} → i ≡ j → - i ≡ - j
  ℤ--cong refl = refl

open import Data.Sign renaming (+ to S+ ; - to S- ; _*_ to _S*_)

abstract

  ℤ*-cong : {x : ℤ} {y : ℤ} {u : ℤ} {v : ℤ} → x ≡ y → u ≡ v → (sign x) S* (sign u) ◃ ∣ x ∣ ℕ* ∣ u ∣ ≡ (sign y) S* (sign v) ◃ ∣ y ∣ ℕ* ∣ v ∣
  ℤ*-cong refl refl = refl

  tmp2 : ∀ n n' n0 → ℕs (n0 ℕ+ (n' ℕ+ n ℕ* ℕs n') ℕ* ℕs n0) ≡
       ℕs (n0 ℕ+ n' ℕ* ℕs n0 ℕ+ n ℕ* ℕs (n0 ℕ+ n' ℕ* ℕs n0))
  tmp2 n n' n0 = ℕr.*-assoc (ℕs n) (ℕs n') (ℕs n0)

  ℤ*-assoc : (x : ℤ) (y : ℤ) (z : ℤ) → x ℤ* y ℤ* z ≡ x ℤ* (y ℤ* z)
  ℤ*-assoc (+ 0) y z = refl
  ℤ*-assoc x (+ 0) z = subst₂ (λ x' x0 → x' ℤ* z ≡ x0) (sym (ℤ*-zero-r x)) (sym (ℤ*-zero-r x)) refl
  ℤ*-assoc x y (+ 0) = subst₂ (λ x' x0 → x' ≡ x ℤ* x0) (sym (ℤ*-zero-r (x ℤ* y))) (sym (ℤ*-zero-r y)) (sym (ℤ*-zero-r x)) 
  ℤ*-assoc -[1+ n ] -[1+ n' ] -[1+ n0 ] = cong -[1+_] (cong ℕp (tmp2 n n' n0))
  ℤ*-assoc -[1+ n ] -[1+ n' ] (+ ℕs n0) = cong (λ x → + x) (tmp2 n n' n0)
  ℤ*-assoc -[1+ n ] (+ ℕs n') -[1+ n0 ] = cong (λ x → + x) (tmp2 n n' n0)
  ℤ*-assoc -[1+ n ] (+ ℕs n') (+ ℕs n0) = cong -[1+_] (cong ℕp (tmp2 n n' n0))
  ℤ*-assoc (+ ℕs n) -[1+ n' ] -[1+ n0 ] =  cong (λ x → + x) (tmp2 n n' n0)
  ℤ*-assoc (+ ℕs n) -[1+ n' ] (+ ℕs n0) = cong -[1+_] (cong ℕp (tmp2 n n' n0))
  ℤ*-assoc (+ ℕs n) (+ ℕs n') -[1+ n0 ] = cong -[1+_] (cong ℕp (tmp2 n n' n0))
  ℤ*-assoc (+ ℕs n) (+ ℕs n') (+ ℕs n0) = cong (λ x → + x) (tmp2 n n' n0)

  identityˡ : (x : ℤ) → sign x ◃ ∣ x ∣ ℕ+ 0 ≡ x
  identityˡ -[1+ n ] = cong -[1+_] ((proj₂ ℕr.+-identity) n)
  identityˡ (+ zero) = refl
  identityˡ (+ ℕs n) = cong (λ x → + ℕs x) ((proj₂ ℕr.+-identity) n)

  distrib₁₁ : ∀ m n → m ℕ* (ℕs n) ≡ m ℕ+ m ℕ* n
  distrib₁₁ m n = subst₂ (λ x x' → x ≡ m ℕ+ x') (ℕr.*-comm (ℕs n) m) (ℕr.*-comm n m) refl

  distrib₁ : ∀ n y → y ℤ* + (ℕs n) ≡ y ℤ+ y ℤ* + n
  distrib₁ zero y = subst₂ (λ x x' → x ≡ y ℤ+ x') (sym (ℤ*-one-r y)) (sym (ℤ*-zero-r y)) (sym (ℤ+-zero-r y))
  distrib₁ (ℕs n) -[1+ n' ] with cong ℕp (distrib₁₁ (ℕs n') (ℕs n))
  ... | eq = cong -[1+_] (subst (λ x → x ≡ ℕs (n' ℕ+ (n ℕ+ n' ℕ* ℕs n))) (sym eq) (m+1+n≡1+m+n n' (n ℕ+ n' ℕ* ℕs n)))
  distrib₁ (ℕs n) (+ zero) = refl
  distrib₁ (ℕs n) (+ ℕs n') = cong (λ x → + x) (distrib₁₁ (ℕs n') (ℕs n))

  ℤ*-opp-r : ∀ m → m ℤ* -[1+ 0 ] ≡ - m
  ℤ*-opp-r -[1+ n ] = cong (λ x → + ℕs x) ((proj₂ ℕr.*-identity) n)
  ℤ*-opp-r (+ zero) = refl
  ℤ*-opp-r (+ ℕs n) = cong -[1+_] ((proj₂ ℕr.*-identity) n)

  distrib₂ : (r s t u : ℤ) → r ℤ+ s ℤ+ (t ℤ+ u) ≡ r ℤ+ t ℤ+ (s ℤ+ u)
  distrib₂ r s t u = subst₂ (λ x x' → x ≡ x') (ℤ+-assoc r s (t ℤ+ u)) (ℤ+-assoc r t (s ℤ+ u)) (ℤ+-left {r} (subst₂ (λ x x' → x ≡ x') (sym (ℤ+-assoc s t u)) (sym (ℤ+-assoc t s u)) (ℤ+-right (ℤ+-comm s t))))

  distrib₃ : ∀ m n → m ℤ* -[1+ ℕs n ] ≡ - m ℤ+ m ℤ* -[1+ n ]
  distrib₃ -[1+ n ] n' = cong (λ x → + x) (distrib₁₁ (ℕs n) (ℕs n'))
  distrib₃ (+ zero) n' = refl
  distrib₃ (+ ℕs n) n' = cong (-[1+_] ∘ ℕs) (subst (λ x → n' ℕ+ x ≡ n ℕ+ (n' ℕ+ n ℕ* ℕs n')) (sym (distrib₁₁ n (ℕs n'))) (subst (λ x → n' ℕ+ (n ℕ+ n ℕ* ℕs n') ≡ x) (ℕr.+-comm (n' ℕ+ n ℕ* ℕs n') n) (subst (λ x → n' ℕ+ (n ℕ+ n ℕ* ℕs n') ≡ x) (sym (ℕr.+-assoc n' (n ℕ* ℕs n') n)) (ℕ+-left {n'} (ℕr.+-comm n (n ℕ* ℕs n'))))))

  distrib : (x : ℤ) (y : ℤ) (z : ℤ) → (y ℤ+ z) ℤ* x ≡ y ℤ* x ℤ+ z ℤ* x 
  distrib -[1+ zero ] y z = subst₂ (λ x x' → (y ℤ+ z) ℤ* -[1+ 0 ] ≡ x ℤ+ x') (sym (ℤ*-opp-r y)) (sym (ℤ*-opp-r z)) (subst₂ (λ x x' → x ≡ x') (sym (ℤ*-opp-r (y ℤ+ z))) (-distr-ℤ+ y z) refl)
  distrib -[1+ ℕs n ] y z = subst₂ (λ x x' →  (y ℤ+ z) ℤ* -[1+ ℕs n ] ≡ x ℤ+ x') (sym (distrib₃ y n)) (sym (distrib₃ z n)) (subst (λ x → x ≡ - y ℤ+ y ℤ* -[1+ n ] ℤ+ (- z ℤ+ z ℤ* -[1+ n ])) (sym (distrib₃ (y ℤ+ z) n)) (subst₂ (λ x x' → x ℤ+ x' ≡ - y ℤ+ y ℤ* -[1+ n ] ℤ+ (- z ℤ+ z ℤ* -[1+ n ])) (sym (-distr-ℤ+ y z)) (sym (distrib -[1+ n ] y z)) (distrib₂ (- y) (- z) (y ℤ* -[1+ n ]) (z ℤ* -[1+ n ]))))
  distrib (+ zero) y z = subst₂ (λ x x' → (y ℤ+ z) ℤ* + zero ≡ x ℤ+ x') (sym (ℤ*-zero-r y)) (sym (ℤ*-zero-r z)) (ℤ*-zero-r (y ℤ+ z))
  distrib (+ ℕs n) y z = subst₂ (λ x x' → (y ℤ+ z) ℤ* + ℕs n ≡ x ℤ+ x') (sym (distrib₁ n y)) (sym (distrib₁ n z)) (subst (λ x → x ≡  y ℤ+ y ℤ* + n ℤ+ (z ℤ+ z ℤ* + n)) (sym (distrib₁ n (y ℤ+ z))) (subst (λ x → y ℤ+ z ℤ+ x ≡ y ℤ+ y ℤ* + n ℤ+ (z ℤ+ z ℤ* + n)) (sym (distrib (+ n) y z)) (distrib₂ y z (y ℤ* + n) (z ℤ* + n))))

  distrib' : (x : ℤ) (y : ℤ) (z : ℤ) → x ℤ* (y ℤ+ z) ≡ x ℤ* y ℤ+ x ℤ* z
  distrib' x y z = subst₂ (λ x' x0 →  x ℤ* (y ℤ+ z) ≡ x' ℤ+ x0) (ℤ*-comm y x) (ℤ*-comm z x) (subst (λ x' → x' ≡ y ℤ* x ℤ+ z ℤ* x) (ℤ*-comm (y ℤ+ z) x) (distrib x y z)) 

  integrity₁ : ∀ {m n} → + (ℕs m) ℤ* n ≡ + 0 → n ≡ + 0
  integrity₁ {m} { -[1+ n ]} ()
  integrity₁ {m} {+ zero} H = refl
  integrity₁ {m} {+ ℕs n} ()

  integrity₂ : ∀ {m n} → -[1+ m ] ℤ* n ≡ + 0 → n ≡ + 0
  integrity₂ {m} { -[1+ n ]} ()
  integrity₂ {m} {+ zero} H = refl
  integrity₂ {m} {+ ℕs n} ()

  integrity : ∀ {m n} → m ℤ* n ≡ + 0 → (m ≡ + 0 → ⊥) → n ≡ + 0
  integrity {m} { -[1+ n ]} hmn hm = ⊥-elim (hm (integrity₂ {n} (subst (λ x → x ≡ + 0) (ℤ*-comm m -[1+ n ]) hmn)))
  integrity {m} {+ zero} hmn hm = refl
  integrity {m} {+ ℕs n} hmn hm = ⊥-elim (hm (integrity₁ {n} (subst (λ x → x ≡ + 0) (ℤ*-comm m (+ ℕs n)) hmn)))