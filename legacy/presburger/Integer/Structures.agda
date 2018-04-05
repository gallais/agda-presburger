module Integer.Structures where

open import Integer.Basic-Properties
open import Integer.Properties
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_)

open import Data.Product

open import Algebra
open import Algebra.Structures

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_ ; _≢_ ; refl ; sym ; cong ; cong₂ ; subst ; subst₂)
open import Relation.Binary.PropositionalEquality.Core using (isEquivalence)

abstract

-----
-- Semi Groups
-----
  ℤ+-isSemigroup : IsSemigroup _≡_ _ℤ+_
  ℤ+-isSemigroup = record {
    isEquivalence = isEquivalence;
    assoc = λ x y z → sym (ℤ+-assoc x y z);
    ∙-cong = ℤ+-cong}

  ℤ*-isSemigroup : IsSemigroup _≡_ _ℤ*_
  ℤ*-isSemigroup = record {
    isEquivalence = isEquivalence;
    assoc = ℤ*-assoc;
    ∙-cong = ℤ*-cong}

-----
-- Groups
-----

  ℤ+-isGroup : IsGroup _≡_ _ℤ+_ (+ 0) -_
  ℤ+-isGroup = record {
    isMonoid = record {
      isSemigroup = ℤ+-isSemigroup;
      identity = ℤ+-zero-l , ℤ+-zero-r};
    inverse = ℤ+-inv;
    ⁻¹-cong = ℤ--cong}

-----
-- Commutative Semi Rings
-----

  isCommutativeSemiring : IsCommutativeSemiring _≡_ _ℤ+_ _ℤ*_ (+ 0) (+ 1)
  isCommutativeSemiring = record {
    +-isCommutativeMonoid = record {
                          isSemigroup = ℤ+-isSemigroup;
                          identityˡ = ℤ+-zero-l;
                          comm = ℤ+-comm
                          };
    *-isCommutativeMonoid = record {
                          isSemigroup = ℤ*-isSemigroup;
                          identityˡ = identityˡ;
                          comm = ℤ*-comm};
    distribʳ = distrib;
    zeroˡ = λ _ → refl}

-----
-- Commutative Rings
-----

  isCommutativeRing : IsCommutativeRing _≡_ _ℤ+_ _ℤ*_ -_ (+ 0) (+ 1)
  isCommutativeRing = record {
    isRing = record {
           +-isAbelianGroup = record {
                            isGroup = ℤ+-isGroup;
                            comm = ℤ+-comm};
           *-isMonoid = record {
                      isSemigroup = ℤ*-isSemigroup;
                      identity = ℤ*-one-l , ℤ*-one-r};
                      distrib = distrib' , distrib};
           *-comm = ℤ*-comm}

  ℤ+*-CommutativeRing : CommutativeRing _ _
  ℤ+*-CommutativeRing = record{
    Carrier = ℤ;
    _≈_ = _≡_;
    _+_ = _ℤ+_;
    _*_ = _ℤ*_;
    -_ = -_;
    0# = + 0;
    1# = + 1;
    isCommutativeRing = isCommutativeRing}