module Interval where

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ZProp

open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FProp
open import Data.Product

open import Function
open import Relation.Binary.PropositionalEquality

interval : ℤ → ℕ → ℤ → Set
interval lb size v = ∃ λ (k : Fin (ℕ.suc size)) → lb ℤ.+ (ℤ.+ Fin.toℕ k) ≡ v

bounded⇒interval : ∀ {v x y} → x ℤ.≤ v → v ℤ.≤ y → interval x ℤ.∣ y ℤ.- x ∣ v
bounded⇒interval {v} {x} {y} x≤v v≤y = k , x+k≡v where

  size = y ℤ.- x
  dist = v ℤ.- x

  0≤size : ℤ.+ 0 ℤ.≤ size
  0≤size = begin
    ℤ.+ 0       ≡⟨ sym (ZProp.+-inverseʳ x) ⟩
    x ℤ.+ ℤ.- x ≤⟨ ZProp.+-monoˡ-≤ (ℤ.- x) (ZProp.≤-trans x≤v v≤y) ⟩
    size        ∎ where open ZProp.≤-Reasoning

  0≤dist : ℤ.+ 0 ℤ.≤ dist
  0≤dist = begin
    ℤ.+ 0   ≡⟨ sym (ZProp.+-inverseʳ x) ⟩
    x ℤ.- x ≤⟨ ZProp.+-monoˡ-≤ (ℤ.- x) x≤v ⟩
    dist    ∎ where open ZProp.≤-Reasoning

  ∣dist∣<1+size : ℤ.∣ dist ∣ ℕ.< ℕ.suc ℤ.∣ size ∣
  ∣dist∣<1+size = ℕ.s≤s $ ZProp.drop‿+≤+ $ begin
    ℤ.+ ℤ.∣ v ℤ.+ ℤ.- x ∣ ≡⟨ ZProp.0≤n⇒+∣n∣≡n 0≤dist ⟩
    dist                  ≤⟨ ZProp.+-monoˡ-≤ (ℤ.- x) v≤y ⟩
    size                  ≡⟨ sym (ZProp.0≤n⇒+∣n∣≡n 0≤size) ⟩
    ℤ.+ ℤ.∣ y ℤ.+ ℤ.- x ∣ ∎ where open ZProp.≤-Reasoning

  k = Fin.fromℕ< ∣dist∣<1+size

  x+k≡v : x ℤ.+ ℤ.+ Fin.toℕ k ≡ v
  x+k≡v = begin
    x ℤ.+ ℤ.+ (Fin.toℕ k) ≡⟨ cong (ℤ._+_ x ∘′ ℤ.+_) (FProp.toℕ-fromℕ< ∣dist∣<1+size) ⟩
    x ℤ.+ ℤ.+ ℤ.∣ dist ∣  ≡⟨ cong (ℤ._+_ x) (ZProp.0≤n⇒+∣n∣≡n 0≤dist) ⟩
    x ℤ.+ dist            ≡⟨ ZProp.+-comm x (v ℤ.- x) ⟩
    v ℤ.- x ℤ.+ x         ≡⟨ ZProp.+-assoc v (ℤ.- x) x ⟩
    v ℤ.+ (ℤ.- x ℤ.+ x)   ≡⟨ cong (ℤ._+_ v) (ZProp.+-inverseˡ x) ⟩
    v ℤ.+ ℤ.+ 0           ≡⟨ ZProp.+-identityʳ v ⟩
    v ∎ where open ≡-Reasoning
