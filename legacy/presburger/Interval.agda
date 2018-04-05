module Interval where

open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Fin as F
open import Data.Vec
open import Product
open import Fin-prop

open import Relation.Binary.PropositionalEquality
open import Equivalence

open import Relation.Binary

interval : ℤ → ℕ → ℤ → Set
interval lb size x = ∃ (λ (k : Fin size) → x ≡ lb ℤ.+ (+ (toℕ k)))

Interval : ℤ → (n : ℕ) → Vec ℤ n
Interval z zero = []
Interval z (ℕ.suc n) = (z ℤ.+ (+ n)) ∷ (Interval z n)

lookup-Interval : ∀ (z : ℤ) (d : ℕ) (p : Fin d) →
                  lookup p (Interval z d) ≡ z ℤ.+ (d ⊖ (toℕ (F.suc p)))
lookup-Interval z zero ()
lookup-Interval z (ℕ.suc n) zero = refl
lookup-Interval z (ℕ.suc n) (F.suc i) = lookup-Interval z n i

Interval-sem : ∀ (P : ℤ → Set) z d →
               ∃ (λ (x : Fin d) → P (z ℤ.+ (+ toℕ x))) ↔ ∃ (λ x → P (lookup x (Interval z d)))
Interval-sem P z d =
  [ ∃ (λ (x : Fin d) → P (z ℤ.+ (+ toℕ x))) ]⤇[ ∃ (λ x → P (lookup x (Interval z d))) ]

  Given (Fin d) compute (Fin d) by Fin-inv
  andprove (λ (c : Fin d) → P (lookup c (Interval z d)))
  assuming (λ (a : Fin d) → P (z ℤ.+ (+ toℕ a)))
  by (λ a Pa →
     subst P (sym (lookup-Interval z d (Fin-inv a)))
     (subst (λ a → P (z ℤ.+ a)) (trans (cong (λ z → + toℕ z) (sym (Fin-inv-invol a)))
                                       (Fin-inv-sem (Fin-inv a))) Pa))

  ■[ ∃ (λ (x : Fin d) → P (z ℤ.+ (+ toℕ x))) ]⤆[ ∃ (λ x → P (lookup x (Interval z d))) ]

  Given (Fin d) compute (Fin d) by Fin-inv
  andprove (λ c → P (z ℤ.+ + toℕ c))
  assuming (λ a → P (lookup a (Interval z d)))
  by (λ a Pa →
     subst (λ k → P (z ℤ.+ k)) (sym (Fin-inv-sem a)) (subst P (lookup-Interval z d a) Pa))

  ■