module Bset where

open import Representation
open import Properties
import Normalization.Linearization as Lin
open import AllmostFree-prop using (lcm-dvd)
import Minusinf as M

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_ ; _≤?_ to _ℕ≤?_ ; _≟_ to _ℕ≟_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_ ; _≤?_ to _ℤ≤?_ ; _≟_ to _ℤ≟_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

open import Product
import Data.List as L

open import Relation.Binary.PropositionalEquality

bset : ∀ {n} (φ : Unf n) → L.List (Lin′ n 1)
bset (.(((-[1+ 0 ] :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {n} {t} { -[1+ .0 ]} refl y')) with Lin.lin-plus (t , y') (val (-[1+ 0 ]) , val-islinn-i)
... | e = L.[_] e
bset (.((((+ 1) :* var zero) :+ t) le val (+ 0)) , le-isunitary (var0-isunit {n} {t} {+ .1} refl y')) = L.[]
bset (.(((-[1+ 0 ] :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {n} {t} { -[1+ .0 ]} refl y')) with Lin.lin-plus (t , y') (val (-[1+ 0 ]) , val-islinn-i)
... | e = L.[_] e
bset (.((((+ 1) :* var zero) :+ t) eq val (+ 0)) , eq-isunitary (var0-isunit {n} {t} {+ .1} refl y')) with Lin.lin-plus (Lin.lin-opp (t , y')) (val (-[1+ 0 ]) , val-islinn-i)
... | e = L.[_] e
bset (.(not (((-[1+ 0 ] :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {n} {t} { -[1+ .0 ]} refl y')) = L.[_] (t , y')
bset (.(not ((((+ 1) :* var zero) :+ t) eq val (+ 0))) , neq-isunitary (var0-isunit {n} {t} {+ .1} refl y')) with Lin.lin-opp (t , y')
... | e = L.[_] e
bset (.(φ₁ and φ₂) , and-isunitary {φ₁} {φ₂} y y') with bset (φ₁ , y) | bset (φ₂ , y')
... | l₁ | l₂ = L._++_ l₁ l₂
bset (.(φ₁ or φ₂) , or-isunitary {φ₁} {φ₂} y y') with bset (φ₁ , y) | bset (φ₂ , y')
... | l₁ | l₂ = L._++_ l₁ l₂
bset (_ , _) = L.[]

bjset : ∀ {n} {p} (φ : Unf n) (j : Fin p) → L.List (Lin′ n 1)
bjset φ j = L.map (λ u → Lin.lin-plus u (val (+ toℕ j) , val-islinn-i)) (bset φ)

δ-extract : ∀ {n} {φ : form n} (δ : Dall φ) → ℕ
δ-extract δ = ∣ proj₁ (proj₁ δ) ∣

my-δ : ∀ {n} (φ : Unf n) → ℕ
my-δ φ = δ-extract (lcm-dvd (M.minusinf φ))

jset : ∀ {n} (φ : Unf n) → ℕ
jset φ = ℕs (my-δ φ)