module integer.order where

open import Data.Nat as ℕ
open import Data.Integer as ℤ

-<+ : ∀ m n → ℤ.suc -[1+ m ] ℤ.≤ + n
-<+ zero n = +≤+ z≤n
-<+ (ℕ.suc m) n = -≤+

-< : ∀ {m n} (lt : ℕ.suc m ℕ.≤ n) → ℤ.suc -[1+ n ] ℤ.≤ -[1+ m ]
-< (s≤s lt) = -≤- lt

n≤sn : ∀ n → n ℕ.≤ ℕ.suc n
n≤sn zero = z≤n
n≤sn (ℕ.suc n) = s≤s (n≤sn n)

z≤sz : ∀ z → z ℤ.≤ ℤ.suc z
z≤sz -[1+ zero ] = -≤+
z≤sz -[1+ ℕ.suc n ] = -≤- (n≤sn n)
z≤sz (+ n) = +≤+ (n≤sn n)