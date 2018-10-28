module Cooper.LinCooper where

open import Representation
open import Properties
open import Normalization.LCMReduction
open import Normalization.Unitarization
open import Cooper.UnfCooper

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

open import Data.Product as Prod

Lin-qelim : ∀ {n f} (φ : Lin {ℕ.suc n} f) → ∃ (Lin {n})
Lin-qelim φ = let ((σ , σ≠0) , divφ) = div φ in
              Unf-qelim (σ≠0 :| :+1 [ ∣+1∣ ]*var0+ val (ℤ.+ 0) :∧ proj₂ (unit divφ))
