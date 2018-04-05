module Cooper.LinCooper where

open import Representation
import Properties as Pr
import Normalization.Unitarization as Uni
import Cooper.UnfCooper as UC

open import Data.Nat as Nat
open import Data.Integer using (+_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

open import Product
import Data.Product as P using (_,_)

open import Relation.Binary.PropositionalEquality using (refl)

Lin-qelim : ∀ {n} (φ : Pr.Lin (Nat.suc n)) → Pr.Lin n
Lin-qelim φ with Uni.lcmφ φ | Uni.unitarise φ
... | P._,_ (l , neq) Hl | ψ , Hψ = UC.Unf-qelim (((l dvd (((+ 1) :* var zero) :+ val (+ 0))) and ψ) , Pr.and-isunitary (Pr.dvd-isunitary neq (Pr.var0-isunit refl Pr.val-islinn-i)) Hψ)