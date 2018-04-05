module Cooper.NnfCooper-prop where

open import Product
open import Equivalence

open import Representation
open import Properties
open import Properties-prop
open import Semantics

import Normalization.Linearization as Lin
import Normalization.Linearization-prop as Linp
import Cooper.LinCooper as LC
import Cooper.LinCooper-prop as LCp
import Cooper.NnfCooper as NC

import Data.Nat as Nat
open import Data.Integer
import Data.Vec as V
import Data.Product as P

abstract
  Nnf-cooper : ∀ {n} (φ : Nnf (Nat.suc n)) →
             ex (proj₁ φ) ⇔ proj₁ (NC.Nnf-qelim φ)
  Nnf-cooper φ ρ with (λ (x : ℤ) → Linp.lin-sem φ (V._∷_ x ρ)) | LC.Lin-qelim (Lin.lin φ) | LCp.Lin-cooper (Lin.lin φ) ρ
  ... | λPQ | ψ , Hψ | P._,_ P₂ Q₂ = P._,_ (λ H → P₂ (P._,_ (P.proj₁ H) (P.proj₁ (λPQ (P.proj₁ H)) (P.proj₂ H)))) (λ H → P._,_ (P.proj₁ (Q₂ H)) (P.proj₂ (λPQ (P.proj₁ (Q₂ H))) (P.proj₂ (Q₂ H))))