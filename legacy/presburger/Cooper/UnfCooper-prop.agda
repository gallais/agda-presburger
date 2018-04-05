module Cooper.UnfCooper-prop where

import Cooper.UnfCooper as UC
open import Representation
open import Properties
open import Properties-prop using (isunitary-islin ; islin-isnnf)
open import Semantics
open import Equivalence using (_↔_ ; _←_ ; _⇔_)

import Normalization.Linearization as Lin
import Normalization.Linearization-prop as Linp
open import AllmostFree-prop using (lcm-dvd ; Af0-Fin-reduc)
open import Disjunction using (Finite-disjunction′ ; Fin-dij)
open import Disjunction-prop using (Finite-disjunction′-sem ; Fin-dij-sem)
import Bset as BS
open import Cooper using (cooper₁-simpl)
import Minusinf as M
import Decidability as D
import List-tools as Lt -- (b∈-Lmap-compat)
import Fin-prop as F -- (allFin-inv)

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_ ; _≤?_ to _ℕ≤?_ ; _≟_ to _ℕ≟_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_ ; _≤?_ to _ℤ≤?_ ; _≟_ to _ℤ≟_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

import Data.Product as P
open import Product
open import Data.Sum using (_⊎_ ; [_,_]′ ; inj₁ ; inj₂)
import Data.Vec as V --renaming (map to Vmap)
import Data.List as L --using () renaming (map to Lmap ; _∷_ to _L∷_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

abstract

  private
    pre-Unf-cooper-l : ∀ {n} (φ : Unf (ℕs n)) (ρ : V.Vec ℤ n) → P.∃ (λ x → [| proj₁ φ |] (V._∷_ x ρ)) →
         (P.∃ (λ j → [| proj₁ (UC.Unf-qelim-l₁ φ j) |] ρ) ⊎ P.∃ (λ u → [| proj₁ (M.minusinf φ) |] (V._∷_ u ρ)))
    pre-Unf-cooper-l φ ρ H with D.Fin-dec {BS.jset φ} (λ j → D.Nnf-dec ((proj₁ (Finite-disjunction′ (proj₁ φ , isunitary-islin (proj₂ φ)) (BS.bjset φ j))) , (islin-isnnf (proj₂ (Finite-disjunction′ (proj₁ φ , isunitary-islin (proj₂ φ)) (BS.bjset φ j))))) ρ)
    ... | yes P = inj₁ P
    ... | no ¬P = inj₂ (cooper₁-simpl φ ρ (λ h → ¬P (P._,_ (P.proj₁ h) (P.proj₂ (Finite-disjunction′-sem (proj₁ φ , isunitary-islin (proj₂ φ)) (BS.bjset φ (P.proj₁ h)) ρ) (P.proj₁ (Lt.b∈-Lmap-compat (λ b → [| proj₁ φ |] (V._∷_ ([| proj₁ b |]e (V._∷_ (+ 0) ρ)) ρ)) (λ u → Lin.lin-plus u (val (+ toℕ (P.proj₁ h)) , val-islinn-i)) (BS.bset φ)) (P._,_ (P.proj₁ (P.proj₂ h)) (P._,_ (P.proj₁ (P.proj₂ (P.proj₂ h))) (subst (λ u → [| proj₁ φ |] (V._∷_ u ρ)) (Linp.lin-plus-sem (P.proj₁ (P.proj₂ h)) (val (+ toℕ (P.proj₁ h)) , val-islinn-i) (V._∷_ (+ 0) ρ)) (P.proj₂ (P.proj₂ (P.proj₂ h)))))))))) (P.proj₁ H) (P.proj₂ H))

    pre-Unf-cooper-r : ∀ {n} (φ : Unf (ℕs n)) (ρ : V.Vec ℤ n) → P.∃ (λ x → [| proj₁ φ |] (V._∷_ x ρ)) ← (P.∃ (λ j → [| proj₁ (UC.Unf-qelim-l₁ φ j) |] ρ) ⊎ P.∃ (λ u → [| proj₁ (M.minusinf φ) |] (V._∷_ u ρ)))
    pre-Unf-cooper-r φ ρ with (λ (j : Fin (BS.jset φ)) → Finite-disjunction′-sem (proj₁ φ , isunitary-islin (proj₂ φ)) (BS.bjset φ j) ρ)
    ... | λPQ = [ (λ J → P._,_ _ (P.proj₂ (P.proj₂ (P.proj₁ (λPQ (P.proj₁ J)) (P.proj₂ J))))) , (λ h → M.cooper₂-simpl φ ρ (P.proj₁ h) (P.proj₂ h)) ]′

    pre-Unf-cooper : ∀ {n} (φ : Unf (ℕs n)) (ρ : V.Vec ℤ n) →
                   P.∃ (λ x → [| proj₁ φ |] (V._∷_ x ρ)) ↔ (P.∃ (λ (j : Fin (BS.jset φ)) → [| proj₁ (UC.Unf-qelim-l₁ φ j) |] ρ) ⊎ P.∃ (λ u → [| proj₁ (M.minusinf φ) |] (V._∷_ u ρ)))
    pre-Unf-cooper φ ρ = P._,_ (pre-Unf-cooper-l φ ρ) (pre-Unf-cooper-r φ ρ)


    pre-Unf-cooper₂ : ∀ {n} (φ : Unf (ℕs n)) → ex (proj₁ φ) ⇔ (proj₁ (UC.Unf-qelim-l φ)) or (ex (proj₁ (M.minusinf φ)))
    pre-Unf-cooper₂ φ ρ = P._,_ (λ h → [ (λ hyp → inj₁ (P.proj₂ (Fin-dij-sem (UC.Unf-qelim-l₁ φ) (V.allFin (BS.jset φ)) ρ) (P._,_ (P.proj₁ hyp) (subst (λ u → [| proj₁ (Finite-disjunction′ (proj₁ φ , isunitary-islin (proj₂ φ)) (BS.bjset φ u)) |] ρ) (sym (F.allFin-inv (P.proj₁ hyp))) (P.proj₂ hyp))))) , inj₂ ]′ (P.proj₁ (pre-Unf-cooper φ ρ) h)) [ (λ h → P.proj₂ (pre-Unf-cooper φ ρ) (inj₁ (P._,_ (P.proj₁ (P.proj₁ (Fin-dij-sem (UC.Unf-qelim-l₁ φ) (V.allFin (BS.jset φ)) ρ) h)) (subst (λ u → [| proj₁ (UC.Unf-qelim-l₁ φ u) |] ρ) (F.allFin-inv (P.proj₁ (P.proj₁ (Fin-dij-sem (UC.Unf-qelim-l₁ φ) (V.allFin (BS.jset φ)) ρ) h))) (P.proj₂ (P.proj₁ (Fin-dij-sem (UC.Unf-qelim-l₁ φ) (V.allFin (BS.jset φ)) ρ) h)))))) , (λ h → P.proj₂ (pre-Unf-cooper φ ρ) (inj₂ h)) ]′

  Unf-cooper : ∀ {n} (φ : Unf (ℕs n)) → ex (proj₁ φ) ⇔ proj₁ (UC.Unf-qelim φ)
  Unf-cooper φ ρ with UC.Unf-qelim-l φ | UC.Unf-qelim-r φ | Af0-Fin-reduc (M.minusinf φ) (lcm-dvd (M.minusinf φ)) ρ | pre-Unf-cooper₂ φ ρ
  ... | ψ₁ , H₁ | ψ₂ , H₂ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂  = P._,_ (λ h → [ inj₁ , (λ x → inj₂ (P₁ x)) ]′ (P₂ h)) [ (λ x → Q₂ (inj₁ x)) , (λ x → Q₂ (inj₂ (Q₁ x))) ]′