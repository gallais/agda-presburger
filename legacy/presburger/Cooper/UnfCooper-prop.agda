module Cooper.UnfCooper-prop where

open import Representation
open import Properties
open import Semantics
open import Equivalence
open import AllmostFree-prop
open import Minusinf
open import Cooper.UnfCooper

open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)

open import Function


-- pre-Unf-cooper₂ : ∀ {n} (φ : Unf (ℕs n)) →
--   ex (proj₁ φ) ⇔ (proj₁ (UC.Unf-qelim-l φ)) or (ex (proj₁ (M.minusinf φ)))

⟦Unf-qelim-l_⟧ : ∀ {n f} (φ : Unit {ℕ.suc n} f) →
                 :∃ f ⇔ (proj₁ (Unf-qelim-l φ) :∨ (:∃ proj₁ (var0⟶-∞ φ)))
⟦Unf-qelim-l φ ⟧ ρ = {!!}


⟦Unf-qelim_⟧ : ∀ {n f} (φ : Unit {ℕ.suc n} f) → :∃ f ⇔ proj₁ (Unf-qelim φ)
⟦Unf-qelim φ ⟧ ρ =
  let (f^-∞ , φ^-∞) = var0⟶-∞ φ
      (σ , divφ^-∞) = lcm-:∣′ φ^-∞
      (p₁ , q₁) = ⟦⋁ φ^-∞ when σ :| divφ^-∞ ⟧ ρ
      (p₂ , q₂) = ⟦Unf-qelim-l φ ⟧ ρ
  in Sum.map₂ p₁ ∘′ p₂
   , [ q₂ ∘′ inj₁ , q₂ ∘′ inj₂ ∘′ q₁ ]′

{-


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