module Cooper where

open import Representation
open import Properties
open import Properties-prop
open import Normalization.Linearisation
open import Normalization.Linearisation-prop
open import Semantics
open import Semantics-prop
open import Equivalence
open import Minusinf
open import AllmostFree-prop
open import Bset
open import Interval

open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties

open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as NProp

open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ZProp
import Data.Integer.Divisibility.Properties as ZdivProp
import Algebra.Properties.Ring ZProp.+-*-ring as APR

open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FProp

open import Data.Empty
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Vec

open import Function
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

step-cooper₁ :
  ∀ {n f σ} (φ : Unit {ℕ.suc n} f) (divφ : All∣′ σ f) x ρ →
  (¬H : ¬ (Σ (Fin (ℕ.suc ℤ.∣ proj₁ σ ∣) × ∃ (Lin-E 1)) $ uncurry λ j b →
             b ∈ (bset φ)
           × (x ≡ (⟦ proj₁ b ⟧e ((ℤ.+ 0) ∷ ρ)) ℤ.+ (ℤ.+ Fin.toℕ j)))) →
  ⟦ f ⟧ (x ∷ ρ) → ⟦ f ⟧ (x ℤ.- ℤ.+ ℤ.∣ proj₁ σ ∣ ∷ ρ)
step-cooper₁ T divφ x ρ ¬H = _
step-cooper₁ F divφ x ρ ¬H = id
-- :≤0
step-cooper₁ (val k :≤0) divφ x ρ ¬H = id
step-cooper₁ {σ = σ , _} (varn p + e :≤0) divφ x ρ ¬H pr = begin
  let t = toExp (Lin-E (ℕ.suc p)) e; x-∣σ∣ = x ℤ.- ℤ.+ ℤ.∣ σ ∣ in
  ⟦ t ⟧e (x-∣σ∣ ∷ ρ) ≡⟨ lin-ext₁ e x-∣σ∣ x ρ ⟩
  ⟦ t ⟧e (x ∷ ρ)     ≤⟨ pr ⟩
  ℤ.+ 0              ∎ where open ZProp.≤-Reasoning
step-cooper₁ {σ = σ , _} (:+1 [ ∣+1∣ ]*var0+ e :≤0) divφ x ρ ¬H pr = begin
  let t = toExp (Lin-E 1) e; ⟦t⟧ = λ x → ⟦ t ⟧e (x ∷ ρ)
      x' = ℤ.+ 1 ℤ.* x; x-∣σ∣ = x ℤ.- ℤ.+ ℤ.∣ σ ∣ in
  ℤ.+ 1 ℤ.* x-∣σ∣ ℤ.+ ⟦t⟧ x-∣σ∣
    ≤⟨ ZProp.+-monoˡ-≤ (⟦t⟧ x-∣σ∣) $ ZProp.*-monoˡ-≤-pos 0 $ ZProp.m-n≤m x ℤ.∣ σ ∣ ⟩
  x' ℤ.+ ⟦t⟧ x-∣σ∣
    ≡⟨ cong (ℤ._+_ x') (lin-ext₁ e x-∣σ∣ x ρ) ⟩
  x' ℤ.+ ⟦t⟧ x
    ≤⟨ pr ⟩
  ℤ.+ 0
    ∎ where open ZProp.≤-Reasoning
step-cooper₁ {σ = σ , σ≠0} (:-1 [ ∣-1∣ ]*var0+ e :≤0) divφ x ρ ¬H pr
  with ℤ.- x ℤ.+ ℤ.+ ℤ.∣ σ ∣ ℤ.+ ⟦ toExp (Lin-E 1) e ⟧e (x ∷ ρ) ZProp.≤? :+0
... | yes le = begin
  :-1 ℤ.* x-∣σ∣ ℤ.+ ⟦t⟧ x-∣σ∣
    ≡⟨ cong₂ ℤ._+_ (ZProp.*-distribˡ-+ :-1 x -∣σ∣) (lin-ext₁ e x-∣σ∣ x ρ) ⟩
  :-1 ℤ.* x ℤ.+ :-1 ℤ.* -∣σ∣ ℤ.+ ⟦t⟧ x
    ≡⟨ cong₂ (λ m n → m ℤ.+ n ℤ.+ ⟦t⟧ x) (ZProp.-1*n≡-n x) (ZProp.-1*n≡-n -∣σ∣) ⟩
  ℤ.- x ℤ.+ ℤ.- -∣σ∣ ℤ.+ ⟦t⟧ x
    ≡⟨ cong (λ t →   ℤ.- x ℤ.+ t ℤ.+ ⟦t⟧ x) (ZProp.neg-involutive +∣σ∣) ⟩
  ℤ.- x ℤ.+ +∣σ∣ ℤ.+ ⟦t⟧ x
    ≤⟨ le ⟩
  :+0 ∎ where

  open ZProp.≤-Reasoning
  +∣σ∣  = ℤ.+ ℤ.∣ σ ∣
  -∣σ∣  = ℤ.- +∣σ∣
  x-∣σ∣ = x ℤ.+ -∣σ∣
  t     = toExp (Lin-E 1) e
  ⟦t⟧   = λ x → ⟦ t ⟧e (x ∷ ρ)

... | no ¬le = ⊥-elim $ ¬H ((j , e +E val :-1) , here refl , ⋯-x≡0) where

   lt   = ZProp.≰→> ¬le
   t    = toExp (Lin-E 1) e
   -x   = ℤ.- x
   +∣σ∣ = ℤ.+ ℤ.∣ σ ∣
   ⟦t⟧  = λ x → ⟦ t ⟧e (x ∷ ρ)
   e-1  = e +E val :-1

   bd = :-1 ℤ.+ (-x ℤ.+ ⟦t⟧ x)

   eq  : :-1 ℤ.+ (-x ℤ.+ +∣σ∣ ℤ.+ ⟦t⟧ x) ℤ.- bd ≡ ℤ.+ ℤ.∣ σ ∣
   eq = begin let exp = :-1 ℤ.+ (-x ℤ.+ ⟦t⟧ x) in
     :-1 ℤ.+ (-x ℤ.+ +∣σ∣ ℤ.+ ⟦t⟧ x) ℤ.- exp
       ≡⟨ cong (ℤ._- exp) (sym (ZProp.+-assoc :-1 (-x ℤ.+ +∣σ∣) (⟦t⟧ x))) ⟩
     :-1 ℤ.+ (-x ℤ.+ +∣σ∣) ℤ.+ ⟦t⟧ x ℤ.- exp
       ≡⟨ cong (λ e → :-1 ℤ.+ e ℤ.+ ⟦t⟧ x ℤ.- exp) (ZProp.+-comm -x +∣σ∣) ⟩
     :-1 ℤ.+ (+∣σ∣ ℤ.+ -x) ℤ.+ ⟦t⟧ x ℤ.- exp
       ≡⟨ cong (λ e → e ℤ.+ ⟦t⟧ x ℤ.- exp) (sym (ZProp.+-assoc :-1 +∣σ∣ -x)) ⟩
     :-1 ℤ.+ +∣σ∣ ℤ.+ -x ℤ.+ ⟦t⟧ x ℤ.- exp
       ≡⟨ cong (λ e → e ℤ.+ -x ℤ.+ ⟦t⟧ x ℤ.- exp) (ZProp.+-comm :-1 +∣σ∣) ⟩
     +∣σ∣ ℤ.+ :-1 ℤ.+ -x ℤ.+ ⟦t⟧ x ℤ.- exp
       ≡⟨ cong (ℤ._- exp) (ZProp.+-assoc (+∣σ∣ ℤ.+ :-1) -x (⟦t⟧ x)) ⟩
     +∣σ∣ ℤ.+ :-1 ℤ.+ (-x ℤ.+ ⟦t⟧ x) ℤ.- exp
       ≡⟨ cong (ℤ._- exp) (ZProp.+-assoc +∣σ∣ :-1 (-x ℤ.+ ⟦t⟧ x)) ⟩
     +∣σ∣ ℤ.+ exp ℤ.- exp
       ≡⟨ ZProp.+-assoc +∣σ∣ exp (ℤ.- exp) ⟩
     +∣σ∣ ℤ.+ (exp ℤ.- exp)
       ≡⟨ cong (ℤ._+_ +∣σ∣) (ZProp.+-inverseʳ exp) ⟩
     +∣σ∣ ℤ.+ :+0
       ≡⟨ ZProp.+-identityʳ +∣σ∣ ⟩
     +∣σ∣
       ∎ where open ≡-Reasoning

   lb : bd ℤ.≤ :+0
   lb = let ctxt = cong (λ a → :-1 ℤ.+ (a ℤ.+ ⟦t⟧ x)) in begin
     :-1 ℤ.+ (-x ℤ.+ ⟦t⟧ x)        ≡⟨ ctxt (sym (ZProp.-1*n≡-n x)) ⟩
     :-1 ℤ.+ (:-1 ℤ.* x ℤ.+ ⟦t⟧ x) ≤⟨ ZProp.+-monoʳ-≤ :-1 pr ⟩
     :-1                           ≤⟨ ℤ.-≤+ ⟩
     :+0                           ∎ where open ZProp.≤-Reasoning

   ub : :+0 ℤ.≤ :-1 ℤ.+ (-x ℤ.+ +∣σ∣ ℤ.+ ⟦t⟧ x)
   ub = ZProp.+-monoʳ-≤ :-1 lt

   int = bounded⇒interval lb ub

   k = proj₁ int
   j = Fin.cast (cong ℕ.suc (cong ℤ.∣_∣ eq)) k

   hyp : -x ℤ.+ (:-1 ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ k) ≡ :+0
   hyp = begin
     -x ℤ.+ (:-1 ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ k)
       ≡⟨ sym (ZProp.+-assoc -x (:-1 ℤ.+ ⟦t⟧ x) (ℤ.+ Fin.toℕ k)) ⟩
     -x ℤ.+ (:-1 ℤ.+ ⟦t⟧ x) ℤ.+ ℤ.+ Fin.toℕ k
       ≡⟨ cong (ℤ._+ ℤ.+ Fin.toℕ k) (sym (ZProp.+-assoc -x :-1 (⟦t⟧ x))) ⟩
     -x ℤ.+ :-1 ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ k
       ≡⟨ cong (λ e → e ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ k) (ZProp.+-comm -x :-1) ⟩
     :-1 ℤ.+ -x ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ k
       ≡⟨ cong (ℤ._+ ℤ.+ Fin.toℕ k) (ZProp.+-assoc :-1 -x (⟦t⟧ x)) ⟩
     :-1 ℤ.+ (-x ℤ.+ ⟦t⟧ x) ℤ.+ ℤ.+ Fin.toℕ k
       ≡⟨ proj₂ int ⟩
     :+0 ∎ where open ≡-Reasoning

   ⋯-x≡0 : x ≡ ⟦ proj₁ e-1 ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ Fin.toℕ j
   ⋯-x≡0 = begin
     x
       ≡⟨ sym (ZProp.neg-involutive x) ⟩
     ℤ.- (ℤ.- x)
       ≡⟨ cong ℤ.-_ (APR.+-left-inverse-unique _ _ hyp) ⟩
     ℤ.- (ℤ.- (:-1 ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ k))
       ≡⟨ ZProp.neg-involutive _ ⟩
     :-1 ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ k
       ≡⟨ cong (ℤ._+ ℤ.+ Fin.toℕ k) (ZProp.+-comm :-1 (⟦t⟧ x)) ⟩
     ⟦t⟧ x ℤ.+ :-1 ℤ.+ ℤ.+ Fin.toℕ k
       ≡⟨ cong (λ e → e ℤ.+ :-1 ℤ.+ ℤ.+ Fin.toℕ k) (lin-ext₁ e x :+0 ρ) ⟩
     ⟦t⟧ :+0 ℤ.+ :-1 ℤ.+ ℤ.+ Fin.toℕ k
       ≡⟨ cong (λ e → ⟦t⟧ :+0 ℤ.+ :-1 ℤ.+ ℤ.+ e) (sym (FProp.toℕ-cast _ k)) ⟩
     ⟦t⟧ :+0 ℤ.+ :-1 ℤ.+ ℤ.+ Fin.toℕ j
       ≡⟨ cong (ℤ._+ ℤ.+ Fin.toℕ j) (⟦ e ⟧+E⟦ val :-1 ⟧ (:+0 ∷ ρ)) ⟩
     ⟦ proj₁ e-1 ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ Fin.toℕ j
       ∎ where open ≡-Reasoning

{-
   ⋯-x≡0 : ⟦t⟧ x ℤ.+ (ℤ.+ Fin.toℕ j) ℤ.- x ≡ ℤ.+ 0
   ⋯-x≡0 = begin
     ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ j ℤ.- x
       ≡⟨ ZProp.+-comm (⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ j) (ℤ.- x) ⟩
     ℤ.- x ℤ.+ (⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ j)
       ≡⟨ sym (ZProp.+-assoc (ℤ.- x) (⟦t⟧ x) (ℤ.+ Fin.toℕ j)) ⟩
     ℤ.- x ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ j
       ≡⟨ cong₂ (λ a b → a ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ b)
                (sym (ZProp.-1*n≡-n x))
                (FProp.toℕ-cast (cong ℕ.suc $ cong ℤ.∣_∣ eq) k) ⟩
     :-1 ℤ.* x ℤ.+ ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ k
       ≡⟨ proj₂ int ⟩
     ℤ.+ 0 ∎ where open ≡-Reasoning

   x≡⋯ : x ≡ ⟦ proj₁ e-1 ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ Fin.toℕ j
   x≡⋯ = begin
     x ≡⟨ sym (ZProp.m-n≡0⇒m≡n (⟦t⟧ x ℤ.+ (ℤ.+ Fin.toℕ j)) x ⋯-x≡0) ⟩
     ⟦t⟧ x ℤ.+ ℤ.+ Fin.toℕ j ≡⟨ {!!} ⟩
     {!!} ≡⟨ {!!} ⟩
     ⟦t⟧ :+0 ℤ.+ :-1 ℤ.+ ℤ.+ Fin.toℕ j
       ≡⟨ cong (ℤ._+ ℤ.+ Fin.toℕ j) (⟦ e ⟧+E⟦ val :-1 ⟧ (:+0 ∷ ρ)) ⟩
     ⟦ proj₁ e-1 ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ Fin.toℕ j ∎ where open ≡-Reasoning


-}
{- 
  ... | P._,_ j Hj with  lin-plus (t , y') (val -[1+ 0 ] , val-islinn-i) | lin-plus-sem (t , y') (val -[1+ 0 ] , val-islinn-i) (+ 0 ● ρ)
  ... | e | Heq = ⊥-elim

  (¬H (P._,_ j
      (P._,_ e
     (P._,_ here
    (subst (λ u → x ≡ u ℤ+ + toℕ j) Heq
    (tmp (subst (λ u → - x ℤ+ (u ℤ+ + toℕ j) ≡ + 0)
    (unfold-ℤ- ([| t |]e (+ 0 ●  ρ)) (+ 1))
     (subst₂ (λ u v → - x ℤ+ (u ℤ- + 1 ℤ+ + toℕ j) ≡ v)
     (context-simpl (t , y') x (+ 0) ρ) Hj
     (sym (ℤr.+-assoc (- x) ([| t |]e (x ● ρ) ℤ- + 1) (+ toℕ j)))))))))))

-}
-- :≡0
step-cooper₁ (val k :≡0) divφ x ρ ¬H = id
step-cooper₁ {σ = σ , _} (varn p + e        :≡0) divφ x ρ ¬H pr = begin
  let t = toExp (Lin-E (ℕ.suc p)) e; x-∣σ∣ = x ℤ.- ℤ.+ ℤ.∣ σ ∣ in
  ⟦ t ⟧e (x-∣σ∣ ∷ ρ) ≡⟨ lin-ext₁ e x-∣σ∣ x ρ ⟩
  ⟦ t ⟧e (x ∷ ρ)     ≡⟨ pr ⟩
  ℤ.+ 0              ∎ where open ≡-Reasoning
step-cooper₁ {σ = σ , σ≠0} (:+1 [ ∣+1∣ ]*var0+ e :≡0) divφ x ρ ¬H pr
  with ℤ.∣ σ ∣ | [∣ σ≠0 ∣≠0]
... | ℕ.suc k | +[1+ k ] = ⊥-elim $′ ¬H ((Fin.suc Fin.zero , _) , here refl , eq) where

  t    = toExp (Lin-E 1) e
  -e   = -E e
  -e-1 = proj₂ -e +E val :-1

  ⟦-e⟧ = λ x → ⟦ proj₁ -e ⟧e (x ∷ ρ)

  eq : x ≡ ⟦ proj₁ -e-1 ⟧e (ℤ.+ 0 ∷ ρ) ℤ.+ ℤ.+ 1
  eq = begin
    x                        ≡⟨ sym (ZProp.*-identityˡ x) ⟩
    ℤ.+ 1 ℤ.* x              ≡⟨ APR.+-left-inverse-unique _ _ pr ⟩
    ℤ.- ⟦ t ⟧e (x ∷ ρ)       ≡⟨ ⟦-E e ⟧ (x ∷ ρ) ⟩
    ⟦-e⟧ x                   ≡⟨ lin-ext₁ (proj₂ -e) x :+0 ρ ⟩
    ⟦-e⟧ :+0                 ≡⟨ sym (ZProp.+-identityʳ (⟦-e⟧ :+0)) ⟩
    ⟦-e⟧ :+0 ℤ.+ ℤ.+ 0       ≡⟨ sym (ZProp.+-assoc (⟦-e⟧ :+0) :-1 :+1) ⟩
    ⟦-e⟧ :+0 ℤ.+ :-1 ℤ.+ :+1 ≡⟨ cong (ℤ._+ :+1) (⟦ proj₂ -e ⟧+E⟦ val :-1 ⟧ (:+0 ∷ ρ)) ⟩
    ⟦ proj₁ -e-1 ⟧e (:+0 ∷ ρ) ℤ.+ :+1
      ∎ where open ≡-Reasoning

step-cooper₁ {σ = σ , σ≠0} (:-1 [ ∣-1∣ ]*var0+ e :≡0) divφ x ρ ¬H pr
  with ℤ.∣ σ ∣ | [∣ σ≠0 ∣≠0]
... | ℕ.suc k | +[1+ k ] = ⊥-elim $′ ¬H ((Fin.suc Fin.zero , _) , here refl , eq) where

  t = toExp (Lin-E 1) e
  e-1 = e +E val :-1
  ⟦t⟧ = λ x → ⟦ t ⟧e (x ∷ ρ)

  eq : x ≡ ⟦ proj₁ (e +E val :-1) ⟧e (:+0 ∷ ρ) ℤ.+ :+1
  eq = begin
    x                                ≡⟨ sym (ZProp.neg-involutive x) ⟩
    ℤ.- ℤ.- x                        ≡⟨ cong ℤ.-_ (sym (ZProp.-1*n≡-n x)) ⟩
    ℤ.- (:-1 ℤ.* x)                  ≡⟨ cong ℤ.-_ (APR.+-left-inverse-unique _ _ pr) ⟩
    ℤ.- ℤ.- ⟦t⟧ x                    ≡⟨ ZProp.neg-involutive _ ⟩
    ⟦t⟧ x                            ≡⟨ lin-ext₁ e x :+0 ρ ⟩
    ⟦t⟧ :+0                          ≡⟨ sym (ZProp.+-identityʳ (⟦t⟧ :+0)) ⟩
    ⟦t⟧ :+0 ℤ.+ ℤ.+ 0                ≡⟨ sym (ZProp.+-assoc (⟦t⟧ :+0) :-1 :+1) ⟩
    ⟦t⟧ :+0 ℤ.+ :-1 ℤ.+ :+1          ≡⟨ cong (ℤ._+ :+1) (⟦ e ⟧+E⟦ val :-1 ⟧ (:+0 ∷ ρ)) ⟩
    ⟦ proj₁ e-1 ⟧e (:+0 ∷ ρ) ℤ.+ :+1 ∎ where open ≡-Reasoning

-- :≢0
step-cooper₁ (val k :≢0) divφ x ρ ¬H = id
step-cooper₁ {σ = σ , _} (varn p + e :≢0) divφ x ρ ¬H =
  contraposition $ λ pr → begin
  let t = toExp (Lin-E (ℕ.suc p)) e; x-∣σ∣ = x ℤ.- ℤ.+ ℤ.∣ σ ∣ in
  ⟦ t ⟧e (x ∷ ρ)     ≡⟨ lin-ext₁ e x x-∣σ∣ ρ ⟩
  ⟦ t ⟧e (x-∣σ∣ ∷ ρ) ≡⟨ pr ⟩
  ℤ.+ 0              ∎ where open ≡-Reasoning
step-cooper₁ {σ = σ , σ≠0} (:+1 [ ∣+1∣ ]*var0+ e :≢0) divφ x ρ ¬H pr hf =
  ¬H ((k , -e) , here refl , eq) where

  k    = Fin.fromℕ ℤ.∣ σ ∣
  k'   = ℤ.+ ℤ.∣ σ ∣
  x-k' = x ℤ.- k'
  -e   = -E e
  t    = toExp (Lin-E 1) e
  ctxt = cong (ℤ._+ k')
  ⟦t⟧  = λ x → ⟦ t ⟧e (x ∷ ρ)
  ⟦-e⟧ = λ x → ⟦ proj₁ -e ⟧e (x ∷ ρ)

  eq : x ≡ ⟦ proj₁ -e ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ (Fin.toℕ k)
  eq = begin
    x                     ≡⟨ sym (ZProp.+-identityʳ x) ⟩
    x ℤ.+ :+0             ≡⟨ cong (ℤ._+_ x) (sym (ZProp.+-inverseˡ k')) ⟩
    x ℤ.+ (ℤ.- k' ℤ.+ k') ≡⟨ sym (ZProp.+-assoc x (ℤ.- k') k') ⟩
    x-k' ℤ.+ k'           ≡⟨ ctxt (sym (ZProp.*-identityˡ x-k')) ⟩
    :+1 ℤ.* x-k' ℤ.+ k'   ≡⟨ ctxt (APR.+-left-inverse-unique (:+1 ℤ.* x-k') _ hf) ⟩
    ℤ.- ⟦t⟧ x-k' ℤ.+ k'   ≡⟨ ctxt (⟦-E e ⟧ (x-k' ∷ ρ)) ⟩
    ⟦-e⟧ x-k' ℤ.+ k'      ≡⟨ ctxt (lin-ext₁ (proj₂ -e) x-k' :+0 ρ) ⟩
    ⟦-e⟧ :+0 ℤ.+ k'       ≡⟨ cong (ℤ._+_ (⟦-e⟧ :+0) ∘ ℤ.+_) (sym (FProp.toℕ-fromℕ _)) ⟩
    ⟦-e⟧ :+0 ℤ.+ ℤ.+ (Fin.toℕ k) ∎ where open ≡-Reasoning

step-cooper₁ {σ = σ , σ≠0} (:-1 [ ∣-1∣ ]*var0+ e :≢0) divφ x ρ ¬H pr hf =
  ¬H ((k , (-, e)) , here refl , eq) where

  k    = Fin.fromℕ ℤ.∣ σ ∣
  k'   = ℤ.+ ℤ.∣ σ ∣
  x-k' = x ℤ.- k'
  t    = toExp (Lin-E 1) e
  ⟦t⟧  = λ x → ⟦ t ⟧e (x ∷ ρ)
  ctxt = cong (λ z → ℤ.- z ℤ.+ k')

  eq : x ≡ ⟦t⟧ :+0 ℤ.+ ℤ.+ (Fin.toℕ k)
  eq = begin
    x                           ≡⟨ sym (ZProp.+-identityʳ x) ⟩
    x ℤ.+ :+0                   ≡⟨ cong (ℤ._+_ x) (sym (ZProp.+-inverseˡ k')) ⟩
    x ℤ.+ (ℤ.- k' ℤ.+ k')       ≡⟨ sym (ZProp.+-assoc x (ℤ.- k') k') ⟩
    x-k' ℤ.+ k'                 ≡⟨ cong (ℤ._+ k') (sym (ZProp.neg-involutive x-k')) ⟩
    ℤ.- (ℤ.- x-k') ℤ.+ k'       ≡⟨ ctxt (sym (ZProp.-1*n≡-n x-k')) ⟩
    ℤ.- (:-1 ℤ.* x-k') ℤ.+ k'   ≡⟨ ctxt (APR.+-left-inverse-unique (:-1 ℤ.* x-k') _ hf) ⟩
    ℤ.- (ℤ.- ⟦t⟧ x-k') ℤ.+ k'   ≡⟨ cong (ℤ._+ k') (ZProp.neg-involutive (⟦t⟧ x-k')) ⟩
    ⟦t⟧ x-k' ℤ.+ k'             ≡⟨ cong₂ ℤ._+_ (lin-ext₁ e x-k' :+0 ρ)
                                               (cong ℤ.+_ (sym (FProp.toℕ-fromℕ _))) ⟩
    ⟦t⟧ :+0 ℤ.+ ℤ.+ (Fin.toℕ k) ∎ where open ≡-Reasoning

step-cooper₁ {σ = σ≠0} (k≠0 :| e) (k∣′σ [ _ ]:| t) x ρ ¬H ⟦f⟧ = begin
  k                                      ∣′⟨ kdivs ⟩
  ⟦ t ⟧e (:-1 ℤ.* ℤ.+ ℤ.∣ σ ∣ ℤ.+ x ∷ ρ) ≡⟨ ctxt (ZProp.+-comm (:-1 ℤ.* ℤ.pos ℤ.∣ σ ∣) x) ⟩
  ⟦ t ⟧e (x ℤ.+ :-1 ℤ.* ℤ.+ ℤ.∣ σ ∣ ∷ ρ) ≡⟨ ctxt (cong (ℤ._+_ x) (ZProp.-1*n≡-n _)) ⟩
  ⟦ t ⟧e (x-∣σ∣ ∷ ρ) ∎ where

  open ZdivProp.∣′-Reasoning
  σ      = proj₁ σ≠0
  x-∣σ∣  = x ℤ.- ℤ.+ ℤ.∣ σ ∣
  k      = toℤ k≠0
  k∣′∣σ∣ = ZdivProp.∣′-trans k∣′σ ZdivProp.m∣′∣m∣
  kdivs  = proj₁ (⟦ e mod-E ∣ σ≠0 ∣≠0 |: _ [ k∣′∣σ∣ ]⟧ :-1 x ρ) ⟦f⟧
  ctxt   = cong (λ x → ⟦ t ⟧e (x ∷ ρ))

step-cooper₁ {σ = σ≠0} (k≠0 :|̸ e) (k∣′σ [ _ ]:|̸ t) x ρ ¬H ¬k∣′ k∣′ = ¬k∣′ $ begin
  k ∣′⟨ kdivs ⟩
  ⟦ t ⟧e (1*+∣σ∣ ℤ.+ x-∣σ∣ ∷ ρ)        ≡⟨ ctxt (ZProp.+-comm 1*+∣σ∣ x-∣σ∣ ) ⟩
  ⟦ t ⟧e (x-∣σ∣ ℤ.+ 1*+∣σ∣ ∷ ρ)        ≡⟨ ctxt (ZProp.+-assoc x -∣σ∣ 1*+∣σ∣) ⟩
  ⟦ t ⟧e (x ℤ.+ (-∣σ∣ ℤ.+ 1*+∣σ∣) ∷ ρ) ≡⟨ ctxt (ctxt' (ZProp.*-identityˡ +∣σ∣)) ⟩
  ⟦ t ⟧e (x ℤ.+ (-∣σ∣ ℤ.+ +∣σ∣) ∷ ρ)   ≡⟨ ctxt (cong (ℤ._+_ x) (ZProp.+-inverseˡ +∣σ∣)) ⟩
  ⟦ t ⟧e (x ℤ.+ :+0 ∷ ρ)               ≡⟨ ctxt (ZProp.+-identityʳ x) ⟩
  ⟦ t ⟧e (x ∷ ρ) ∎ where

  open ZdivProp.∣′-Reasoning
  σ      = proj₁ σ≠0
  +∣σ∣   = ℤ.+ ℤ.∣ σ ∣
  -∣σ∣   = ℤ.- +∣σ∣
  1*+∣σ∣ = :+1 ℤ.* +∣σ∣
  x-∣σ∣  = x ℤ.- +∣σ∣
  k      = toℤ k≠0
  k∣′∣σ∣ = ZdivProp.∣′-trans k∣′σ ZdivProp.m∣′∣m∣
  kdivs = proj₁ (⟦ e mod-E ∣ σ≠0 ∣≠0 |: _ [ k∣′∣σ∣ ]⟧ :+1 x-∣σ∣ ρ) k∣′
  ctxt   = cong (λ x → ⟦ t ⟧e (x ∷ ρ))
  ctxt'  = cong (λ t → x ℤ.+ (-∣σ∣ ℤ.+ t))

step-cooper₁ (φ :∧ ψ) (divφ :∧ divψ) x ρ ¬H = Prod.map
  (step-cooper₁ φ divφ x ρ $ flip contraposition ¬H
                           $ Prod.map₂ $ Prod.map₁ (∈-++⁺ˡ _))
  (step-cooper₁ ψ divψ x ρ $ flip contraposition ¬H
                           $ Prod.map₂ $ Prod.map₁ (∈-++⁺ʳ _ (bset φ)))
step-cooper₁ (φ :∨ ψ) (divφ :∨ divψ) x ρ ¬H = Sum.map
  (step-cooper₁ φ divφ x ρ $ flip contraposition ¬H
                           $ Prod.map₂ $ Prod.map₁ (∈-++⁺ˡ _))
  (step-cooper₁ ψ divψ x ρ $ flip contraposition ¬H
                           $ Prod.map₂ $ Prod.map₁ (∈-++⁺ʳ _ (bset φ)))


{-

  x-decomp-dec₁ : ∀ {m n} (L : List (Lin′ n 1)) (j : Fin m) →
    ∀ ρ x → Dec (P.∃ (λ b → P.Σ (b ∈ L) (λ _ → x ≡ ([| proj₁ b |]e ρ ℤ+ (+ toℕ j)))))
  x-decomp-dec₁ [] j ρ x = no (λ h → b∈[]-elim (P.proj₁ (P.proj₂ h)))
  x-decomp-dec₁ (x ∷ xs) j ρ x' with x' ℤ≟ ([| proj₁ x |]e ρ ℤ+ + toℕ j) | x-decomp-dec₁ xs j ρ x'
  ... | yes P₁ | _ = yes (P._,_ x (P._,_ here P₁))
  ... | _ | yes P₂ = yes (P._,_ (P.proj₁ P₂) (P._,_ (there ((P.proj₁ ∘ P.proj₂) P₂)) ((P.proj₂ ∘ P.proj₂) P₂)))
  ... | no ¬P₁ | no ¬P₂ = no (λ hf → [ (λ h → ¬P₁ (subst (λ u → x' ≡ [| proj₁ u |]e ρ ℤ+ + toℕ j) h ((P.proj₂ ∘ P.proj₂) hf))) , (λ h → ¬P₂ (P._,_ (P.proj₁ hf) (P._,_ h ((P.proj₂ ∘ P.proj₂) hf)))) ]′ (b∈L-elim (P.proj₁ (P.proj₂ hf))))

  x-decomp-dec : ∀ {m n} (L : List (Lin′ n 1)) → ∀ ρ x → Dec (P.∃ (λ (j : Fin m) → P.∃ (λ b → P.Σ (b ∈ L) (λ _ → x ≡ ([| proj₁ b |]e ρ ℤ+ (+ toℕ j))))))
  x-decomp-dec L ρ x = Fin-dec (λ a → x-decomp-dec₁ L a ρ x)

  cooper₁ : ∀ {n} (φ : Unf (ℕs n)) (δ : Dall (proj₁ (minusinf φ))) → ∀ (ρ : Vec ℤ n) → ((P.∃ (λ (j : Fin (ℕs (δ-extract δ))) → P.∃ (λ b → P.Σ (b ∈ (bset φ)) (λ _ → [| proj₁ φ |] ((([| proj₁ b |]e ((+ 0) ● ρ)) ℤ+ (+ toℕ j)) ● ρ))))) → ⊥) → ∀ x → [| proj₁ φ |] (x ● ρ) → [| proj₁ φ |] ((x ℤ- ((+ δ-extract δ))) ● ρ)
  cooper₁ φ δ ρ ¬H x φx with x-decomp-dec {ℕs ∣ proj₁ (proj₁ δ) ∣} (bset φ) (+ 0 ● ρ) x
  ... | yes (P._,_ j (P._,_ b (P._,_ b∈L Heq))) = ⊥-elim (¬H (P._,_ j (P._,_ b (P._,_ b∈L (subst (λ u → [| proj₁ φ |] (u ● ρ)) Heq φx)))))
  ... | no ¬P = step-cooper₁ φ δ x ρ ¬P φx

  cooper₁-ext : ∀ (k : ℕ) {n} (φ : Unf (ℕs n)) (ρ : Vec ℤ n) → ((P.∃ (λ (j : Fin (jset φ)) → P.∃ (λ b → P.Σ (b ∈ (bset φ)) (λ _ → [| proj₁ φ |] ((([| proj₁ b |]e ((+ 0) ● ρ)) ℤ+ (+ toℕ j)) ● ρ))))) → ⊥) → ∀ x → [| proj₁ φ |] (x ● ρ) → [| proj₁ φ |] ((x ℤ- (+ k ℤ* (+ my-δ φ))) ● ρ)
  cooper₁-ext zero φ ρ _ x φx = subst (λ u → [| proj₁ φ |] (u ● ρ)) (sym (unfold-ℤ- x (+ 0))) (subst (λ u → [| proj₁ φ |] (u ● ρ)) (sym (P.proj₂ ℤr.+-identity x)) φx)
  cooper₁-ext (ℕs k) φ ρ ¬H x φx with cooper₁-ext k φ ρ ¬H x φx
  ... | φxk = subst (λ u → [| proj₁ φ |] (x ℤ- u ● ρ)) (sym (P.proj₂ ℤr.distrib (+ my-δ φ) (+ 1) (+ k))) (subst (λ u → [| proj₁ φ |] (x ℤ- (u ℤ+ ((+ k) ℤ* (+ my-δ φ))) ● ρ)) (sym (P.proj₁ ℤr.*-identity (+ (my-δ φ)))) (subst (λ u → [| proj₁ φ |] (u ● ρ)) (sym (unfold-ℤ- x (+ (my-δ φ) ℤ+ ((+ k) ℤ* + (my-δ φ))))) (subst (λ u → [| proj₁ φ |] ((x ℤ+ - u) ● ρ)) (ℤr.+-comm ((+ k) ℤ* + (my-δ φ)) (+ (my-δ φ))) (subst (λ u → [| proj₁ φ |] ((x ℤ+ u) ● ρ)) (sym (-distr-ℤ+ ((+ k) ℤ* + (my-δ φ)) (+ (my-δ φ)))) (subst (λ u → [| proj₁ φ |] (u ● ρ)) (ℤr.+-assoc x (- ((+ k) ℤ* (+ (my-δ φ)))) (- (+ (my-δ φ)))) (subst (λ u → [| proj₁ φ |] ((u ℤ+ - (+ (my-δ φ))) ● ρ)) (unfold-ℤ- x ((+ k) ℤ* + (my-δ φ))) (subst (λ u → [| proj₁ φ |] (u ● ρ)) (unfold-ℤ- (x ℤ- ((+ k) ℤ* + (my-δ φ))) (+ (my-δ φ))) (cooper₁ φ (lcm-dvd (minusinf φ)) ρ ¬H (x ℤ- ((+ k) ℤ* + (my-δ φ))) φxk))))))))

  cooper₁-simpl : ∀ {n} (φ : Unf (ℕs n)) (ρ : Vec ℤ n) → ((P.∃ (λ (j : Fin (jset φ)) → P.∃ (λ b → P.Σ (b ∈ (bset φ)) (λ _ → [| proj₁ φ |] ((([| proj₁ b |]e ((+ 0) ● ρ)) ℤ+ (+ toℕ j)) ● ρ))))) → ⊥) → ∀ x → [| proj₁ φ |] (x ● ρ) → P.∃ (λ u → [| proj₁ (minusinf φ) |] (u ● ρ))
  cooper₁-simpl φ ρ ¬H x φx with bound-inf φ ρ | ℤcompare x (bound-inf φ ρ) | cooper₂ φ ρ
  cooper₁-simpl φ ρ ¬H x φx | z | less y | H = P._,_ x (P.proj₁ (H x (ℤ≤.trans (nℤ≤sn x) y)) φx)
  cooper₁-simpl φ ρ ¬H .z φx | z | equal refl | H = P._,_ z (P.proj₁ (H z ℤ≤.refl) φx)
  cooper₁-simpl φ ρ ¬H x φx | z | greater y | H with ℤ≤-reachability x z (proj₁ (lcm-dvd (minusinf φ))) (ℤ≤.trans (nℤ≤sn z) y)
  ... | P._,_ k Hk = P._,_ (x ℤ- ((+ k) ℤ* + my-δ φ)) (P.proj₁ (H (x ℤ- ((+ k) ℤ* + my-δ φ)) Hk) (cooper₁-ext k φ ρ ¬H x φx))
-}
