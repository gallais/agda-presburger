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
open import Comparisons

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.Any.Properties

open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as NProp

open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ZProp
open import Data.Integer.Divisibility.Signed
import Data.Integer.DivMod as ZDM
import Algebra.Properties.Ring ZProp.+-*-ring as APR

open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FProp

open import Data.Empty
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Vec

open import Function
open import Relation.Nullary
import Relation.Nullary.Decidable as DEC
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

step-cooper₁ :
  ∀ {n f σ} (φ : Unit {ℕ.suc n} f) (divφ : All∣ σ (proj₁ $ var0⟶-∞ φ)) x ρ →
  (¬H : ¬ (∃ λ (j : Fin (ℕ.suc ℤ.∣ proj₁ σ ∣)) →
             Any (λ b → x ≡ ⟦ proj₁ b ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ Fin.toℕ j) (bset φ))) →
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

... | no ¬le = ⊥-elim $ ¬H (j , here ⋯-x≡0) where

   lt   = ZProp.≰⇒> ¬le
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

-- :≡0
step-cooper₁ (val k :≡0) divφ x ρ ¬H = id
step-cooper₁ {σ = σ , _} (varn p + e        :≡0) divφ x ρ ¬H pr = begin
  let t = toExp (Lin-E (ℕ.suc p)) e; x-∣σ∣ = x ℤ.- ℤ.+ ℤ.∣ σ ∣ in
  ⟦ t ⟧e (x-∣σ∣ ∷ ρ) ≡⟨ lin-ext₁ e x-∣σ∣ x ρ ⟩
  ⟦ t ⟧e (x ∷ ρ)     ≡⟨ pr ⟩
  ℤ.+ 0              ∎ where open ≡-Reasoning
step-cooper₁ {σ = σ , σ≠0} (:+1 [ ∣+1∣ ]*var0+ e :≡0) divφ x ρ ¬H pr
  with ℤ.∣ σ ∣ | [∣ σ≠0 ∣≠0]
... | ℕ.suc k | +[1+ k ]≠ = ⊥-elim $′ ¬H (Fin.suc Fin.zero , here eq) where

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
... | ℕ.suc k | +[1+ k ]≠ = ⊥-elim $′ ¬H (Fin.suc Fin.zero , here eq) where

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
  ¬H (k , here eq) where

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
  ¬H (k , here eq) where

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

step-cooper₁ {σ = σ≠0} (k≠0 :| e) (k∣σ [ _ ]:| t) x ρ ¬H ⟦f⟧ = begin
  k                                      ∣⟨ kdivs ⟩
  ⟦ t ⟧e (:-1 ℤ.* ℤ.+ ℤ.∣ σ ∣ ℤ.+ x ∷ ρ) ≡⟨ ctxt (ZProp.+-comm (:-1 ℤ.* ℤ.pos ℤ.∣ σ ∣) x) ⟩
  ⟦ t ⟧e (x ℤ.+ :-1 ℤ.* ℤ.+ ℤ.∣ σ ∣ ∷ ρ) ≡⟨ ctxt (cong (ℤ._+_ x) (ZProp.-1*n≡-n _)) ⟩
  ⟦ t ⟧e (x-∣σ∣ ∷ ρ) ∎ where

  open ∣-Reasoning
  σ      = proj₁ σ≠0
  x-∣σ∣  = x ℤ.- ℤ.+ ℤ.∣ σ ∣
  k      = toℤ k≠0
  k∣∣σ∣ = ∣-trans k∣σ m∣∣m∣
  kdivs  = proj₁ (⟦ e mod-E ∣ σ≠0 ∣≠0 |: _ [ k∣∣σ∣ ]⟧ :-1 x ρ) ⟦f⟧
  ctxt   = cong (λ x → ⟦ t ⟧e (x ∷ ρ))

step-cooper₁ {σ = σ≠0} (k≠0 :|̸ e) (k∣σ [ _ ]:|̸ t) x ρ ¬H ¬k∣ k∣ = ¬k∣ $ begin
  k ∣⟨ kdivs ⟩
  ⟦ t ⟧e (1*+∣σ∣ ℤ.+ x-∣σ∣ ∷ ρ)        ≡⟨ ctxt (ZProp.+-comm 1*+∣σ∣ x-∣σ∣ ) ⟩
  ⟦ t ⟧e (x-∣σ∣ ℤ.+ 1*+∣σ∣ ∷ ρ)        ≡⟨ ctxt (ZProp.+-assoc x -∣σ∣ 1*+∣σ∣) ⟩
  ⟦ t ⟧e (x ℤ.+ (-∣σ∣ ℤ.+ 1*+∣σ∣) ∷ ρ) ≡⟨ ctxt (ctxt' (ZProp.*-identityˡ +∣σ∣)) ⟩
  ⟦ t ⟧e (x ℤ.+ (-∣σ∣ ℤ.+ +∣σ∣) ∷ ρ)   ≡⟨ ctxt (cong (ℤ._+_ x) (ZProp.+-inverseˡ +∣σ∣)) ⟩
  ⟦ t ⟧e (x ℤ.+ :+0 ∷ ρ)               ≡⟨ ctxt (ZProp.+-identityʳ x) ⟩
  ⟦ t ⟧e (x ∷ ρ) ∎ where

  open ∣-Reasoning
  σ      = proj₁ σ≠0
  +∣σ∣   = ℤ.+ ℤ.∣ σ ∣
  -∣σ∣   = ℤ.- +∣σ∣
  1*+∣σ∣ = :+1 ℤ.* +∣σ∣
  x-∣σ∣  = x ℤ.- +∣σ∣
  k      = toℤ k≠0
  k∣∣σ∣ = ∣-trans k∣σ m∣∣m∣
  kdivs = proj₁ (⟦ e mod-E ∣ σ≠0 ∣≠0 |: _ [ k∣∣σ∣ ]⟧ :+1 x-∣σ∣ ρ) k∣
  ctxt   = cong (λ x → ⟦ t ⟧e (x ∷ ρ))
  ctxt'  = cong (λ t → x ℤ.+ (-∣σ∣ ℤ.+ t))

step-cooper₁ (φ :∧ ψ) (divφ :∧ divψ) x ρ ¬H = Prod.map
  (step-cooper₁ φ divφ x ρ $ flip contraposition ¬H $ Prod.map₂ ++⁺ˡ)
  (step-cooper₁ ψ divψ x ρ $ flip contraposition ¬H $ Prod.map₂ $ ++⁺ʳ (bset φ))
step-cooper₁ (φ :∨ ψ) (divφ :∨ divψ) x ρ ¬H = Sum.map
  (step-cooper₁ φ divφ x ρ $ flip contraposition ¬H $ Prod.map₂ ++⁺ˡ)
  (step-cooper₁ ψ divψ x ρ $ flip contraposition ¬H $ Prod.map₂ $ ++⁺ʳ (bset φ))


cooper₁-dec : ∀ {m} n (L : List (∃ (Lin-E {m} 1))) →
  ∀ ρ x → Dec (∃ λ (j : Fin n) → Any (λ b → x ≡ ⟦ proj₁ b ⟧e ρ ℤ.+ ℤ.+ Fin.toℕ j) L)
cooper₁-dec n L ρ x = FProp.any? $′ λ j → Any.any (λ b → x ℤ.≟ _) L

cooper₁ : ∀ {n f σ} (φ : Unit {ℕ.suc n} f) (divφ : All∣ σ (proj₁ $ var0⟶-∞ φ)) → ∀ ρ →
          let ∣σ∣ = ℤ.∣ proj₁ σ ∣ in
          (¬H : ¬ (∃ λ (j : Fin (ℕ.suc ∣σ∣)) →
                Any (λ b → ⟦ f ⟧ (⟦ proj₁ b ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ Fin.toℕ j ∷ ρ)) (bset φ)))
          → ∀ x → ⟦ f ⟧ (x ∷ ρ) → ⟦ f ⟧ (x ℤ.- ℤ.+ ∣σ∣ ∷ ρ)
cooper₁ {f = f} {σ} φ divφ ρ ¬H x pr
  with cooper₁-dec (ℕ.suc ℤ.∣ proj₁ σ ∣) (bset φ) (:+0 ∷ ρ) x
... | yes (j , b∈) = ⊥-elim (¬H (j , Any.map (λ e → subst (λ x → ⟦ f ⟧ (x ∷ ρ)) e pr) b∈))
... | no ¬p = step-cooper₁ φ divφ x ρ ¬p pr


cooper₁s : ∀ (k : ℕ) {n f σ} (φ : Unit {ℕ.suc n} f) (divφ : All∣ σ (proj₁ $ var0⟶-∞ φ)) → ∀ ρ →
          let ∣σ∣ = ℤ.∣ proj₁ σ ∣ in
          (¬H : ¬ (∃ λ (j : Fin (ℕ.suc ∣σ∣)) →
                Any (λ b → ⟦ f ⟧ (⟦ proj₁ b ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ Fin.toℕ j ∷ ρ)) (bset φ)))
          → ∀ x → ⟦ f ⟧ (x ∷ ρ) → ⟦ f ⟧ (x ℤ.- (ℤ.+ k ℤ.* ℤ.+ ∣σ∣) ∷ ρ)
cooper₁s ℕ.zero    φ divφ ρ ¬H x pr
  rewrite ZProp.+-identityʳ x = pr
cooper₁s (ℕ.suc k) {f = f} {σ} φ divφ ρ ¬H x pr = subst (λ x → ⟦ f ⟧ (x ∷ ρ)) eq
  $ cooper₁s k φ divφ ρ ¬H (x ℤ.- ℤ.+ ∣σ∣)
  $ cooper₁ φ divφ ρ ¬H x pr where

  ∣σ∣ = ℤ.∣ proj₁ σ ∣

  eq : x ℤ.- ℤ.+ ∣σ∣ ℤ.- ℤ.+ k ℤ.* ℤ.+ ∣σ∣ ≡ x ℤ.- ℤ.+ (ℕ.suc k) ℤ.* ℤ.+ ∣σ∣
  eq = sym $ begin
    x ℤ.- ℤ.+ (ℕ.suc k) ℤ.* ℤ.+ ∣σ∣
      ≡⟨ cong (ℤ._-_ x) (ZProp.[1+m]*n≡n+m*n (ℤ.+ k) (ℤ.+ ∣σ∣)) ⟩
    x ℤ.- (ℤ.+ ∣σ∣ ℤ.+ ℤ.+ k ℤ.* ℤ.+ ∣σ∣)
      ≡⟨ cong (ℤ._+_ x) (ZProp.neg-distrib-+ (ℤ.+ ∣σ∣) (ℤ.+ k ℤ.* ℤ.+ ∣σ∣)) ⟩
    x ℤ.+ (ℤ.- ℤ.+ ∣σ∣ ℤ.+ ℤ.- (ℤ.+ k ℤ.* ℤ.+ ∣σ∣))
      ≡⟨ sym $ ZProp.+-assoc x (ℤ.- ℤ.+ ∣σ∣) (ℤ.- (ℤ.+ k ℤ.* ℤ.+ ∣σ∣)) ⟩
    x ℤ.- ℤ.+ ∣σ∣ ℤ.- ℤ.+ k ℤ.* ℤ.+ ∣σ∣
      ∎ where open ≡-Reasoning


cooper₁-simpl : ∀ {n f σ} (φ : Unit {ℕ.suc n} f) (divφ : All∣ σ (proj₁ $ var0⟶-∞ φ)) → ∀ ρ →
          let ∣σ∣ = ℤ.∣ proj₁ σ ∣ in
          (¬H : ¬ (∃ λ (j : Fin (ℕ.suc ∣σ∣)) →
                Any (λ b → ⟦ f ⟧ (⟦ proj₁ b ⟧e (:+0 ∷ ρ) ℤ.+ ℤ.+ Fin.toℕ j ∷ ρ)) (bset φ)))
          → ∀ x → ⟦ f ⟧ (x ∷ ρ) → ∃ λ u → ⟦ proj₁ (var0⟶-∞ φ) ⟧ (u ∷ ρ)
cooper₁-simpl {σ = σ , σ≠0} φ divφ ρ ¬H x pr with ℤcompare x (bound φ ρ)
... | less    x<bd = -, proj₁ (cooper-bound φ x ρ (ZProp.<⇒≤ x<bd)) pr
... | equal   x≡bd = -, proj₁ (cooper-bound φ x ρ (ZProp.≤-reflexive x≡bd)) pr
... | greater x>bd = -, proj₁ (cooper-bound φ x′ ρ x′≤bd) pr′ where

  bd     = bound φ ρ
  x-bd   = x ℤ.- bd
  0≤x-bd : :+0 ℤ.≤ x-bd
  0≤x-bd = ZProp.m≤n⇒0≤n-m (ZProp.<⇒≤ x>bd)
  d      = ℤ.∣ σ ∣
  d≢0    = DEC.fromWitnessFalse $ to≢0 σ≠0 ∘′ ZProp.∣n∣≡0⇒n≡0
  q      = ℤ.suc ((x-bd ZDM.divℕ d) {d≢0})
  +∣q∣≡q = ZProp.0≤n⇒+∣n∣≡n (ZProp.≤-step (ZDM.0≤n⇒0≤n/ℕd x-bd d 0≤x-bd))
  x′     = x ℤ.- (ℤ.+ ℤ.∣ q ∣ ℤ.* ℤ.+ d)

  x′≤bd : x′ ℤ.≤ bd
  x′≤bd = begin
    x ℤ.- (ℤ.+ ℤ.∣ q ∣ ℤ.* ℤ.+ d)
      ≡⟨ cong (λ m → x ℤ.- (m ℤ.* ℤ.+ d)) +∣q∣≡q ⟩
    x ℤ.- q ℤ.* ℤ.+ d
      ≤⟨ ZProp.+-monoʳ-≤ x (ZProp.neg-mono-≤-≥ (ZProp.<⇒≤ (ZDM.n<s[n/ℕd]*d x-bd d))) ⟩
    x ℤ.+ ℤ.- x-bd
      ≡⟨ cong (ℤ._+_ x) (ZProp.neg-distrib-+ x (ℤ.- bd)) ⟩
    x ℤ.+ (ℤ.- x ℤ.+ ℤ.- (ℤ.- bd))
      ≡⟨ sym (ZProp.+-assoc x (ℤ.- x) (ℤ.- (ℤ.- bd))) ⟩
    x ℤ.+ ℤ.- x ℤ.+ ℤ.- (ℤ.- bd)
      ≡⟨ cong₂ ℤ._+_ (ZProp.+-inverseʳ x) (ZProp.neg-involutive bd) ⟩
    :+0 ℤ.+ bd
      ≡⟨ ZProp.+-identityˡ bd ⟩
    bd ∎ where open ZProp.≤-Reasoning

  pr′ = cooper₁s ℤ.∣ q ∣ φ divφ ρ ¬H x pr
