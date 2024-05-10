module A201605.TowardsAltArtemov.NormalizationCatholic where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; subst)
open import Relation.Nullary using (Dec ; yes ; no)
open import Size using (∞)

open import A201605.AbelChapmanExtended.Delay
open import A201605.TowardsAltArtemov.SyntaxCatholic


lookup : ∀ {Γ Δ} {A : Ty 0} →
         Var Γ A → Env Δ Γ → Val Δ (↥ty ⁿ⌊ Δ ⌋ A)
lookup (top A)   (γ , v) = v
lookup (pop B x) (γ , v) = lookup x γ


never : ∀ {i A} → ∞Delay i A
force never = later never


mutual
  eval : ∀ {i Γ Δ} {A : Ty 0} →
         Tm Γ (↥ty ⁿ⌊ Γ ⌋ A) → Env Δ Γ → Delay i (Val Δ (↥ty ⁿ⌊ Δ ⌋ A))
  eval {A = A} (var {A′} x) γ with A ≟ A′
  eval (var x)   γ | yes refl = now (lookup x γ)
  eval (var x)   γ | no  _    = later never
  eval {A = A⊃B} (lam A′ {B′} t) γ with A⊃B ≟ (A′ ⊃ B′)
  eval (lam A t) γ | yes refl = now (lam A t γ {{refl}})
  eval (lam A t) γ | no  _    = later never
  eval {A = B} (app {A′} {B′} t u) γ with B ≟ B′
  eval (app t u) γ | yes refl = v ← eval t γ ⁏ w ← eval u γ ⁏ β-reduce v w
  eval (app t u) γ | no  _    = later never

  ∞eval : ∀ {i Γ Δ} {A : Ty 0} →
          Tm Γ (↥ty ⁿ⌊ Γ ⌋ A) → Env Δ Γ → ∞Delay i (Val Δ (↥ty ⁿ⌊ Δ ⌋ A))
  force (∞eval t γ) = eval t γ

  β-reduce : ∀ {i Δ} {A B : Ty 0} →
             Val Δ (↥ty ⁿ⌊ Δ ⌋ (A ⊃ B)) → Val Δ (↥ty ⁿ⌊ Δ ⌋ A) → Delay i (Val Δ (↥ty ⁿ⌊ Δ ⌋ B))
  β-reduce {A = A} {B} (ne v) w = now (ne (app v w))
  β-reduce {A = A} {B} (lam A′ {B′} t γ) w with A ≟ A′ | B ≟ B′
  β-reduce (lam A  t γ) w | yes refl | yes refl = later (∞eval t (γ , w))
  β-reduce (lam A′ t γ) w | _        | _        = later never


mutual
  readback : ∀ {i Δ} (A : Ty 0) →
             Val Δ (↥ty ⁿ⌊ Δ ⌋ A) → Delay i (Nf Δ (↥ty ⁿ⌊ Δ ⌋ A))
  readback ★       (ne v) = ne <$> readback-ne v
  readback ★       v      = later never
  readback (A ⊃ B) v      = later (∞η-expand v)

  readback-ne : ∀ {i Δ} {A : Ty 0} →
                Ne Val Δ (↥ty ⁿ⌊ Δ ⌋ A) → Delay i (Ne Nf Δ (↥ty ⁿ⌊ Δ ⌋ A))
  readback-ne (var x)   = now (var x)
  readback-ne (app v w) = n ← readback-ne v ⁏
                          m ← readback _ w ⁏
                          now (app n m)

  ∞η-expand : ∀ {i Δ} {A B : Ty 0} →
              Val Δ (↥ty ⁿ⌊ Δ ⌋ (A ⊃ B)) → ∞Delay i (Nf Δ (↥ty ⁿ⌊ Δ ⌋ (A ⊃ B)))
  force (∞η-expand {A = A} {B = B} v) =
        v′ ← β-reduce (≪val (weak A id) (↑val (weak A id) v)) (ne (var (top A))) ⁏
        n′ ← readback B v′ ⁏
        now (lam A n′)


id-env : (Γ : Cx) → Env Γ Γ
id-env ∅       = ∅
id-env (Γ , A) = ↑env (weak A id) (id-env Γ) , ne (var (top A))


nf? : {Γ : Cx} {A : Ty 0} →
      Tm Γ (↥ty ⁿ⌊ Γ ⌋ A) → Delay ∞ (Nf Γ (↥ty ⁿ⌊ Γ ⌋ A))
nf? {Γ} {A} t = t′ ← eval t (id-env Γ) ⁏
                readback A t′


v₀ : ∀ {Γ A} → Tm (Γ , A) (↥ty ⁿ⌊ Γ , A ⌋ A)
v₀ {A = A} = var (top A)

v₁ : ∀ {Γ A B} → Tm ((Γ , A) , B) (↥ty ⁿ⌊ (Γ , A) , B ⌋ A)
v₁ {A = A} {B} = var (pop B (top A))

v₂ : ∀ {Γ A B C} → Tm (((Γ , A) , B) , C) (↥ty ⁿ⌊ ((Γ , A) , B) , C ⌋ A)
v₂ {A = A} {B} {C} = var (pop C (pop B (top A)))


I : ∀ {Γ A} → Tm Γ (↥ty ⁿ⌊ Γ ⌋ (A ⊃ A))
I {A = A} = lam A v₀

K : ∀ {Γ A B} → Tm Γ (↥ty ⁿ⌊ Γ ⌋ (A ⊃ B ⊃ A))
K {A = A} {B} = lam A (lam B v₁ {{refl}})

S : ∀ {Γ A B C} → Tm Γ (↥ty ⁿ⌊ Γ ⌋ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C))
S {A = A} {B} {C} = lam (A ⊃ B ⊃ C) (lam (A ⊃ B) (lam A (app (app v₂ v₀ {{refl}}) (app v₁ v₀ {{refl}}) {{refl}}) {{refl}}) {{refl}})


II : ∀ {Γ A} → Tm Γ (↥ty ⁿ⌊ Γ ⌋ (A ⊃ A))
II = app I I {{refl}}

SKK : ∀ {Γ A} → Tm Γ (↥ty ⁿ⌊ Γ ⌋ (A ⊃ A))
SKK {A = A} = app (app S K {{refl}}) (K {B = A ⊃ A}) {{refl}}

SKSK : ∀ {Γ A B} → Tm Γ (↥ty ⁿ⌊ Γ ⌋ (A ⊃ B ⊃ A))
SKSK = app (app (app S K {{refl}}) S {{refl}}) K {{refl}}

flip : ∀ {Γ A B C} → Tm Γ (↥ty ⁿ⌊ Γ ⌋ ((A ⊃ B ⊃ C) ⊃ B ⊃ A ⊃ C))
flip {A = A} {B} {C} = lam (A ⊃ B ⊃ C) (lam B (lam A (app (app v₂ v₀ {{refl}}) v₁ {{refl}}) {{refl}}) {{refl}})
