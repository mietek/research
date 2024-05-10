module A201605.AbelChapmanExtended.Termination where

open import Data.Product using (∃ ; _,_)
open import Data.Unit using () renaming (tt to unit)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Size using (∞)

open import A201605.AbelChapmanExtended.Delay
open import A201605.AbelChapmanExtended.Convergence

open import A201605.AbelChapmanExtended.Syntax
open import A201605.AbelChapmanExtended.OPE
open import A201605.AbelChapmanExtended.Renaming.Syntax
open import A201605.AbelChapmanExtended.Renaming.OPE
open import A201605.AbelChapmanExtended.Normalization
open import A201605.AbelChapmanExtended.Renaming.Convergence
open import A201605.AbelChapmanExtended.Semantics
open import A201605.AbelChapmanExtended.Renaming.Semantics
open import A201605.AbelChapmanExtended.Reflection




β-reduce-sound : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) {w : Val Δ a} →
                 C⟦ b ⟧ (eval t (ρ , w)) → C⟦ b ⟧ (β-reduce (lam t ρ) w)
β-reduce-sound t ρ (v , ⇓v , ⟦v⟧) = (v , ⇓later ⇓v , ⟦v⟧)


⟦loop⟧ : ∀ {Δ c} {v? : Delay ∞ (Val Δ ⊥)} →
         C⟦ ⊥ ⟧ v? →
         C⟦ c ⟧ (v ← v? ⁏
                 ω-reduce v)
⟦loop⟧ {c = c} (ne v , ⇓v , (n , ⇓n)) =
      let v′   = ne (loop v)
          ⟦v′⟧ = reflect c (loop v) (loop n , ⇓map loop ⇓n)
      in  (v′ , ⇓bind ⇓v ⇓now , ⟦v′⟧)


⟦var⟧ : ∀ {Γ Δ a} (x : Var Γ a) (ρ : Env Δ Γ) →
        E⟦ Γ ⟧ ρ → C⟦ a ⟧ (now (lookup x ρ))
⟦var⟧ top     (ρ , v) (⟦ρ⟧ , ⟦v⟧) = (v , ⇓now , ⟦v⟧)
⟦var⟧ (pop x) (ρ , v) (⟦ρ⟧ , ⟦v⟧) = ⟦var⟧ x ρ ⟦ρ⟧


⟦lam⟧ : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (⟦ρ⟧ : E⟦ Γ ⟧ ρ) →
        (∀ {Δ′} (η : Δ′ ⊇ Δ) (w : Val Δ′ a)
            (⟦w⟧ : V⟦ a ⟧ w) → C⟦ b ⟧ (eval t (ren-env η ρ , w))) →
        C⟦ a ⇒ b ⟧ (now (lam t ρ))
⟦lam⟧ t ρ ⟦ρ⟧ h =
      (lam t ρ , ⇓now , λ η w ⟦w⟧ → β-reduce-sound t (ren-env η ρ) (h η w ⟦w⟧))


⟦app⟧ : ∀ {Δ a b} {v? : Delay ∞ (Val Δ (a ⇒ b))} {w? : Delay ∞ (Val Δ a)} →
        C⟦ a ⇒ b ⟧ v? → C⟦ a ⟧ w? →
        C⟦ b ⟧ (v ← v? ⁏
                w ← w? ⁏
                β-reduce v w)
⟦app⟧ (v , ⇓v , ⟦v⟧) (w , ⇓w , ⟦w⟧) =
      let (vw , ⇓vw , ⟦vw⟧) = ⟦v⟧ id w ⟦w⟧
          ⇓vw′              = ⇓bind ⇓v (⇓bind ⇓w (subst (λ v → β-reduce v w ⇓ vw)
                                                        (ren-val-id v)
                                                        ⇓vw))
      in  (vw , ⇓vw′ , ⟦vw⟧)


⟦pair⟧ : ∀ {Γ Δ a b} (t : Tm Γ a) (u : Tm Γ b) (ρ : Env Δ Γ) (⟦ρ⟧ : E⟦ Γ ⟧ ρ) →
         C⟦ a ⟧ (eval t ρ) → C⟦ b ⟧ (eval u ρ) →
         C⟦ a ∧ b ⟧ (v ← eval t ρ ⁏
                     w ← eval u ρ ⁏
                     now (pair v w))
⟦pair⟧ t u ρ ⟦ρ⟧ (v , ⇓v , ⟦v⟧) (w , ⇓w , ⟦w⟧) =
      let c    = (v , ⇓now , ⟦v⟧)
          d    = (w , ⇓now , ⟦w⟧)
      in  (pair v w , ⇓bind ⇓v (⇓bind ⇓w ⇓now) , c , d)


⟦fst⟧ : ∀ {Δ a b} {v? : Delay ∞ (Val Δ (a ∧ b))} →
        C⟦ a ∧ b ⟧ v? →
        C⟦ a ⟧ (v ← v? ⁏
                π₁-reduce v)
⟦fst⟧ (v , ⇓v , ⟦v⟧) =
      let (c₁ , c₂)         = ⟦v⟧
          (v₁ , ⇓v₁ , ⟦v₁⟧) = c₁
      in  (v₁ , ⇓bind ⇓v ⇓v₁ , ⟦v₁⟧)


⟦snd⟧ : ∀ {Δ a b} {v? : Delay ∞ (Val Δ (a ∧ b))} →
        C⟦ a ∧ b ⟧ v? →
        C⟦ b ⟧ (v ← v? ⁏
                π₂-reduce v)
⟦snd⟧ (v , ⇓v , ⟦v⟧) =
      let (c₁ , c₂)         = ⟦v⟧
          (v₂ , ⇓v₂ , ⟦v₂⟧) = c₂
      in  (v₂ , ⇓bind ⇓v ⇓v₂ , ⟦v₂⟧)


⟦unit⟧ : ∀ {Δ} → C⟦_⟧_ {Δ} ⊤ (now unit)
⟦unit⟧ = (unit , ⇓now , unit)


term : ∀ {Γ Δ a} (t : Tm Γ a) (ρ : Env Δ Γ) (⟦ρ⟧ : E⟦ Γ ⟧ ρ) → C⟦ a ⟧ (eval t ρ)
term (loop t)   ρ ⟦ρ⟧ = ⟦loop⟧ (term t ρ ⟦ρ⟧)
term (var x)    ρ ⟦ρ⟧ = ⟦var⟧ x ρ ⟦ρ⟧
term (lam t)    ρ ⟦ρ⟧ = ⟦lam⟧ t ρ ⟦ρ⟧ (λ η w ⟦w⟧ → term t (ren-env η ρ , w)
                                                           (ren-E⟦⟧ η ρ ⟦ρ⟧ , ⟦w⟧))
term (app t u)  ρ ⟦ρ⟧ = ⟦app⟧ (term t ρ ⟦ρ⟧) (term u ρ ⟦ρ⟧)
term (pair t u) ρ ⟦ρ⟧ = ⟦pair⟧ t u ρ ⟦ρ⟧ (term t ρ ⟦ρ⟧) (term u ρ ⟦ρ⟧)
term (fst t)    ρ ⟦ρ⟧ = ⟦fst⟧ (term t ρ ⟦ρ⟧)
term (snd t)    ρ ⟦ρ⟧ = ⟦snd⟧ (term t ρ ⟦ρ⟧)
term unit       ρ ⟦ρ⟧ = ⟦unit⟧


⟦id-env⟧ : (Γ : Cx) → E⟦ Γ ⟧ (id-env Γ)
⟦id-env⟧ ∅       = unit
⟦id-env⟧ (Γ , a) =
      let ρ = ren-E⟦⟧ wk (id-env Γ) (⟦id-env⟧ Γ)
          v = reflect-var {Γ = Γ , a} top
      in  (ρ , v)

normalize : (Γ : Cx) (a : Ty) (t : Tm Γ a) → ∃ λ n → nf? t ⇓ n
normalize Γ a t =
      let (v , ⇓v , ⟦v⟧) = term t (id-env Γ) (⟦id-env⟧ Γ)
          (n , ⇓n)       = reify a v ⟦v⟧
      in  (n , ⇓bind ⇓v ⇓n)

nf : ∀ {Γ a} → Tm Γ a → Nf Γ a
nf {Γ} {a} t =
      let (n , ⇓n) = normalize Γ a t
      in  n
