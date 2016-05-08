module AbelChapmanExtended.Termination where

open import Data.Product using (∃ ; _×_ ; _,_)
open import Data.Unit using () renaming (⊤ to Unit ; tt to unit)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Size using (∞)

open import AbelChapmanExtended.Convergence
open import AbelChapmanExtended.Delay
open import AbelChapmanExtended.Normalization
open import AbelChapmanExtended.Renaming
open import AbelChapmanExtended.Syntax
open import AbelChapmanExtended.Termination.Eval
open import AbelChapmanExtended.Termination.Readback




mutual
  V⟦_⟧_ : ∀ {Γ} (a : Ty) → Val Γ a → Set
  V⟦ ★ ⟧      ne v = readback-ne v ⇓
  V⟦ a ⇒ b ⟧ v    = ∀ {Δ} (ρ : Δ ≥ _) (w : Val Δ a) →
                     V⟦ a ⟧ w → C⟦ b ⟧ (β-reduce (ren-val ρ v) w)
  V⟦ ⊤ ⟧     v    = Unit
  V⟦ a ∧ b ⟧  v    = C⟦ a ⟧ (π₁-reduce v) × C⟦ b ⟧ (π₂-reduce v)


  C⟦_⟧_ : ∀ {Γ} (a : Ty) → Delay ∞ (Val Γ a) → Set
  C⟦ a ⟧ v? = ∃ λ v → v? ⇓ v × V⟦ a ⟧ v


E⟦_⟧_ : ∀ {Δ} (Γ : Cx) → Env Δ Γ → Set
E⟦ ∅ ⟧     ∅       = Unit
E⟦ Γ , a ⟧ (γ , v) = E⟦ Γ ⟧ γ × V⟦ a ⟧ v


⇓ren-readback-ne : ∀ {Δ Δ′ a} (ρ : Δ′ ≥ Δ) (v : Ne Val Δ a) {v′ : Ne Nf Δ a} →
                   readback-ne v ⇓ v′ → readback-ne (ren-nev ρ v) ⇓ ren-nen ρ v′
⇓ren-readback-ne ρ v ⇓v′ = ⇓≈subst (⇓map (ren-nen ρ) ⇓v′) (ren-readback-ne ρ v)


⇓ren-π₁-reduce : ∀ {Δ Δ′ a b} (ρ : Δ′ ≥ Δ) (v : Val Δ (a ∧ b)) {v′ : Val Δ a} →
                 π₁-reduce v ⇓ v′ → π₁-reduce (ren-val ρ v) ⇓ ren-val ρ v′
⇓ren-π₁-reduce ρ v ⇓v′ = ⇓≈subst (⇓map (ren-val ρ) ⇓v′) (ren-π₁-reduce ρ v)


⇓ren-π₂-reduce : ∀ {Δ Δ′ a b} (ρ : Δ′ ≥ Δ) (v : Val Δ (a ∧ b)) {v′ : Val Δ b} →
                 π₂-reduce v ⇓ v′ → π₂-reduce (ren-val ρ v) ⇓ ren-val ρ v′
⇓ren-π₂-reduce ρ v ⇓v′ = ⇓≈subst (⇓map (ren-val ρ) ⇓v′) (ren-π₂-reduce ρ v)


ren-V⟦⟧ : ∀ {Δ Δ′} (a : Ty) (ρ : Δ′ ≥ Δ) (v : Val Δ a) →
          V⟦ a ⟧ v → V⟦ a ⟧ (ren-val ρ v)
ren-V⟦⟧ ★        ρ (ne v) (v′ , ⇓v′)   = (ren-nen ρ v′ , ⇓ren-readback-ne ρ v ⇓v′)
ren-V⟦⟧ (a ⇒ b) ρ v      ⟦v⟧ ρ′ w ⟦w⟧ =
      let (vw , ⇓vw , ⟦vw⟧) = ⟦v⟧ (ρ′ • ρ) w ⟦w⟧
          ⇓vw′              = subst (λ v′ → β-reduce v′ w ⇓ vw)
                                    (sym (ren-val-• ρ′ ρ v))
                                    ⇓vw
      in  (vw , ⇓vw′ , ⟦vw⟧)
ren-V⟦⟧ ⊤       ρ v      unit         = unit
ren-V⟦⟧ (a ∧ b)  ρ v      (c₁ , c₂)    =
      let (v₁ , ⇓v₁ , ⟦v₁⟧) = c₁
          (v₂ , ⇓v₂ , ⟦v₂⟧) = c₂
          v₁′               = ren-val ρ v₁
          v₂′               = ren-val ρ v₂
          ⇓v₁′              = ⇓ren-π₁-reduce ρ v ⇓v₁
          ⇓v₂′              = ⇓ren-π₂-reduce ρ v ⇓v₂
          ⟦v₁⟧′             = ren-V⟦⟧ a ρ v₁ ⟦v₁⟧
          ⟦v₂⟧′             = ren-V⟦⟧ b ρ v₂ ⟦v₂⟧
      in  (v₁′ , ⇓v₁′ , ⟦v₁⟧′) , (v₂′ , ⇓v₂′ , ⟦v₂⟧′)


ren-E⟦⟧ : ∀ {Γ Δ Δ′} (ρ : Δ′ ≥ Δ) (γ : Env Δ Γ) →
          E⟦ Γ ⟧ γ → E⟦ Γ ⟧ (ren-env ρ γ)
ren-E⟦⟧ ρ ∅       unit        = unit
ren-E⟦⟧ ρ (γ , v) (⟦γ⟧ , ⟦v⟧) = (ren-E⟦⟧ ρ γ ⟦γ⟧ , ren-V⟦⟧ _ ρ v ⟦v⟧)


β-reduce-sound : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (γ : Env Δ Γ) {w : Val Δ a} →
                 C⟦ b ⟧ (eval t (γ , w)) → C⟦ b ⟧ (β-reduce (lam t γ) w)
β-reduce-sound t γ (v , ⇓v , ⟦v⟧) = (v , ⇓later ⇓v , ⟦v⟧)


⟦var⟧ : ∀ {Γ Δ a} (x : Var Γ a) (γ : Env Δ Γ) →
        E⟦ Γ ⟧ γ → C⟦ a ⟧ (now (lookup x γ))
⟦var⟧ top     (γ , v) (⟦γ⟧ , ⟦v⟧) = (v , ⇓now , ⟦v⟧)
⟦var⟧ (pop x) (γ , v) (⟦γ⟧ , ⟦v⟧) = ⟦var⟧ x γ ⟦γ⟧


⟦lam⟧ : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (γ : Env Δ Γ) (⟦γ⟧ : E⟦ Γ ⟧ γ) →
        (∀ {Δ′} (ρ : Δ′ ≥ Δ) (w : Val Δ′ a) (⟦w⟧ : V⟦ a ⟧ w) → C⟦ b ⟧ (eval t (ren-env ρ γ , w))) →
        C⟦ a ⇒ b ⟧ (now (lam t γ))
⟦lam⟧ t γ ⟦γ⟧ h = (lam t γ , ⇓now , (λ ρ w ⟦w⟧ → β-reduce-sound t (ren-env ρ γ) (h ρ w ⟦w⟧)))


⟦app⟧ : ∀ {Δ a b} {v? : Delay ∞ (Val Δ (a ⇒ b))} {w? : Delay ∞ (Val Δ a)} →
        C⟦ a ⇒ b ⟧ v? → C⟦ a ⟧ w? →
        C⟦ b ⟧ (v ← v? ⁏
                w ← w? ⁏
                β-reduce v w)
⟦app⟧ {w? = w?} (v , ⇓v , ⟦v⟧) (w , ⇓w , ⟦w⟧) =
      let (vw , ⇓vw , ⟦vw⟧) = ⟦v⟧ id w ⟦w⟧
          ⇓vw′              = ⇓bind ⇓v (⇓bind ⇓w (subst (λ v → β-reduce v w ⇓ vw)
                                                        (ren-val-id v)
                                                        ⇓vw))
      in  (vw , ⇓vw′ , ⟦vw⟧)


⟦unit⟧ : ∀ {Δ} → C⟦_⟧_ {Δ} ⊤ (now unit)
⟦unit⟧ = unit , ⇓now , unit


⟦pair⟧ : ∀ {Γ Δ a b} (t : Tm Γ a) (u : Tm Γ b) (γ : Env Δ Γ) (⟦γ⟧ : E⟦ Γ ⟧ γ) →
         C⟦ a ⟧ (eval t γ) → C⟦ b ⟧ (eval u γ) →
         C⟦ a ∧ b ⟧ (v ← eval t γ ⁏
                     w ← eval u γ ⁏
                     now (pair v w))
⟦pair⟧ t u γ ⟦γ⟧ (v , ⇓v , ⟦v⟧) (w , ⇓w , ⟦w⟧) =
      let c   = (v , ⇓now , ⟦v⟧)
          d   = (w , ⇓now , ⟦w⟧)
          ⇓z  = ⇓bind ⇓v (⇓bind ⇓w ⇓now)
      in  (pair v w , ⇓z , c , d)


⟦fst⟧ : ∀ {Δ a b} {v? : Delay ∞ (Val Δ (a ∧ b))} →
        C⟦ a ∧ b ⟧ v? →
        C⟦ a ⟧ (v ← v? ⁏
                π₁-reduce v)
⟦fst⟧ {v? = v?} (v , ⇓v , (c₁ , c₂)) =
      let (v₁ , ⇓v₁ , ⟦v₁⟧) = c₁
          ⇓v₁′              = ⇓bind ⇓v ⇓v₁
      in  (v₁ , ⇓v₁′ , ⟦v₁⟧)


⟦snd⟧ : ∀ {Δ a b} {v? : Delay ∞ (Val Δ (a ∧ b))} →
        C⟦ a ∧ b ⟧ v? →
        C⟦ b ⟧ (v ← v? ⁏
                π₂-reduce v)
⟦snd⟧ {v? = v?} (v , ⇓v , (c₁ , c₂)) =
      let (v₂ , ⇓v₂ , ⟦v₂⟧) = c₂
          ⇓v₂′              = ⇓bind ⇓v ⇓v₂
      in  (v₂ , ⇓v₂′ , ⟦v₂⟧)


term : ∀ {Γ Δ a} (t : Tm Γ a) (γ : Env Δ Γ) (⟦γ⟧ : E⟦ Γ ⟧ γ) → C⟦ a ⟧ (eval t γ)
term (var x)    γ ⟦γ⟧ = ⟦var⟧ x γ ⟦γ⟧
term (lam t)    γ ⟦γ⟧ = ⟦lam⟧ t γ ⟦γ⟧ (λ ρ w ⟦w⟧ → term t (ren-env ρ γ , w) (ren-E⟦⟧ ρ γ ⟦γ⟧ , ⟦w⟧))
term (app t u)  γ ⟦γ⟧ = ⟦app⟧ (term t γ ⟦γ⟧) (term u γ ⟦γ⟧)
term unit       γ ⟦γ⟧ = ⟦unit⟧
term (pair t u) γ ⟦γ⟧ = ⟦pair⟧ t u γ ⟦γ⟧ (term t γ ⟦γ⟧) (term u γ ⟦γ⟧)
term (fst t)    γ ⟦γ⟧ = ⟦fst⟧ (term t γ ⟦γ⟧)
term (snd t)    γ ⟦γ⟧ = ⟦snd⟧ (term t γ ⟦γ⟧)


mutual
  reify : ∀ {Γ} (a : Ty) (v : Val Γ a) → V⟦ a ⟧ v → readback v ⇓
  reify ★        (ne v) (n , ⇓n)  = ne n , ⇓map ne ⇓n
  reify (a ⇒ b) v      ⟦v⟧       =
        let w                 = ne (var top)
            ⟦w⟧               = reflect a (var top) (var top , ⇓now)
            (vw , ⇓vw , ⟦vw⟧) = ⟦v⟧ wk w ⟦w⟧
            (n , ⇓n)          = reify b vw ⟦vw⟧
            ⇓z                = ⇓later (⇓bind ⇓vw (⇓bind ⇓n ⇓now))
        in  (lam n , ⇓z)
  reify ⊤       v      ⟦v⟧       = unit , ⇓now
  reify (a ∧ b)  v      (c₁ , c₂) =
        let (v₁ , ⇓v₁ , ⟦v₁⟧) = c₁
            (v₂ , ⇓v₂ , ⟦v₂⟧) = c₂
            (n₁ , ⇓n₁)        = reify a v₁ ⟦v₁⟧
            (n₂ , ⇓n₂)        = reify b v₂ ⟦v₂⟧
            ⇓z                = ⇓later (⇓bind ⇓v₁ (⇓bind ⇓v₂ (⇓bind ⇓n₁ (⇓bind ⇓n₂ ⇓now))))
        in  (pair n₁ n₂ , ⇓z)

  reflect : ∀ {Γ} (a : Ty) (v : Ne Val Γ a) → readback-ne v ⇓ → V⟦ a ⟧ (ne v)
  reflect ★        v ⇓v       = ⇓v
  reflect (a ⇒ b) v (n , ⇓n) = λ ρ w ⟦w⟧ →
        let (m , ⇓m) = reify a w ⟦w⟧
            n′      = ren-nen ρ n
            ⇓n′     = ⇓ren-readback-ne ρ v ⇓n
            vw      = app (ren-nev ρ v) w
            ⟦vw⟧    = reflect b vw (app n′ m , ⇓bind ⇓n′ (⇓bind ⇓m ⇓now))
        in  (ne vw , ⇓now , ⟦vw⟧)
  reflect ⊤       v ⇓v       = unit
  reflect (a ∧ b) v (n , ⇓n)  =
        let v₁   = fst v
            v₂   = snd v
            ⟦v₁⟧ = reflect a v₁ (fst n , ⇓bind ⇓n ⇓now)
            ⟦v₂⟧ = reflect b v₂ (snd n , ⇓bind ⇓n ⇓now)
        in  (ne v₁ , ⇓now , ⟦v₁⟧) , (ne v₂ , ⇓now , ⟦v₂⟧)


reflect-var : ∀ {Γ a} (x : Var Γ a) → V⟦ a ⟧ ne (var x)
reflect-var {a = a} x = reflect a (var x) (var x , ⇓now)


⟦id-env⟧ : (Γ : Cx) → E⟦ Γ ⟧ (id-env Γ)
⟦id-env⟧ ∅       = unit
⟦id-env⟧ (Γ , a) = (ren-E⟦⟧ wk (id-env Γ) (⟦id-env⟧ Γ) , reflect-var {Γ = Γ , a} top)


normalize : (Γ : Cx) (a : Ty) (t : Tm Γ a) → ∃ λ n → nf? t ⇓ n
normalize Γ a t =
      let (v , ⇓v , ⟦v⟧) = term t (id-env Γ) (⟦id-env⟧ Γ)
          (n , ⇓n)       = reify a v ⟦v⟧
          ⇓n′            = ⇓bind ⇓v ⇓n
      in  (n , ⇓n′)


nf : ∀ {Γ a} → Tm Γ a → Nf Γ a
nf {Γ} {a} t =
      let (n , ⇓n) = normalize Γ a t
      in  n
