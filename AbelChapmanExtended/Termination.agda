module AbelChapmanExtended.Termination where

open import Data.Product using (∃ ; _,_)
open import Data.Unit using () renaming (tt to unit)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Size using (∞)

open import AbelChapmanExtended.Delay
open import AbelChapmanExtended.Convergence

open import AbelChapmanExtended.Syntax
open import AbelChapmanExtended.OPE
open import AbelChapmanExtended.Renaming
open import AbelChapmanExtended.Normalization
open import AbelChapmanExtended.Semantics
open import AbelChapmanExtended.RenamingLemmas.OPE
open import AbelChapmanExtended.RenamingLemmas.Semantics
open import AbelChapmanExtended.Reflection




κ₁-reduce-sound : ∀ {Γ Δ a b c} (ul : Tm (Γ , a) c) (ur : Tm (Γ , b) c) →
                  (ρ : Env Δ Γ) {v : Val Δ a} →
                  C⟦ c ⟧ (eval ul (ρ , v)) →
                  C⟦ c ⟧ (κ-reduce (inl v) ul ur ρ)
κ₁-reduce-sound ul ur ρ (v′ , ⇓v′ , ⟦v′⟧) = (v′ , ⇓later ⇓v′ , ⟦v′⟧)


κ₂-reduce-sound : ∀ {Γ Δ a b c} (ul : Tm (Γ , a) c) (ur : Tm (Γ , b) c) →
                  (ρ : Env Δ Γ) {v : Val Δ b} →
                  C⟦ c ⟧ (eval ur (ρ , v)) →
                  C⟦ c ⟧ (κ-reduce (inr v) ul ur ρ)
κ₂-reduce-sound ul ur ρ (v′ , ⇓v′ , ⟦v′⟧) = (v′ , ⇓later ⇓v′ , ⟦v′⟧)


β-reduce-sound : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) {w : Val Δ a} →
                 C⟦ b ⟧ (eval t (ρ , w)) →
                 C⟦ b ⟧ (β-reduce (lam t ρ) w)
β-reduce-sound t ρ (vw , ⇓vw , ⟦vw⟧) = (vw , ⇓later ⇓vw , ⟦vw⟧)


⟦boom⟧ : ∀ {Δ c} {v? : Delay ∞ (Val Δ ⊥)} →
         C⟦ ⊥ ⟧ v? →
         C⟦ c ⟧ (v ← v? ⁏
                 ω-reduce v)
⟦boom⟧ {c = c} (ne v , ⇓v , (n , ⇓n)) =
      let v′   = ne (boom v)
          ⟦v′⟧ = reflect c (boom v) (boom n , ⇓map boom ⇓n)
      in  (v′ , ⇓bind ⇓v ⇓now , ⟦v′⟧)


⟦inl⟧ : ∀ {Δ a b} {v? : Delay ∞ (Val Δ a)} →
        C⟦ a ⟧ v? →
        C⟦ a ∨ b ⟧ (v ← v? ⁏
                    now (inl v))
⟦inl⟧ (v , ⇓v , ⟦v⟧) =
      let ⟦v′⟧ = (v , ⇓now , ⟦v⟧)
      in  (inl v , ⇓bind ⇓v ⇓now , ⟦v′⟧)


⟦inr⟧ : ∀ {Δ a b} {v? : Delay ∞ (Val Δ b)} →
        C⟦ b ⟧ v? →
        C⟦ a ∨ b ⟧ (v ← v? ⁏
                    now (inr v))
⟦inr⟧ (v , ⇓v , ⟦v⟧) =
      let ⟦v′⟧ = (v , ⇓now , ⟦v⟧)
      in  (inr v , ⇓bind ⇓v ⇓now , ⟦v′⟧)


⟦case⟧ : ∀ {Γ Δ a b c} (t : Tm Γ (a ∨ b)) {v? : Delay ∞ (Val Δ (a ∨ b))} →
         (ul : Tm (Γ , a) c) (ur : Tm (Γ , b) c) (ρ : Env Δ Γ) (⟦ρ⟧ : E⟦ Γ ⟧ ρ) →
         C⟦ a ∨ b ⟧ v? →
         (∀ {Δ′} (η : Δ′ ⊇ Δ) (v : Val Δ′ a) (⟦v⟧ : V⟦ a ⟧ v) →
             C⟦ c ⟧ (eval ul (ren-env η ρ , v))) →
         (∀ {Δ′} (η : Δ′ ⊇ Δ) (v : Val Δ′ b) (⟦v⟧ : V⟦ b ⟧ v) →
             C⟦ c ⟧ (eval ur (ren-env η ρ , v))) →
         C⟦ c ⟧ (v ← v? ⁏
                 κ-reduce v ul ur ρ)
⟦case⟧ {a = a} {b} {c} t ul ur ρ ⟦ρ⟧ (ne v , ⇓v , (n , ⇓n)) hl hr =
      let (wl , ⇓wl , ⟦wl⟧) = hl wk nev₀ (reflect-var {a = a} top)
          (wr , ⇓wr , ⟦wr⟧) = hr wk nev₀ (reflect-var {a = b} top)
          (ml , ⇓ml)        = reify c wl ⟦wl⟧
          (mr , ⇓mr)        = reify c wr ⟦wr⟧
          n′                = case n ml mr
          ⇓n′               = ⇓bind ⇓n (⇓bind ⇓ml (⇓bind ⇓mr ⇓now))
          v′                = ne (case v wl wr)
          ⟦v′⟧              = reflect c (case v wl wr) (n′ , ⇓n′)
      in  (v′ , ⇓bind ⇓v (⇓bind ⇓wl (⇓bind ⇓wr ⇓now)) , ⟦v′⟧)
⟦case⟧ t ul ur ρ ⟦ρ⟧ (inl v , ⇓v , ⟦v⟧) hl hr =
      let (v′ , ⇓v′ , ⟦v′⟧) = ⟦v⟧
          dl                = subst (λ ρ → C⟦ _ ⟧ eval ul (ρ , v′))
                                    (ren-env-id ρ)
                                    (hl id v′ ⟦v′⟧)
          (v″ , ⇓v″ , ⟦v″⟧) = κ₁-reduce-sound ul ur ρ dl
      in  (v″ , ⇓bind ⇓v (⇓bind ⇓v′ ⇓v″) , ⟦v″⟧)
⟦case⟧ t ul ur ρ ⟦ρ⟧ (inr v , ⇓v , ⟦v⟧) hl hr =
      let (v′ , ⇓v′ , ⟦v′⟧) = ⟦v⟧
          dr                = subst (λ ρ → C⟦ _ ⟧ eval ur (ρ , v′))
                                    (ren-env-id ρ)
                                    (hr id v′ ⟦v′⟧)
          (v″ , ⇓v″ , ⟦v″⟧) = κ₂-reduce-sound ul ur ρ dr
      in  (v″ , ⇓bind ⇓v (⇓bind ⇓v′ ⇓v″) , ⟦v″⟧)


⟦var⟧ : ∀ {Γ Δ a} (x : Var Γ a) (ρ : Env Δ Γ) →
        E⟦ Γ ⟧ ρ → C⟦ a ⟧ (now (lookup x ρ))
⟦var⟧ top     (ρ , v) (⟦ρ⟧ , ⟦v⟧) = (v , ⇓now , ⟦v⟧)
⟦var⟧ (pop x) (ρ , v) (⟦ρ⟧ , ⟦v⟧) = ⟦var⟧ x ρ ⟦ρ⟧


⟦lam⟧ : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (⟦ρ⟧ : E⟦ Γ ⟧ ρ) →
        (∀ {Δ′} (η : Δ′ ⊇ Δ) (w : Val Δ′ a) (⟦w⟧ : V⟦ a ⟧ w) →
            C⟦ b ⟧ (eval t (ren-env η ρ , w))) →
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
          ⇓vw′              = subst (λ v → β-reduce v w ⇓ vw)
                                            (ren-val-id v)
                                            ⇓vw
      in  (vw , ⇓bind ⇓v (⇓bind ⇓w ⇓vw′) , ⟦vw⟧)


⟦pair⟧ : ∀ {Γ Δ a b} (t : Tm Γ a) (u : Tm Γ b) (ρ : Env Δ Γ) (⟦ρ⟧ : E⟦ Γ ⟧ ρ) →
         C⟦ a ⟧ (eval t ρ) → C⟦ b ⟧ (eval u ρ) →
         C⟦ a ∧ b ⟧ (v ← eval t ρ ⁏
                     w ← eval u ρ ⁏
                     now (pair v w))
⟦pair⟧ t u ρ ⟦ρ⟧ (v , ⇓v , ⟦v⟧) (w , ⇓w , ⟦w⟧) =
      let c = (v , ⇓now , ⟦v⟧)
          d = (w , ⇓now , ⟦w⟧)
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
term (boom t)       ρ ⟦ρ⟧ = ⟦boom⟧ (term t ρ ⟦ρ⟧)
term (inl t)        ρ ⟦ρ⟧ = ⟦inl⟧ (term t ρ ⟦ρ⟧)
term (inr t)        ρ ⟦ρ⟧ = ⟦inr⟧ (term t ρ ⟦ρ⟧)
term (case t ul ur) ρ ⟦ρ⟧ = ⟦case⟧ t ul ur ρ ⟦ρ⟧ (term t ρ ⟦ρ⟧)
                              (λ η v ⟦v⟧ → term ul (ren-env η ρ , v)
                                                    (ren-E⟦⟧ η ρ ⟦ρ⟧ , ⟦v⟧))
                              (λ η v ⟦v⟧ → term ur (ren-env η ρ , v)
                                                    (ren-E⟦⟧ η ρ ⟦ρ⟧ , ⟦v⟧))
term (var x)        ρ ⟦ρ⟧ = ⟦var⟧ x ρ ⟦ρ⟧
term (lam t)        ρ ⟦ρ⟧ = ⟦lam⟧ t ρ ⟦ρ⟧
                              (λ η w ⟦w⟧ → term t (ren-env η ρ , w)
                                                   (ren-E⟦⟧ η ρ ⟦ρ⟧ , ⟦w⟧))
term (app t u)      ρ ⟦ρ⟧ = ⟦app⟧ (term t ρ ⟦ρ⟧) (term u ρ ⟦ρ⟧)
term (pair t u)     ρ ⟦ρ⟧ = ⟦pair⟧ t u ρ ⟦ρ⟧ (term t ρ ⟦ρ⟧) (term u ρ ⟦ρ⟧)
term (fst t)        ρ ⟦ρ⟧ = ⟦fst⟧ (term t ρ ⟦ρ⟧)
term (snd t)        ρ ⟦ρ⟧ = ⟦snd⟧ (term t ρ ⟦ρ⟧)
term unit           ρ ⟦ρ⟧ = ⟦unit⟧


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
