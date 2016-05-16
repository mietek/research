module AbelChapmanExtended.Reflection where

open import Data.Product using (_,_)
open import Data.Unit using () renaming (tt to unit)

open import AbelChapmanExtended.Convergence
open import AbelChapmanExtended.Normalization
open import AbelChapmanExtended.Renaming
open import AbelChapmanExtended.RenamingLemmas.Convergence
open import AbelChapmanExtended.Semantics
open import AbelChapmanExtended.Syntax




mutual
  reify : ∀ {Γ} (a : Ty) (v : Val Γ a) → V⟦ a ⟧ v → readback v ⇓
  reify ⊥       (ne v)  (n , ⇓n)          = (ne n , ⇓map ne ⇓n)
  reify (a ∨ b)  (ne v)  (n , ⇓n)          = (ne n , ⇓map ne ⇓n)
  reify (a ∨ b)  (inl v) (.v , ⇓now , ⟦v⟧) =
        let (n , ⇓n) = reify a v ⟦v⟧
        in  (inl n , ⇓map inl ⇓n)
  reify (a ∨ b)  (inr v) (.v , ⇓now , ⟦v⟧) =
        let (n , ⇓n) = reify b v ⟦v⟧
        in  (inr n , ⇓map inr ⇓n)
  reify (a ⇒ b) v       ⟦v⟧               =
        let w                 = nev₀
            ⟦w⟧               = reflect-var {a = a} top
            (vw , ⇓vw , ⟦vw⟧) = ⟦v⟧ wk w ⟦w⟧
            (n , ⇓n)          = reify b vw ⟦vw⟧
            ⇓λn               = ⇓bind ⇓vw (⇓bind ⇓n ⇓now)
        in  (lam n , ⇓later ⇓λn)
  reify (a ∧ b)  v       (c₁ , c₂)         =
        let (v₁ , ⇓v₁ , ⟦v₁⟧) = c₁
            (v₂ , ⇓v₂ , ⟦v₂⟧) = c₂
            (n₁ , ⇓n₁)        = reify a v₁ ⟦v₁⟧
            (n₂ , ⇓n₂)        = reify b v₂ ⟦v₂⟧
            ⇓ψn               = ⇓bind ⇓v₁ (⇓bind ⇓v₂ (⇓bind ⇓n₁ (⇓bind ⇓n₂ ⇓now)))
        in  (pair n₁ n₂ , ⇓later ⇓ψn)
  reify ⊤       v       ⟦v⟧               = (unit , ⇓now)


  reflect : ∀ {Γ} (a : Ty) (v : Ne Val Γ a) → readback-ne v ⇓ → V⟦ a ⟧ (ne v)
  reflect ⊥       v ⟦v⟧      = ⟦v⟧
  reflect (a ∨ b)  v ⟦v⟧      = ⟦v⟧
  reflect (a ⇒ b) v (n , ⇓n) = λ η w ⟦w⟧ →
        let (m , ⇓m) = reify a w ⟦w⟧
            n′       = ren-nen η n
            ⇓n′      = ⇓ren-readback-ne η v ⇓n
            vw       = app (ren-nev η v) w
            ⟦vw⟧     = reflect b vw (app n′ m , ⇓bind ⇓n′ (⇓bind ⇓m ⇓now))
        in  (ne vw , ⇓now , ⟦vw⟧)
  reflect (a ∧ b)  v (n , ⇓n) =
        let v₁   = fst v
            v₂   = snd v
            ⟦v₁⟧ = reflect a v₁ (fst n , ⇓bind ⇓n ⇓now)
            ⟦v₂⟧ = reflect b v₂ (snd n , ⇓bind ⇓n ⇓now)
        in  (ne v₁ , ⇓now , ⟦v₁⟧) , (ne v₂ , ⇓now , ⟦v₂⟧)
  reflect ⊤       v ⟦v⟧      = unit


  reflect-var : ∀ {Γ a} (x : Var Γ a) → V⟦ a ⟧ ne (var x)
  reflect-var {a = a} x = reflect a (var x) (var x , ⇓now)
