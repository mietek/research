module AbelChapmanExtended.Renaming where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)

open import AbelChapmanExtended.Syntax




data _≥_ : (Γ Γ′ : Cx) → Set where
  id   : ∀ {Γ}                → Γ        ≥ Γ
  weak : ∀ {Γ Γ′ a} → Γ′ ≥ Γ → (Γ′ , a) ≥ Γ
  lift : ∀ {Γ Γ′ a} → Γ′ ≥ Γ → (Γ′ , a) ≥ (Γ , a)


_•_ : ∀ {Γ Γ′ Γ″} → Γ″ ≥ Γ′ → Γ′ ≥ Γ → Γ″ ≥ Γ
id     • ρ′      = ρ′
weak ρ • ρ′      = weak (ρ • ρ′)
lift ρ • id      = lift ρ
lift ρ • weak ρ′ = weak (ρ • ρ′)
lift ρ • lift ρ′ = lift (ρ • ρ′)


ρ•id : ∀ {Γ Γ′} (ρ : Γ ≥ Γ′) → ρ • id ≡ ρ
ρ•id id       = refl
ρ•id (weak ρ) = cong weak (ρ•id ρ)
ρ•id (lift ρ) = refl

id•ρ : ∀ {Γ Γ′} (ρ : Γ ≥ Γ′) → id • ρ ≡ ρ
id•ρ id       = refl
id•ρ (weak ρ) = refl
id•ρ (lift ρ) = cong lift (id•ρ ρ)


•assoc : ∀ {Γ Γ′ Γ″ Γ‴} (ρ″ : Γ‴ ≥ Γ″) (ρ′ : Γ″ ≥ Γ′) (ρ : Γ′ ≥ Γ) →
         (ρ″ • ρ′) • ρ ≡ ρ″ • (ρ′ • ρ)
•assoc id        ρ′        ρ        = refl
•assoc (weak ρ″) ρ′        ρ        = cong weak (•assoc ρ″ ρ′ ρ)
•assoc (lift ρ″) id        ρ        = refl
•assoc (lift ρ″) (weak ρ′) ρ        = cong weak (•assoc ρ″ ρ′ ρ)
•assoc (lift ρ″) (lift ρ′) id       = refl
•assoc (lift ρ″) (lift ρ′) (weak ρ) = cong weak (•assoc ρ″ ρ′ ρ)
•assoc (lift ρ″) (lift ρ′) (lift ρ) = cong lift (•assoc ρ″ ρ′ ρ)


Ren : ∀ {X : Set} → (Cx → X → Set) → Cx → Cx → Set
Ren Ξ Γ Γ′ = ∀ {x} → Ξ Γ x → Ξ Γ′ x


mutual
  ren-var : ∀ {Γ Γ′} → Γ′ ≥ Γ → Ren Var Γ Γ′
  ren-var id       x       = x
  ren-var (weak ρ) x       = pop (ren-var ρ x)
  ren-var (lift ρ) top     = top
  ren-var (lift ρ) (pop x) = pop (ren-var ρ x)


  ren-nen : ∀ {Δ Δ′} → Δ′ ≥ Δ → Ren (Ne Nf) Δ Δ′
  ren-nen ρ (var x)   = var (ren-var ρ x)
  ren-nen ρ (app n m) = app (ren-nen ρ n) (ren-nf ρ m)
  ren-nen ρ (fst n)   = fst (ren-nen ρ n)
  ren-nen ρ (snd n)   = snd (ren-nen ρ n)


  ren-nev : ∀ {Δ Δ′} → Δ′ ≥ Δ → Ren (Ne Val) Δ Δ′
  ren-nev ρ (var x)   = var (ren-var ρ x)
  ren-nev ρ (app v w) = app (ren-nev ρ v) (ren-val ρ w)
  ren-nev ρ (fst v)   = fst (ren-nev ρ v)
  ren-nev ρ (snd v)   = snd (ren-nev ρ v)


  ren-nf : ∀ {Δ Δ′} → Δ′ ≥ Δ → Ren Nf Δ Δ′
  ren-nf ρ (ne n)     = ne (ren-nen ρ n)
  ren-nf ρ (lam n)    = lam (ren-nf (lift ρ) n)
  ren-nf ρ unit       = unit
  ren-nf ρ (pair n m) = pair (ren-nf ρ n) (ren-nf ρ m)


  ren-val : ∀ {Δ Δ′} → Δ′ ≥ Δ → Ren Val Δ Δ′
  ren-val ρ (ne n)     = ne (ren-nev ρ n)
  ren-val ρ (lam t γ)  = lam t (ren-env ρ γ)
  ren-val ρ unit       = unit
  ren-val ρ (pair v w) = pair (ren-val ρ v) (ren-val ρ w)


  ren-env : ∀ {Δ Δ′} → Δ′ ≥ Δ → Ren Env Δ Δ′
  ren-env ρ ∅       = ∅
  ren-env ρ (γ , v) = ren-env ρ γ , ren-val ρ v


mutual
  ren-var-id : ∀ {Δ a} (x : Var Δ a) → ren-var id x ≡ x
  ren-var-id x = refl


  ren-nev-id : ∀ {Δ a} (v : Ne Val Δ a) → ren-nev id v ≡ v
  ren-nev-id (var x)   = refl
  ren-nev-id (app v w) = cong₂ app (ren-nev-id v) (ren-val-id w)
  ren-nev-id (fst v)   = cong fst (ren-nev-id v)
  ren-nev-id (snd v)   = cong snd (ren-nev-id v)


  ren-val-id : ∀ {Δ a} (v : Val Δ a) → ren-val id v ≡ v
  ren-val-id (ne v)     = cong ne (ren-nev-id v)
  ren-val-id (lam t γ)  = cong (lam t) (ren-env-id γ)
  ren-val-id unit       = refl
  ren-val-id (pair v w) = cong₂ pair (ren-val-id v) (ren-val-id w)


  ren-env-id : ∀ {Γ Δ} (γ : Env Δ Γ) → ren-env id γ ≡ γ
  ren-env-id ∅       = refl
  ren-env-id (γ , v) = cong₂ _,_ (ren-env-id γ) (ren-val-id v)


mutual
  ren-var-• : ∀ {Δ Δ′ Δ″ a} (ρ′ : Δ″ ≥ Δ′) (ρ : Δ′ ≥ Δ) (x : Var Δ a) →
              (ren-var ρ′ ∘ ren-var ρ) x ≡ ren-var (ρ′ • ρ) x
  ren-var-• id        ρ        x       = refl
  ren-var-• (weak ρ′) ρ        x       = cong pop (ren-var-• ρ′ ρ x)
  ren-var-• (lift ρ′) id       x       = refl
  ren-var-• (lift ρ′) (weak ρ) x       = cong pop (ren-var-• ρ′ ρ x)
  ren-var-• (lift ρ′) (lift ρ) top     = refl
  ren-var-• (lift ρ′) (lift ρ) (pop x) = cong pop (ren-var-• ρ′ ρ x)


  ren-nev-• : ∀ {Δ Δ′ Δ″ a} (ρ′ : Δ″ ≥ Δ′) (ρ : Δ′ ≥ Δ) (v : Ne Val Δ a) →
              (ren-nev ρ′ ∘ ren-nev ρ) v ≡ ren-nev (ρ′ • ρ) v
  ren-nev-• ρ′ ρ (var x)   = cong var (ren-var-• ρ′ ρ x)
  ren-nev-• ρ′ ρ (app v w) = cong₂ app (ren-nev-• ρ′ ρ v) (ren-val-• ρ′ ρ w)
  ren-nev-• ρ′ ρ (fst v)   = cong fst (ren-nev-• ρ′ ρ v)
  ren-nev-• ρ′ ρ (snd v)   = cong snd (ren-nev-• ρ′ ρ v)


  ren-val-• : ∀ {Δ Δ′ Δ″ a} (ρ′ : Δ″ ≥ Δ′) (ρ : Δ′ ≥ Δ) (v : Val Δ a) →
              (ren-val ρ′ ∘ ren-val ρ) v ≡ ren-val (ρ′ • ρ) v
  ren-val-• ρ′ ρ (ne w)     = cong ne (ren-nev-• ρ′ ρ w)
  ren-val-• ρ′ ρ (lam t γ)  = cong (lam t) (ren-env-• ρ′ ρ γ)
  ren-val-• ρ′ ρ unit       = refl
  ren-val-• ρ′ ρ (pair v w) = cong₂ pair (ren-val-• ρ′ ρ v) (ren-val-• ρ′ ρ w)


  ren-env-• : ∀ {Γ Δ Δ′ Δ″} (ρ′ : Δ″ ≥ Δ′) (ρ : Δ′ ≥ Δ) (γ : Env Δ Γ) →
              (ren-env ρ′ ∘ ren-env ρ) γ ≡ ren-env (ρ′ • ρ) γ
  ren-env-• ρ′ ρ ∅       = refl
  ren-env-• ρ′ ρ (γ , v) = cong₂ _,_ (ren-env-• ρ′ ρ γ) (ren-val-• ρ′ ρ v)




-- module NonStandardLibrary where
--   open import Categories.Category using (Category)
--   open import Function using (flip)
--   open import Relation.Binary.PropositionalEquality using (sym ; cong₂ ; isEquivalence)
--
--   OPE : Category _ _ _
--   OPE = record
--     { Obj       = Cx
--     ; _⇒_      = _≥_
--     ; _≡_       = _≡_
--     ; _∘_       = flip _•_
--     ; id        = id
--     ; assoc     = λ {_} {_} {_} {_} {ρ} {ρ′} {ρ″} → sym (•assoc ρ ρ′ ρ″)
--     ; identityˡ = λ {_} {_} {ρ} → ρ•id ρ
--     ; identityʳ = λ {_} {_} {ρ} → id•ρ ρ
--     ; equiv     = isEquivalence
--     ; ∘-resp-≡  = cong₂ (flip _•_)
--     }
