module AbelChapmanExtended.RenamingLemmas.OPE where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)

open import AbelChapmanExtended.OPE
open import AbelChapmanExtended.Renaming
open import AbelChapmanExtended.Syntax


cong₃ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {D : Set ℓ‴}
        {a a′ b b′ c c′} (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′ →
        f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl


mutual
  ren-var-id : ∀ {Δ a} (x : Var Δ a) → ren-var id x ≡ x
  ren-var-id top     = refl
  ren-var-id (pop x) = cong pop (ren-var-id x)

  ren-nev-id : ∀ {Δ a} (v : Ne Val Δ a) → ren-nev id v ≡ v
  ren-nev-id (boom v)       = cong boom (ren-nev-id v)
  ren-nev-id (case v wl wr) = cong₃ case (ren-nev-id v)
                                         (ren-val-id wl)
                                         (ren-val-id wr)
  ren-nev-id (var x)        = cong var (ren-var-id x)
  ren-nev-id (app v w)      = cong₂ app (ren-nev-id v) (ren-val-id w)
  ren-nev-id (fst v)        = cong fst (ren-nev-id v)
  ren-nev-id (snd v)        = cong snd (ren-nev-id v)

  ren-val-id : ∀ {Δ a} (v : Val Δ a) → ren-val id v ≡ v
  ren-val-id (ne v)     = cong ne (ren-nev-id v)
  ren-val-id (inl v)    = cong inl (ren-val-id v)
  ren-val-id (inr v)    = cong inr (ren-val-id v)
  ren-val-id (lam t ρ)  = cong (lam t) (ren-env-id ρ)
  ren-val-id (pair v w) = cong₂ pair (ren-val-id v) (ren-val-id w)
  ren-val-id unit       = refl

  ren-env-id : ∀ {Γ Δ} (ρ : Env Δ Γ) → ren-env id ρ ≡ ρ
  ren-env-id ∅       = refl
  ren-env-id (ρ , v) = cong₂ _,_ (ren-env-id ρ) (ren-val-id v)


mutual
  ren-var-• : ∀ {Δ Δ′ Δ″ a} (η′ : Δ″ ⊇ Δ′) (η : Δ′ ⊇ Δ) (x : Var Δ a) →
              (ren-var η′ ∘ ren-var η) x ≡ ren-var (η′ • η) x
  ren-var-• base      η        x       = refl
  ren-var-• (weak η′) η        x       = cong pop (ren-var-• η′ η x)
  ren-var-• (lift η′) (weak η) x       = cong pop (ren-var-• η′ η x)
  ren-var-• (lift η′) (lift η) top     = refl
  ren-var-• (lift η′) (lift η) (pop x) = cong pop (ren-var-• η′ η x)

  ren-nev-• : ∀ {Δ Δ′ Δ″ a} (η′ : Δ″ ⊇ Δ′) (η : Δ′ ⊇ Δ) (v : Ne Val Δ a) →
              (ren-nev η′ ∘ ren-nev η) v ≡ ren-nev (η′ • η) v
  ren-nev-• η′ η (boom v)       = cong boom (ren-nev-• η′ η v)
  ren-nev-• η′ η (case v wl wr) = cong₃ case (ren-nev-• η′ η v)
                                             (ren-val-• (lift η′) (lift η) wl)
                                             (ren-val-• (lift η′) (lift η) wr)
  ren-nev-• η′ η (var x)        = cong var (ren-var-• η′ η x)
  ren-nev-• η′ η (app v w)      = cong₂ app (ren-nev-• η′ η v) (ren-val-• η′ η w)
  ren-nev-• η′ η (fst v)        = cong fst (ren-nev-• η′ η v)
  ren-nev-• η′ η (snd v)        = cong snd (ren-nev-• η′ η v)

  ren-val-• : ∀ {Δ Δ′ Δ″ a} (η′ : Δ″ ⊇ Δ′) (η : Δ′ ⊇ Δ) (v : Val Δ a) →
              (ren-val η′ ∘ ren-val η) v ≡ ren-val (η′ • η) v
  ren-val-• η′ η (ne w)     = cong ne (ren-nev-• η′ η w)
  ren-val-• η′ η (inl v)    = cong inl (ren-val-• η′ η v)
  ren-val-• η′ η (inr v)    = cong inr (ren-val-• η′ η v)
  ren-val-• η′ η (lam t ρ)  = cong (lam t) (ren-env-• η′ η ρ)
  ren-val-• η′ η (pair v w) = cong₂ pair (ren-val-• η′ η v) (ren-val-• η′ η w)
  ren-val-• η′ η unit       = refl

  ren-env-• : ∀ {Γ Δ Δ′ Δ″} (η′ : Δ″ ⊇ Δ′) (η : Δ′ ⊇ Δ) (ρ : Env Δ Γ) →
              (ren-env η′ ∘ ren-env η) ρ ≡ ren-env (η′ • η) ρ
  ren-env-• η′ η ∅       = refl
  ren-env-• η′ η (ρ , v) = cong₂ _,_ (ren-env-• η′ η ρ) (ren-val-• η′ η v)
