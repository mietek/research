module BasicIPC.Gentzen.TarskiSoundness where

open import BasicIPC.Gentzen public
open import BasicIPC.TarskiSemantics public




module NaturalSoundness where
  open NaturalSemantics public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)    γ = lookup i γ
  eval (lam t)    γ = λ a → eval t (γ , a)
  eval (app t u)  γ = (eval t γ) (eval u γ)
  eval (pair t u) γ = eval t γ , eval u γ
  eval (fst t)    γ = π₁ (eval t γ)
  eval (snd t)    γ = π₂ (eval t γ)
  eval tt         γ = ∙


  -- Correctness of evaluation with respect to conversion.

  -- FIXME: How to show this?
  postulate
    oops₁ : ∀ {{_ : Model}} {A B Γ} {t : Γ , A ⊢ B} {u : Γ ⊢ A}
            → eval ([ top ≔ u ] t) ≡ (λ γ → eval t (γ , eval u γ))
    oops₂ : ∀ {{_ : Model}} {A B Γ} {t : Γ ⊢ A ▻ B}
            → eval t ≡ (λ γ a → eval (mono⊢ (weak⊆ {A = A}) t) (γ , a) a)

  check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒                    = refl
  check (trans⇒ p q)             = trans (check p) (check q)
  check (sym⇒ p)                 = sym (check p)
  check (conglam⇒ {A} {B} p)     = cong (λˢ {A} {B}) (check p)
  check (congapp⇒ {A} {B} p q)   = cong₂ (_$ˢᶜ_ {A} {B}) (check p) (check q)
  check (congpair⇒ {A} {B} p q)  = cong₂ (_,ˢᶜ_ {A} {B}) (check p) (check q)
  check (congfst⇒ {A} {B} p)     = cong (π₁ˢᶜ {A} {B}) (check p)
  check (congsnd⇒ {A} {B} p)     = cong (π₂ˢᶜ {A} {B}) (check p)
  check (beta▻⇒ {A} {B} {t} {u}) = sym (oops₁ {A} {B} {_} {t} {u})
  check (eta▻⇒ {A} {B} {t})      = oops₂ {A} {B} {_} {t}
  check beta∧₁⇒                  = refl
  check beta∧₂⇒                  = refl
  check eta∧⇒                    = refl
  check eta⊤⇒                   = refl




-- NOTE: The Coquand-Dybjer variant of Tarski semantics does not work for Gentzen-style,
-- because we need to store information about open syntax in the model.
