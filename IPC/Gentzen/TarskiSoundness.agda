module IPC.Gentzen.TarskiSoundness where

open import IPC.Gentzen public
open import IPC.TarskiSemantics public




module NaturalSoundness where
  open NaturalSemantics public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)      γ = lookup i γ
  eval (lam t)      γ = λ a → eval t (γ , a)
  eval (app t u)    γ = (eval t γ) (eval u γ)
  eval (pair t u)   γ = eval t γ , eval u γ
  eval (fst t)      γ = π₁ (eval t γ)
  eval (snd t)      γ = π₂ (eval t γ)
  eval tt           γ = ∙
  eval (boom t)     γ = elim𝟘 (eval t γ)
  eval (inl t)      γ = ι₁ (eval t γ)
  eval (inr t)      γ = ι₂ (eval t γ)
  eval (case t u v) γ = elim⊎ (eval t γ)
                          (λ a → eval u (γ , a))
                          (λ b → eval v (γ , b))


  -- Correctness of evaluation with respect to conversion.

  -- FIXME: How to show this?
  postulate
    oops₁ : ∀ {{_ : Model}} {A B Γ} {t : Γ , A ⊢ B} {u : Γ ⊢ A}
            → eval ([ top ≔ u ] t) ≡ (λ γ → eval t (γ , eval u γ))
    oops₂ : ∀ {{_ : Model}} {A B Γ} {t : Γ ⊢ A ▻ B}
            → eval t ≡ (λ γ a → eval (mono⊢ (weak⊆ {A = A}) t) (γ , a) a)
    oops₃ : ∀ {{_ : Model}} {A B C Γ} {t : Γ ⊢ A} {u : Γ , A ⊢ C} {v : Γ , B ⊢ C}
            → eval ([ top ≔ t ] u) ≡ (λ γ → eval u (γ , eval t γ))
    oops₄ : ∀ {{_ : Model}} {A B C Γ} {t : Γ ⊢ B} {u : Γ , A ⊢ C} {v : Γ , B ⊢ C}
            → eval ([ top ≔ t ] v) ≡ (λ γ → eval v (γ , eval t γ))
    oops₅ : ∀ {{_ : Model}} {A B Γ} {t : Γ ⊢ A ∨ B}
            → eval t ≡ (λ γ → elim⊎ (eval t γ) (λ a → ι₁ a) (λ b → ι₂ b))

  check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒                             = refl
  check (trans⇒ p q)                      = trans (check p) (check q)
  check (sym⇒ p)                          = sym (check p)
  check (conglam⇒ {A} {B} p)              = cong (λˢ {A} {B}) (check p)
  check (congapp⇒ {A} {B} p q)            = cong₂ (_$ˢᶜ_ {A} {B}) (check p) (check q)
  check (congpair⇒ {A} {B} p q)           = cong₂ (_,ˢᶜ_ {A} {B}) (check p) (check q)
  check (congfst⇒ {A} {B} p)              = cong (π₁ˢᶜ {A} {B}) (check p)
  check (congsnd⇒ {A} {B} p)              = cong (π₂ˢᶜ {A} {B}) (check p)
  check (congboom⇒ {C} p)                 = cong (elim𝟘ˢᶜ {C}) (check p)
  check (conginl⇒ {A} {B} p)              = cong (ι₁ˢᶜ {A} {B}) (check p)
  check (conginr⇒ {A} {B} p)              = cong (ι₂ˢᶜ {A} {B}) (check p)
  check (congcase⇒ {A} {B} {C} p q r)     = cong₃ (elim⊎ˢᶜ′ {A} {B} {C})
                                                   (check p) (check q) (check r)
  check (beta▻⇒ {A} {B} {t} {u})          = sym (oops₁ {A} {B} {_} {t} {u})
  check (eta▻⇒ {A} {B} {t})               = oops₂ {A} {B} {_} {t}
  check beta∧₁⇒                           = refl
  check beta∧₂⇒                           = refl
  check eta∧⇒                             = refl
  check eta⊤⇒                            = refl
  check (beta∨₁⇒ {A} {B} {C} {t} {u} {v}) = sym (oops₃ {A} {B} {C} {_} {t} {u} {v})
  check (beta∨₂⇒ {A} {B} {C} {t} {u} {v}) = sym (oops₄ {A} {B} {C} {_} {t} {u} {v})
  check (eta∨⇒ {A} {B} {t})               = oops₅ {A} {B} {_} {t}




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSoundness where
  open CoquandDybjerSemantics (⌀ ⊢_) public


  -- Completeness with respect to a particular model.

  reify : ∀ {{_ : Model}} {A} → ⊨ A → ⌀ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} (t , f) = t
  reify {A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
  reify {⊤}    ∙       = tt
  reify {⊥}    ()
  reify {A ∨ B} (ι₁ a)  = inl (reify {A} a)
  reify {A ∨ B} (ι₂ b)  = inr (reify {B} b)

  reify⋆ : ∀ {{_ : Model}} {Π} → ⊨⋆ Π → ⌀ ⊢⋆ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)      γ = lookup i γ
  eval (lam t)      γ = multicut (reify⋆ γ) (lam t) , (λ a → eval t (γ , a))
  eval (app t u)    γ = (eval t γ) $ˢ (eval u γ)
  eval (pair t u)   γ = eval t γ , eval u γ
  eval (fst t)      γ = π₁ (eval t γ)
  eval (snd t)      γ = π₂ (eval t γ)
  eval tt           γ = ∙
  eval (boom t)     γ = elim𝟘 (eval t γ)
  eval (inl t)      γ = ι₁ (eval t γ)
  eval (inr t)      γ = ι₂ (eval t γ)
  eval (case t u v) γ = elim⊎ (eval t γ) (λ a → eval u (γ , a)) (λ b → eval v (γ , b))


  -- TODO: Correctness of evaluation with respect to conversion.
