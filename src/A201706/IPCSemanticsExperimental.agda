module A201706.IPCSemanticsExperimental where

open import A201706.IPC public


-- Intuitionistic Kripke models.

record Model : Set₁ where
  field
    World       : Set
    _⊒_         : World → World → Set
    refl⊒       : ∀ {w} → w ⊒ w
    trans⊒      : ∀ {w w′ w″} → w″ ⊒ w′ → w′ ⊒ w → w″ ⊒ w
    idtrans⊒₁   : ∀ {w w′} → (η : w′ ⊒ w) → trans⊒ refl⊒ η ≡ η
    idtrans⊒₂   : ∀ {w w′} → (η : w′ ⊒ w) → trans⊒ η refl⊒ ≡ η
    assoctrans⊒ : ∀ {w w′ w″ w‴} → (η″ : w‴ ⊒ w″) (η′ : w″ ⊒ w′) (η : w′ ⊒ w) →
                    trans⊒ η″ (trans⊒ η′ η) ≡ trans⊒ (trans⊒ η″ η′) η
    G           : World → Set
    monoG       : ∀ {w w′} → w′ ⊒ w → G w → G w′
    idmonoG     : ∀ {w} → (a : G w) → monoG refl⊒ a ≡ a
    assocmonoG  : ∀ {w w′ w″} → (η′ : w″ ⊒ w′) (η : w′ ⊒ w) (a : G w) →
                    monoG η′ (monoG η a) ≡ monoG (trans⊒ η′ η) a
open Model {{…}} public


-- Values.

infix 3 _⊩_
_⊩_ : ∀ {{_ : Model}} → World → Ty → Set
w ⊩ •      = G w
w ⊩ A ⇒ B = ∀ {w′ : World} → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B

mono⊩ : ∀ {{_ : Model}} {A} {w w′ : World} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
mono⊩ {•}      η a = monoG η a
mono⊩ {A ⇒ B} η f = λ η′ a → f (trans⊒ η′ η) a

idmono⊩ : ∀ {{_ : Model}} {A} {w : World} → (a : w ⊩ A) → mono⊩ {A} refl⊒ a ≡ a
idmono⊩ {•}      a = idmonoG a
idmono⊩ {A ⇒ B} a = fex′ (fex (λ η → cong a (idtrans⊒₂ η)))

assocmono⊩ : ∀ {{_ : Model}} {A} {w w′ w″ : World} → (η′ : w″ ⊒ w′) (η : w′ ⊒ w) (a : w ⊩ A) →
                mono⊩ {A} η′ (mono⊩ {A} η a) ≡ mono⊩ {A} (trans⊒ η′ η) a
assocmono⊩ {•}      η′ η a = assocmonoG η′ η a
assocmono⊩ {A ⇒ B} η′ η a = fex′ (fex (λ η″ → cong a (sym (assoctrans⊒ η″ η′ η))))


-- Lists of values.

module IPCSemanticsExperimentalList where
  open IPCList public

  infix 3 _⊩⋆_
  _⊩⋆_ : ∀ {{_ : Model}} → World → Ty⋆ → Set
  w ⊩⋆ Ξ = All (w ⊩_) Ξ

  mono⊩⋆ : ∀ {{_ : Model}} {w w′ : World} {Ξ} → w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ η ξ = mapAll (λ {A} → mono⊩ {A} η) ξ

  idmono⊩⋆ : ∀ {{_ : Model}} {w : World} {Ξ} → (ξ : w ⊩⋆ Ξ) → mono⊩⋆ refl⊒ ξ ≡ ξ
  idmono⊩⋆ {Ξ = ∅}     ∅       = refl
  idmono⊩⋆ {Ξ = Ξ , A} (ξ , a) = cong² _,_ (idmono⊩⋆ ξ) (idmono⊩ {A} a)

  assocmono⊩⋆ : ∀ {{_ : Model}} {w w′ w″ : World} {Ξ} → (η′ : w″ ⊒ w′) (η : w′ ⊒ w) (ξ : w ⊩⋆ Ξ) →
                   mono⊩⋆ η′ (mono⊩⋆ η ξ) ≡ mono⊩⋆ (trans⊒ η′ η) ξ
  assocmono⊩⋆ {Ξ = ∅}     η′ η ∅       = refl
  assocmono⊩⋆ {Ξ = Ξ , A} η′ η (ξ , a) = cong² _,_ (assocmono⊩⋆ η′ η ξ) (assocmono⊩ {A} η′ η a)

  lookup⊩ : ∀ {{_ : Model}} {w : World} {Ξ A} → w ⊩⋆ Ξ → Ξ ∋ A → w ⊩ A
  lookup⊩ ξ 𝒾 = lookupAll ξ 𝒾


-- Vectors of values.

module IPCSemanticsExperimentalVec where
  open IPCVec public

  infix 3 _⊩⋆_
  _⊩⋆_ : ∀ {{_ : Model}} {n} → World → Ty⋆ n → Set
  w ⊩⋆ Ξ = All (w ⊩_) Ξ

  mono⊩⋆ : ∀ {{_ : Model}} {w w′ : World} {n} {Ξ : Ty⋆ n} →
              w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ η ξ = mapAll (λ {A} → mono⊩ {A} η) ξ

  idmono⊩⋆ : ∀ {{_ : Model}} {w : World} {n} {Ξ : Ty⋆ n} →
                (ξ : w ⊩⋆ Ξ) → mono⊩⋆ refl⊒ ξ ≡ ξ
  idmono⊩⋆ {Ξ = ∅}     ∅       = refl
  idmono⊩⋆ {Ξ = Ξ , A} (ξ , a) = cong² _,_ (idmono⊩⋆ ξ) (idmono⊩ {A} a)

  assocmono⊩⋆ : ∀ {{_ : Model}} {w w′ w″ : World} {n} {Ξ : Ty⋆ n} →
                   (η′ : w″ ⊒ w′) (η : w′ ⊒ w) (ξ : w ⊩⋆ Ξ) →
                   mono⊩⋆ η′ (mono⊩⋆ η ξ) ≡ mono⊩⋆ (trans⊒ η′ η) ξ
  assocmono⊩⋆ {Ξ = ∅}     η′ η ∅       = refl
  assocmono⊩⋆ {Ξ = Ξ , A} η′ η (ξ , a) = cong² _,_ (assocmono⊩⋆ η′ η ξ) (assocmono⊩ {A} η′ η a)

  lookup⊩ : ∀ {{_ : Model}} {w : World} {n} {Ξ : Ty⋆ n} {A i} →
               w ⊩⋆ Ξ → Ξ ∋⟨ i ⟩ A → w ⊩ A
  lookup⊩ ξ 𝒾 = lookupAll ξ 𝒾
