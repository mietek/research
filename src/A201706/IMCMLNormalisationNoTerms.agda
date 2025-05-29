{-# OPTIONS --rewriting #-}

module A201706.IMCMLNormalisationNoTerms where

open import A201706.IMCMLSemanticsNoTerms public


-- TODO
postulate
  ● : ∀ {ℓ} {X : Set ℓ} → X


-- Absolute values.

infix 3 _⊨_
_⊨_ : Cx → Ty → Set₁
Δ ⁏ Γ ⊨ A = ∀ {{_ : Model}} {w : World} →
               (∀ {w′ : World} → w′ Я w → w′ ⟪⊢⟫⋆ ⌈ Δ ⌉) →
               (∀ {w′ : World} → w′ Я w → w′ ⟪⊩⟫⋆ ⌈ Δ ⌉) →
               w ⊩⋆ Γ →
               w ⊩ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx → Ty⋆ → Set₁
Δ ⁏ Γ ⊨⋆ Ξ = ∀ {{_ : Model}} {w : World} →
                (∀ {w′ : World} → w′ Я w → w′ ⟪⊢⟫⋆ ⌈ Δ ⌉) →
                (∀ {w′ : World} → w′ Я w → w′ ⟪⊩⟫⋆ ⌈ Δ ⌉) →
                w ⊩⋆ Γ →
                w ⊩⋆ Ξ


-- Soundness.

mutual
  ⟦_⟧ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊨ A
  ⟦ var 𝒾 ⟧                       δ₁ δ₂ γ = lookup⊩ γ 𝒾
  ⟦ mvar 𝒾 ⟧                      δ₁ δ₂ γ = mlookup⟪⊩⟫ (δ₂ reflЯ) (∋→⌈∋⌉ 𝒾) reflЯ ∅
  ⟦ lam {A = A} {B} 𝒟 ⟧           δ₁ δ₂ γ = return {A ⇒ B}
                                              λ θ a →
                                                ⟦ 𝒟 ⟧ (λ ζ → δ₁ (transЯ ζ (⊒→Я θ)))
                                                      (λ ζ → δ₂ (transЯ ζ (⊒→Я θ)))
                                                      (mono⊩⋆ θ γ , a)
  ⟦ app {A = A} {B} 𝒟 ℰ ⟧         δ₁ δ₂ γ = bind {A ⇒ B} {B} (⟦ 𝒟 ⟧ δ₁ δ₂ γ)
                                              λ θ f →
                                                f refl⊒ (mono⊩ {A} θ (⟦ ℰ ⟧ δ₁ δ₂ γ))
  ⟦ box {Φ = Φ} {A} 𝒟 ⟧           δ₁ δ₂ γ = return {[ Φ ] A}
                                              λ ζ →
                                                mgraft⊢ (concat⟨⊢⟩⋆ {Φ} (δ₁ ζ) mrefl⟨⊢⟩⋆) 𝒟 ,
                                                λ ζ′ φ →
                                                  ●
  ⟦ unbox {Φ = Φ} {A} {C} φ 𝒟 ℰ ⟧ δ₁ δ₂ γ = bind {[ Φ ] A} {C} (⟦ 𝒟 ⟧ δ₁ δ₂ γ)
                                              λ θ q →
                                                ⟦ ℰ ⟧ (λ ζ → δ₁ (transЯ ζ (⊒→Я θ)) , ●)
                                                      (λ ζ → δ₂ (transЯ ζ (⊒→Я θ)) , ●)
                                                      (mono⊩⋆ θ γ)

  ⟦_⟧⋆ : ∀ {Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ → Δ ⁏ Γ ⊨⋆ Ξ
  ⟦ ∅ ⟧⋆     δ₁ δ₂ γ = ∅
  ⟦ ξ , 𝒟 ⟧⋆ δ₁ δ₂ γ = ⟦ ξ ⟧⋆ δ₁ δ₂ γ , ⟦ 𝒟 ⟧ δ₁ δ₂ γ


-- Canonical model.

instance
  canon : Model
  canon = record
    { World  = Cx
    ; _⊒_    = λ { (Δ′ ⁏ Γ′) (Δ ⁏ Γ) → Δ′ ⊇ Δ ∧ Γ′ ⊇ Γ }
    ; refl⊒  = refl⊇ , refl⊇
    ; trans⊒ = λ { (ζ′ , η′) (ζ , η) → trans⊇ ζ′ ζ , trans⊇ η′ η }
    ; _Я_    = λ { (Δ′ ⁏ Γ′) (Δ ⁏ Γ) → Δ′ ⊇ Δ }
    ; reflЯ  = refl⊇
    ; transЯ = trans⊇
    ; G      = _⊢ⁿᵉ •
    ; monoG  = λ { (ζ , η) 𝒟 → mono⊢ⁿᵉ ζ η 𝒟 }
    ; ⊒→Я   = π₁
    ; peek   = id
    }

mutual
  reifyᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊩ A → Δ ⁏ Γ ⊢ⁿᶠ A
  reifyᶜ {•}       κ = κ (refl⊇ , refl⊇)
                         λ θ a →
                           neⁿᶠ a
  reifyᶜ {A ⇒ B}  κ = κ (refl⊇ , refl⊇)
                         λ θ f →
                           lamⁿᶠ (reifyᶜ (f (refl⊇ , weak refl⊇) ⟦ varⁿᵉ zero ⟧ᶜ))
  reifyᶜ {[ Ψ ] A} κ = κ (refl⊇ , refl⊇)
                         λ {w″} θ q →
                           boxⁿᶠ (π₁ (q {w′ = w″} refl⊇))

  ⟨reify⟩ᶜ : ∀ {Γ Φ Δ A} → Δ ⁏ Γ ⟪⊩⟫ [ Φ ] A → Δ ⟨⊢⟩ⁿᶠ [ Φ ] A
  ⟨reify⟩ᶜ {Γ} {Φ} a = reifyᶜ (a (weak⊇⧺₂ Φ) (mono⟨⊢⟩⋆ (weak⊇⧺₁ Φ) mrefl⟨⊢⟩⋆))

  ⟨reify⟩⋆ᶜ : ∀ {Γ Ξ Δ} → Δ ⁏ Γ ⟪⊩⟫⋆ Ξ → Δ ⟨⊢⟩⋆ⁿᶠ Ξ
  ⟨reify⟩⋆ᶜ {Γ} {∅}           ∅       = ∅
  ⟨reify⟩⋆ᶜ {Γ} {Ξ , [ Φ ] A} (ξ , a) = ⟨reify⟩⋆ᶜ {Γ} ξ , ⟨reify⟩ᶜ {Γ} {Φ} a

  ⟦_⟧ᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ⁿᵉ A → Δ ⁏ Γ ⊩ A
  ⟦_⟧ᶜ {•}       𝒟 = return {•} 𝒟
  ⟦_⟧ᶜ {A ⇒ B}  𝒟 = return {A ⇒ B}
                       λ { (ζ , η) a →
                         ⟦ appⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟) (reifyᶜ a) ⟧ᶜ }
  ⟦_⟧ᶜ {[ Ψ ] A} 𝒟 = λ { (ζ , η) κ →
                       neⁿᶠ (unboxⁿᵉ ●
                                     (mono⊢ⁿᵉ ζ η 𝒟)
                                     (κ (weak refl⊇ , refl⊇)
                                        λ ζ′ →
                                          ● ,
                                          ●)) }


-- TODO: Needs a name.

refl⊩⋆ : ∀ {Γ Δ : Ty⋆} → Δ ⁏ Γ ⊩⋆ Γ
refl⊩⋆ {∅}     = ∅
refl⊩⋆ {Γ , A} = mono⊩⋆ (refl⊇ , weak refl⊇) refl⊩⋆ , ⟦ varⁿᵉ zero ⟧ᶜ

mrefl⟪⊩⟫⋆ : ∀ {Γ Δ : Ty⋆} → Δ ⁏ Γ ⟪⊩⟫⋆ ⌈ Δ ⌉
mrefl⟪⊩⟫⋆ {Γ} {∅}     = ∅
mrefl⟪⊩⟫⋆ {Γ} {Δ , A} = mono⟪⊩⟫⋆ {w = _ ⁏ Γ} (weak refl⊇ , refl⊇) (mrefl⟪⊩⟫⋆ {Γ}) ,
                           λ ζ φ →
                             ⟦ mvarⁿᵉ (mono∋ ζ zero) ⟧ᶜ


-- Completeness.

reify : ∀ {Γ Δ A} → Δ ⁏ Γ ⊨ A → Δ ⁏ Γ ⊢ⁿᶠ A
reify {Γ} 𝔞 = reifyᶜ (𝔞 (λ ζ → mono⟨⊢⟩⋆ ζ mrefl⟨⊢⟩⋆)
                     (λ ζ → mono⟪⊩⟫⋆ {w = _ ⁏ Γ} (ζ , refl⊇) (mrefl⟪⊩⟫⋆ {Γ}))
                     refl⊩⋆)


-- Normalisation.

nbe : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ⁿᶠ A
nbe = reify ∘ ⟦_⟧
