module Selinger92Plus where

open import Selinger92


----------------------------------------------------------------------------------------------------

{-
subst : ∀ {𝓍 𝓎} {X : Set 𝓍} (Y : X → Set 𝓎) {x x′} → x ≡ x′ → Y x → Y x′
subst Y refl x = x

coe : ∀ {𝓍} {X X′ : Set 𝓍} → X ≡ X′ → X → X′
coe = subst id

hmm1 : ∀ {k} {Γ Γ′ : Fm§ k} → (Γ ⊑ Γ′) ≡ (renFm§ id≤ Γ ⊑ renFm§ id≤ Γ′)
hmm1 {Γ = Γ} {Γ′} = _⊑_ & lidrenFm§ Γ ⁻¹ ⊗ lidrenFm§ Γ′ ⁻¹

lidtren⊑ : ∀ {k} {Γ Γ′ : Fm§ k} (η : Γ ⊑ Γ′) → tren⊑ id≤ η ≡ coe hmm1 η
lidtren⊑ stop      = refl
lidtren⊑ (wk⊑ η)   =
    begin
      wk⊑ (tren⊑ id≤ η)
    ≡⟨ wk⊑ & lidtren⊑ η ⟩
      wk⊑ (coe hmm1 η)
    ≡⟨ {!!} ⟩
      coe hmm1 (wk⊑ η)
    ∎
lidtren⊑ (lift⊑ η) = {!!}

bicast⊑ : ∀ {k} {Γ Γ′ Δ Δ′ : Fm§ k} → Γ ≡ Δ → Γ′ ≡ Δ′ → Γ ⊑ Γ′ → Δ ⊑ Δ′
bicast⊑ refl refl η = η

wkbicast⊑ : ∀ {k} {Γ Γ′ Δ Δ′ : Fm§ k} {C C′} (p₁ : Γ ≡ Δ) (p₂ : Γ′ ≡ Δ′) (q : C ≡ C′) (η : Γ ⊑ Γ′) →
              (wk⊑ ∘ bicast⊑ p₁ p₂) η ≡ (bicast⊑ p₁ ((_,_ & p₂ ⊗ q)) ∘ wk⊑) η
wkbicast⊑ refl refl refl η = refl
-}


----------------------------------------------------------------------------------------------------

bicast⊑ : ∀ {k} {Γ Γ^ Γ′ Γ′^ : Fm§ k} → Γ^ ≡ Γ → Γ′^ ≡ Γ′ → Γ ⊑ Γ′ → Γ^ ⊑ Γ′^
bicast⊑ refl refl η = η

wkbicast⊑ : ∀ {k} {Γ Γ^ Γ′ Γ′^ : Fm§ k} {C C^} (p₁ : Γ^ ≡ Γ) (p₂ : Γ′^ ≡ Γ′) (q : C^ ≡ C) (η : Γ ⊑ Γ′) →
              (wk⊑ ∘ bicast⊑ p₁ p₂) η ≡ (bicast⊑ p₁ ((_,_ & p₂ ⊗ q)) ∘ wk⊑) η
wkbicast⊑ refl refl refl η = refl

liftbicast⊑ : ∀ {k} {Γ Γ^ Γ′ Γ′^ : Fm§ k} {C C^} (p₁ : Γ^ ≡ Γ) (p₂ : Γ′^ ≡ Γ′) (q : C^ ≡ C) (η : Γ ⊑ Γ′) →
                (lift⊑ ∘ bicast⊑ p₁ p₂) η ≡ (bicast⊑ (_,_ & p₁ ⊗ q) (_,_ & p₂ ⊗ q) ∘ lift⊑) η
liftbicast⊑ refl refl refl η = refl

lidtren⊑ : ∀ {k} {Γ Γ′ : Fm§ k} (η : Γ ⊑ Γ′) →
             tren⊑ id≤ η ≡ bicast⊑ (lidrenFm§ Γ) (lidrenFm§ Γ′) η
lidtren⊑ stop      = refl
lidtren⊑ (wk⊑ η)   = wk⊑ & lidtren⊑ η
                   ⋮ wkbicast⊑ (lidrenFm§ _) (lidrenFm§ _) (lidrenFm _) η

lidtren⊑ (lift⊑ η) = lift⊑ & lidtren⊑ η
                   ⋮ liftbicast⊑ (lidrenFm§ _) (lidrenFm§ _) (lidrenFm _) η

lcomptren⊑ : ∀ {k k′ k″} {Γ Γ′ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (ζ : Γ ⊑ Γ′) →
               tren⊑ (η′ ∘≤ η) ζ ≡ bicast⊑ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Γ′) ((tren⊑ η′ ∘ tren⊑ η) ζ)
lcomptren⊑ η′ η stop      = refl
lcomptren⊑ η′ η (wk⊑ ζ)   = wk⊑ & lcomptren⊑ η′ η ζ
                          ⋮ wkbicast⊑ (comprenFm§ η′ η _) (comprenFm§ η′ η _) (comprenFm η′ η _) ((tren⊑ η′ ∘ tren⊑ η) ζ)
lcomptren⊑ η′ η (lift⊑ ζ) = lift⊑ & lcomptren⊑ η′ η ζ
                          ⋮ liftbicast⊑ (comprenFm§ η′ η _) (comprenFm§ η′ η _) (comprenFm η′ η _) ((tren⊑ η′ ∘ tren⊑ η) ζ)


----------------------------------------------------------------------------------------------------

bicast∋ : ∀ {k} {Γ Γ^ : Fm§ k} {A A^} → Γ^ ≡ Γ → A^ ≡ A → Γ ∋ A → Γ^ ∋ A^
bicast∋ refl refl i = i

zerobicast∋ : ∀ {k} {Γ Γ^ : Fm§ k} {C C^} (p : Γ^ ≡ Γ) (q : C^ ≡ C) →
                zero ≡ bicast∋ (_,_ & p ⊗ q) q zero
zerobicast∋ refl refl = refl

sucbicast∋ : ∀ {k} {Γ Γ^ : Fm§ k} {A A^ C C^} (p : Γ^ ≡ Γ) (q₁ : C^ ≡ C) (q₂ : A^ ≡ A) (i : Γ ∋ A) →
               (suc ∘ bicast∋ p q₂) i ≡ (bicast∋ (_,_ & p ⊗ q₁) q₂ ∘ suc) i
sucbicast∋ refl refl refl zero    = refl
sucbicast∋ refl refl refl (suc i) = suc & sucbicast∋ refl refl refl i

lidtren∋ : ∀ {k} {Γ : Fm§ k} {A} (i : Γ ∋ A) → tren∋ id≤ i ≡ bicast∋ (lidrenFm§ Γ) (lidrenFm A) i
lidtren∋ zero    = zerobicast∋ (lidrenFm§ _) (lidrenFm _)
lidtren∋ (suc i) = suc & lidtren∋ i
                 ⋮ sucbicast∋ (lidrenFm§ _) (lidrenFm _) (lidrenFm _) i

comptren∋ : ∀ {k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Γ ∋ A) →
              tren∋ (η′ ∘≤ η) i ≡
                bicast∋ (comprenFm§ η′ η Γ) (comprenFm η′ η A) ((tren∋ η′ ∘ tren∋ η) i)
comptren∋ η′ η zero    = zerobicast∋ (comprenFm§ η′ η _) (comprenFm η′ η _)
comptren∋ η′ η (suc i) = suc & comptren∋ η′ η i
                       ⋮ sucbicast∋ (comprenFm§ η′ η _) (comprenFm η′ η _) (comprenFm η′ η _) ((tren∋ η′ ∘ tren∋ η) i)


----------------------------------------------------------------------------------------------------

bicast : ∀ {Þ k} {Γ Γ^ : Fm§ k} {A A^} → Γ^ ≡ Γ → A^ ≡ A → Þ / Γ ⊢ A → Þ / Γ^ ⊢ A^
bicast refl refl d = d

-- lidtren : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → tren id≤ d ≡ bicast (lidrenFm§ Γ) (lidrenFm A) d
-- lidtren (‵var i)                = {!!}
-- lidtren (‵lam d)                = {!!}
-- lidtren (d ‵$ e)                = {!!}
-- lidtren (‵pair d e)             = {!!}
-- lidtren (‵fst d)                = {!!}
-- lidtren (‵snd d)                = {!!}
-- lidtren (‵left d)               = {!!}
-- lidtren (‵right d)              = {!!}
-- lidtren (‵either c d e)         = {!!}
-- lidtren (‵all refl d)           = {!!}
-- lidtren (‵unall t refl d)       = {!!}
-- lidtren (‵ex t refl d)          = {!!}
-- lidtren (‵letex refl refl d e)  = {!!}
-- lidtren (‵abort d)              = {!!}
-- lidtren (‵magic d)              = {!!}
-- lidtren ‵refl                   = {!!}
-- lidtren (‵sym d)                = {!!}
-- lidtren (‵trans d e)            = {!!}
-- lidtren (‵cong f i refl refl d) = {!!}
-- lidtren ‵dis                    = {!!}
-- lidtren (‵inj d)                = {!!}
-- lidtren (‵ind refl refl d e)    = {!!}
-- lidtren (‵proj i refl)          = {!!}
-- lidtren (‵comp g φ refl)        = {!!}
-- lidtren (‵rec f g)              = {!!}
--

postulate
  comptren : ∀ {Þ k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (d : Þ / Γ ⊢ A) →
               tren (η′ ∘≤ η) d ≡ bicast (comprenFm§ η′ η Γ) (comprenFm η′ η A) ((tren η′ ∘ tren η) d)
-- comptren η′ η (‵var i)                = {!!}
-- comptren η′ η (‵lam d)                = {!!}
-- comptren η′ η (d ‵$ e)                = {!!}
-- comptren η′ η (‵pair d e)             = {!!}
-- comptren η′ η (‵fst d)                = {!!}
-- comptren η′ η (‵snd d)                = {!!}
-- comptren η′ η (‵left d)               = {!!}
-- comptren η′ η (‵right d)              = {!!}
-- comptren η′ η (‵either c d e)         = {!!}
-- comptren η′ η (‵all refl d)           = {!!}
-- comptren η′ η (‵unall t refl d)       = {!!}
-- comptren η′ η (‵ex t refl d)          = {!!}
-- comptren η′ η (‵letex refl refl d e)  = {!!}
-- comptren η′ η (‵abort d)              = {!!}
-- comptren η′ η (‵magic d)              = {!!}
-- comptren η′ η ‵refl                   = {!!}
-- comptren η′ η (‵sym d)                = {!!}
-- comptren η′ η (‵trans d e)            = {!!}
-- comptren η′ η (‵cong f i refl refl d) = {!!}
-- comptren η′ η ‵dis                    = {!!}
-- comptren η′ η (‵inj d)                = {!!}
-- comptren η′ η (‵ind refl refl d e)    = {!!}
-- comptren η′ η (‵proj i refl)          = {!!}
-- comptren η′ η (‵comp g φ refl)        = {!!}
-- comptren η′ η (‵rec f g)              = {!!}


----------------------------------------------------------------------------------------------------

bicast§ : ∀ {Þ k} {Γ Γ^ : Fm§ k} {Δ Δ^} → Γ^ ≡ Γ → Δ^ ≡ Δ → Þ / Γ ⊢§ Δ → Þ / Γ^ ⊢§ Δ^
bicast§ refl refl δ = δ

nilbicast§ : ∀ {Þ k} {Γ Γ^ : Fm§ k} (p : Γ^ ≡ Γ) → ∙ ≡ bicast§ {Þ} p refl ∙
nilbicast§ refl = refl

consbicast§ : ∀ {Þ k} {Γ Γ^ Δ Δ^ : Fm§ k} {A A^} (p₁ : Γ^ ≡ Γ) (p₂ : Δ^ ≡ Δ) (q : A^ ≡ A) (δ : Þ / Γ ⊢§ Δ) (d : Þ / Γ ⊢ A) →
                (bicast§ p₁ p₂ δ , bicast p₁ q d) ≡ (bicast§ p₁ (_,_ & p₂ ⊗ q) (δ , d))
consbicast§ refl refl refl δ d = refl

comptren§ : ∀ {Þ k k′ k″} {Γ Δ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
              tren§ (η′ ∘≤ η) δ ≡ bicast§ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Δ) ((tren§ η′ ∘ tren§ η) δ)
comptren§ η′ η ∙       = nilbicast§ (comprenFm§ η′ η _)
comptren§ η′ η (δ , d) = _,_ & comptren§ η′ η δ ⊗ comptren η′ η d
                       ⋮ consbicast§ (comprenFm§ η′ η _) (comprenFm§ η′ η _) (comprenFm η′ η _) ((tren§ η′ ∘ tren§ η) δ) ((tren η′ ∘ tren η) d)


----------------------------------------------------------------------------------------------------

hcomptren§′ : ∀ {Þ k k′ k″} {Γ Δ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
                tren§ (η′ ∘≤ η) δ ≅ (tren§ η′ ∘ tren§ η) δ
hcomptren§′ {Γ = Γ} {Δ} η′ η δ =
    begin
      tren§ (η′ ∘≤ η) δ
    ≡⟨ comptren§ η′ η δ ⟩
      bicast§ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Δ) ((tren§ η′ ∘ tren§ η) δ)
    ≅⟨ {!!} ⟩
      (tren§ η′ ∘ tren§ η) δ
    ∎
  where
    open ≅-Reasoning


----------------------------------------------------------------------------------------------------
