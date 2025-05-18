module Selinger92Plus where

open import Selinger92
open ≡-Reasoning


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

bicast⊑ : ∀ {k} {Γ Γ′ Γ^ Γ′^ : Fm§ k} → Γ^ ≡ Γ → Γ′^ ≡ Γ′ → Γ ⊑ Γ′ → Γ^ ⊑ Γ′^
bicast⊑ refl refl η = η

wkbicast⊑ : ∀ {k} {Γ Γ′ Γ^ Γ′^ : Fm§ k} {C C^} (p₁ : Γ^ ≡ Γ) (p₂ : Γ′^ ≡ Γ′) (q : C^ ≡ C) (η : Γ ⊑ Γ′) →
              (wk⊑ ∘ bicast⊑ p₁ p₂) η ≡ (bicast⊑ p₁ ((_,_ & p₂ ⊗ q)) ∘ wk⊑) η
wkbicast⊑ refl refl refl η = refl

liftbicast⊑ : ∀ {k} {Γ Γ′ Γ^ Γ′^ : Fm§ k} {C C^} (p₁ : Γ^ ≡ Γ) (p₂ : Γ′^ ≡ Γ′) (q : C^ ≡ C) (η : Γ ⊑ Γ′) →
                (lift⊑ ∘ bicast⊑ p₁ p₂) η ≡ (bicast⊑ (_,_ & p₁ ⊗ q) (_,_ & p₂ ⊗ q) ∘ lift⊑) η
liftbicast⊑ refl refl refl η = refl

lidtren⊑ : ∀ {k} {Γ Γ′ : Fm§ k} (η : Γ ⊑ Γ′) →
             tren⊑ id≤ η ≡ bicast⊑ (lidrenFm§ Γ) (lidrenFm§ Γ′) η
lidtren⊑                           stop      = refl
lidtren⊑ {Γ = Γ}     {Γ′ = Γ′ , C} (wk⊑ η)   =
    begin
      wk⊑ (tren⊑ id≤ η)
    ≡⟨ wk⊑ & lidtren⊑ η ⟩
      (wk⊑ ∘ bicast⊑ (lidrenFm§ Γ) (lidrenFm§ Γ′)) η
    ≡⟨ wkbicast⊑ (lidrenFm§ Γ) (lidrenFm§ Γ′) (lidrenFm C) η ⟩
      (bicast⊑ (lidrenFm§ Γ) (_,_ & lidrenFm§ Γ′ ⊗ lidrenFm C) ∘ wk⊑) η
    ∎
lidtren⊑ {Γ = Γ , C} {Γ′ = Γ′ , C} (lift⊑ η) =
    begin
      lift⊑ (tren⊑ id≤ η)
    ≡⟨ lift⊑ & lidtren⊑ η ⟩
      (lift⊑ ∘ bicast⊑ (lidrenFm§ Γ) (lidrenFm§ Γ′)) η
    ≡⟨ liftbicast⊑ (lidrenFm§ Γ) (lidrenFm§ Γ′) (lidrenFm C) η ⟩
      (bicast⊑ (_,_ & lidrenFm§ Γ ⊗ lidrenFm C) (_,_ & lidrenFm§ Γ′ ⊗ lidrenFm C) ∘ lift⊑) η
    ∎

lcomptren⊑ : ∀ {k k′ k″} {Γ Γ′ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (ζ : Γ ⊑ Γ′) →
               tren⊑ (η′ ∘≤ η) ζ ≡ bicast⊑ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Γ′) ((tren⊑ η′ ∘ tren⊑ η) ζ)
lcomptren⊑                           η′ η stop      = refl
lcomptren⊑ {Γ = Γ}     {Γ′ = Γ′ , C} η′ η (wk⊑ ζ)   =
    begin
      wk⊑ (tren⊑ (η′ ∘≤ η) ζ)
    ≡⟨ wk⊑ & lcomptren⊑ η′ η ζ ⟩
      (wk⊑ ∘ bicast⊑ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Γ′)) ((tren⊑ η′ ∘ tren⊑ η) ζ)
    ≡⟨ wkbicast⊑ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Γ′) (comprenFm η′ η C) ((tren⊑ η′ ∘ tren⊑ η) ζ) ⟩
      (bicast⊑ (comprenFm§ η′ η Γ) (_,_ & comprenFm§ η′ η Γ′ ⊗ comprenFm η′ η C) ∘ wk⊑) (tren⊑ η′ (tren⊑ η ζ))
    ∎
lcomptren⊑ {Γ = Γ , C} {Γ′ = Γ′ , C} η′ η (lift⊑ ζ) =
    begin
      lift⊑ (tren⊑ (η′ ∘≤ η) ζ)
    ≡⟨ lift⊑ & lcomptren⊑ η′ η ζ ⟩
      (lift⊑ ∘ bicast⊑ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Γ′)) ((tren⊑ η′ ∘ tren⊑ η) ζ)
    ≡⟨ liftbicast⊑ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Γ′) (comprenFm η′ η C) (tren⊑ η′ (tren⊑ η ζ)) ⟩
      bicast⊑ (_,_ & comprenFm§ η′ η Γ ⊗ comprenFm η′ η C) (_,_ & comprenFm§ η′ η Γ′ ⊗ comprenFm η′ η C) ((tren⊑ η′ ∘ tren⊑ η) (lift⊑ ζ))
    ∎


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
lidtren∋ {Γ = Γ , A} {A} zero    =
    begin
      zero
    ≡⟨ zerobicast∋ (lidrenFm§ Γ) (lidrenFm A) ⟩
      bicast∋ (_,_ & lidrenFm§ Γ ⊗ lidrenFm A) (lidrenFm A) zero
    ∎
lidtren∋ {Γ = Γ , C} {A} (suc i) =
    begin
      suc (tren∋ id≤ i)
    ≡⟨ suc & lidtren∋ i ⟩
      (suc ∘ bicast∋ (lidrenFm§ Γ) (lidrenFm A)) i
    ≡⟨ sucbicast∋ (lidrenFm§ Γ) (lidrenFm C) (lidrenFm A) i ⟩
      (bicast∋ (_,_ & lidrenFm§ Γ ⊗ lidrenFm C) (lidrenFm A) ∘ suc) i
    ∎

comptren∋ : ∀ {k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Γ ∋ A) →
              tren∋ (η′ ∘≤ η) i ≡
                bicast∋ (comprenFm§ η′ η Γ) (comprenFm η′ η A) ((tren∋ η′ ∘ tren∋ η) i)
comptren∋ {Γ = Γ , A} {A} η′ η zero =
    begin
      zero
    ≡⟨ zerobicast∋ (comprenFm§ η′ η Γ) (comprenFm η′ η A) ⟩
      bicast∋ (_,_ & comprenFm§ η′ η Γ ⊗ comprenFm η′ η A) (comprenFm η′ η A) ((tren∋ η′ ∘ tren∋ η) zero)
    ∎
comptren∋ {Γ = Γ , C} {A} η′ η (suc i) =
    begin
      suc (tren∋ (η′ ∘≤ η) i)
    ≡⟨ suc & comptren∋ η′ η i ⟩
      suc (bicast∋ (comprenFm§ η′ η Γ) (comprenFm η′ η A) ((tren∋ η′ ∘ tren∋ η) i))
    ≡⟨ sucbicast∋ (comprenFm§ η′ η Γ) (comprenFm η′ η C) (comprenFm η′ η A) (tren∋ η′ (tren∋ η i)) ⟩
      bicast∋ (_,_ & comprenFm§ η′ η Γ ⊗ comprenFm η′ η C) (comprenFm η′ η A) ((tren∋ η′ ∘ tren∋ η) (suc i))
    ∎


----------------------------------------------------------------------------------------------------

bicast : ∀ {Þ k} {Γ Γ^ : Fm§ k} {A A^} → Γ^ ≡ Γ → A^ ≡ A → Þ / Γ ⊢ A → Þ / Γ^ ⊢ A^
bicast refl refl d = d

lidtren : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → tren id≤ d ≡ bicast (lidrenFm§ Γ) (lidrenFm A) d
lidtren d = {!!}

comptren : ∀ {Þ k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (d : Þ / Γ ⊢ A) →
             tren (η′ ∘≤ η) d ≡ bicast (comprenFm§ η′ η Γ) (comprenFm η′ η A) ((tren η′ ∘ tren η) d)
comptren η′ η d = {!!}


----------------------------------------------------------------------------------------------------

bicast§ : ∀ {Þ k} {Γ Γ^ : Fm§ k} {Δ Δ^} → Γ^ ≡ Γ → Δ^ ≡ Δ → Þ / Γ ⊢§ Δ → Þ / Γ^ ⊢§ Δ^
bicast§ refl refl δ = δ

comptren§ : ∀ {Þ k k′ k″} {Γ Δ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
              tren§ (η′ ∘≤ η) δ ≡ bicast§ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Δ) ((tren§ η′ ∘ tren§ η) δ)
comptren§ η′ η δ = {!!}


----------------------------------------------------------------------------------------------------
