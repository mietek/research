module IPCSyntaxNoTerms where

open import IPC public
open IPCList public


-- Contexts.

Cx : Set
Cx = Ty⋆


-- Derivations.

infix 3 _⊢_
data _⊢_ : Cx → Ty → Set where
  var : ∀ {Γ A} →
          Γ ∋ A →
          Γ ⊢ A
  lam : ∀ {Γ A B} →
          Γ , A ⊢ B →
          Γ ⊢ A ⇒ B
  app : ∀ {Γ A B} →
          Γ ⊢ A ⇒ B → Γ ⊢ A →
          Γ ⊢ B

infix 3 _⊢⋆_
_⊢⋆_ : Cx → Ty⋆ → Set
Γ ⊢⋆ Ξ = All (Γ ⊢_) Ξ

mono⊢ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (var 𝒾)   = var (mono∋ η 𝒾)
mono⊢ η (lam 𝒟)   = lam (mono⊢ (lift η) 𝒟)
mono⊢ η (app 𝒟 ℰ) = app (mono⊢ η 𝒟) (mono⊢ η ℰ)

mono⊢⋆ : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ Ξ → Γ′ ⊢⋆ Ξ
mono⊢⋆ η ξ = mapAll (mono⊢ η) ξ

idmono⊢ : ∀ {Γ A} → (𝒟 : Γ ⊢ A) → mono⊢ refl⊇ 𝒟 ≡ 𝒟
idmono⊢ (var 𝒾)   = cong var (idmono∋ 𝒾)
idmono⊢ (lam 𝒟)   = cong lam (idmono⊢ 𝒟)
idmono⊢ (app 𝒟 ℰ) = cong² app (idmono⊢ 𝒟) (idmono⊢ ℰ)

assocmono⊢ : ∀ {Γ Γ′ Γ″ A} → (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (𝒟 : Γ ⊢ A) →
                mono⊢ η′ (mono⊢ η 𝒟) ≡ mono⊢ (trans⊇ η′ η) 𝒟
assocmono⊢ η′ η (var 𝒾)   = cong var (assocmono∋ η′ η 𝒾)
assocmono⊢ η′ η (lam 𝒟)   = cong lam (assocmono⊢ (lift η′) (lift η) 𝒟)
assocmono⊢ η′ η (app 𝒟 ℰ) = cong² app (assocmono⊢ η′ η 𝒟) (assocmono⊢ η′ η ℰ)

idmono⊢⋆ : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ) → mono⊢⋆ refl⊇ ξ ≡ ξ
idmono⊢⋆ ∅       = refl
idmono⊢⋆ (ξ , 𝒟) = cong² _,_ (idmono⊢⋆ ξ) (idmono⊢ 𝒟)

assocmono⊢⋆ : ∀ {Γ Γ′ Γ″ Ξ} → (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) →
                 mono⊢⋆ η′ (mono⊢⋆ η ξ) ≡ mono⊢⋆ (trans⊇ η′ η) ξ
assocmono⊢⋆ η′ η ∅       = refl
assocmono⊢⋆ η′ η (ξ , 𝒟) = cong² _,_ (assocmono⊢⋆ η′ η ξ) (assocmono⊢ η′ η 𝒟)

refl⊢⋆ : ∀ {Γ} → Γ ⊢⋆ Γ
refl⊢⋆ {∅}     = ∅
refl⊢⋆ {Γ , A} = mono⊢⋆ (weak refl⊇) refl⊢⋆ , var zero

lookup⊢ : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ∋ A → Γ ⊢ A
lookup⊢ ξ 𝒾 = lookupAll ξ 𝒾

graft⊢ : ∀ {Γ Φ A} → Γ ⊢⋆ Φ → Φ ⊢ A → Γ ⊢ A
graft⊢ φ (var 𝒾)   = lookup⊢ φ 𝒾
graft⊢ φ (lam 𝒟)   = lam (graft⊢ (mono⊢⋆ (weak refl⊇) φ , var zero) 𝒟)
graft⊢ φ (app 𝒟 ℰ) = app (graft⊢ φ 𝒟) (graft⊢ φ ℰ)

graft⊢⋆ : ∀ {Γ Φ Ξ} → Γ ⊢⋆ Φ → Φ ⊢⋆ Ξ → Γ ⊢⋆ Ξ
graft⊢⋆ φ ξ = mapAll (graft⊢ φ) ξ

trans⊢⋆ : ∀ {Γ Γ′ Γ″} → Γ″ ⊢⋆ Γ′ → Γ′ ⊢⋆ Γ → Γ″ ⊢⋆ Γ
trans⊢⋆ γ′ ∅       = ∅
trans⊢⋆ γ′ (γ , 𝒟) = trans⊢⋆ γ′ γ , graft⊢ γ′ 𝒟


-- Normal forms.

mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : Cx → Ty → Set where
    lamⁿᶠ : ∀ {Γ A B} →
              Γ , A ⊢ⁿᶠ B →
              Γ ⊢ⁿᶠ A ⇒ B
    neⁿᶠ  : ∀ {Γ A} →
              Γ ⊢ⁿᵉ A →
              Γ ⊢ⁿᶠ A

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : Cx → Ty → Set where
    varⁿᵉ : ∀ {Γ A} →
              Γ ∋ A →
              Γ ⊢ⁿᵉ A
    appⁿᵉ : ∀ {Γ A B} →
              Γ ⊢ⁿᵉ A ⇒ B → Γ ⊢ⁿᶠ A →
              Γ ⊢ⁿᵉ B

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Cx → Ty⋆ → Set
Γ ⊢⋆ⁿᵉ Ξ = All (Γ ⊢ⁿᵉ_) Ξ

mutual
  mono⊢ⁿᶠ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (lamⁿᶠ 𝒟)   = lamⁿᶠ (mono⊢ⁿᶠ (lift η) 𝒟)
  mono⊢ⁿᶠ η (neⁿᶠ 𝒟)    = neⁿᶠ (mono⊢ⁿᵉ η 𝒟)

  mono⊢ⁿᵉ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (varⁿᵉ 𝒾)   = varⁿᵉ (mono∋ η 𝒾)
  mono⊢ⁿᵉ η (appⁿᵉ 𝒟 ℰ) = appⁿᵉ (mono⊢ⁿᵉ η 𝒟) (mono⊢ⁿᶠ η ℰ)

mono⊢⋆ⁿᵉ : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ⁿᵉ Ξ → Γ′ ⊢⋆ⁿᵉ Ξ
mono⊢⋆ⁿᵉ η ξ = mapAll (mono⊢ⁿᵉ η) ξ

mutual
  idmono⊢ⁿᶠ : ∀ {Γ A} → (𝒟 : Γ ⊢ⁿᶠ A) → mono⊢ⁿᶠ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ⁿᶠ (neⁿᶠ 𝒟)    = cong neⁿᶠ (idmono⊢ⁿᵉ 𝒟)
  idmono⊢ⁿᶠ (lamⁿᶠ 𝒟)   = cong lamⁿᶠ (idmono⊢ⁿᶠ 𝒟)

  idmono⊢ⁿᵉ : ∀ {Γ A} → (𝒟 : Γ ⊢ⁿᵉ A) → mono⊢ⁿᵉ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ⁿᵉ (varⁿᵉ 𝒾)   = cong varⁿᵉ (idmono∋ 𝒾)
  idmono⊢ⁿᵉ (appⁿᵉ 𝒟 ℰ) = cong² appⁿᵉ (idmono⊢ⁿᵉ 𝒟) (idmono⊢ⁿᶠ ℰ)

mutual
  assocmono⊢ⁿᶠ : ∀ {Γ Γ′ Γ″ A} → (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (𝒟 : Γ ⊢ⁿᶠ A) →
                    mono⊢ⁿᶠ η′ (mono⊢ⁿᶠ η 𝒟) ≡ mono⊢ⁿᶠ (trans⊇ η′ η) 𝒟
  assocmono⊢ⁿᶠ η′ η (neⁿᶠ 𝒟)    = cong neⁿᶠ (assocmono⊢ⁿᵉ η′ η 𝒟)
  assocmono⊢ⁿᶠ η′ η (lamⁿᶠ 𝒟)   = cong lamⁿᶠ (assocmono⊢ⁿᶠ (lift η′) (lift η) 𝒟)

  assocmono⊢ⁿᵉ : ∀ {Γ Γ′ Γ″ A} → (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (𝒟 : Γ ⊢ⁿᵉ A)  →
                    mono⊢ⁿᵉ η′ (mono⊢ⁿᵉ η 𝒟) ≡ mono⊢ⁿᵉ (trans⊇ η′ η) 𝒟
  assocmono⊢ⁿᵉ η′ η (varⁿᵉ 𝒾)   = cong varⁿᵉ (assocmono∋ η′ η 𝒾)
  assocmono⊢ⁿᵉ η′ η (appⁿᵉ 𝒟 ℰ) = cong² appⁿᵉ (assocmono⊢ⁿᵉ η′ η 𝒟) (assocmono⊢ⁿᶠ η′ η ℰ)

idmono⊢⋆ⁿᵉ : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ⁿᵉ Ξ) → mono⊢⋆ⁿᵉ refl⊇ ξ ≡ ξ
idmono⊢⋆ⁿᵉ ∅       = refl
idmono⊢⋆ⁿᵉ (ξ , 𝒟) = cong² _,_ (idmono⊢⋆ⁿᵉ ξ) (idmono⊢ⁿᵉ 𝒟)

assocmono⊢⋆ⁿᵉ : ∀ {Γ Γ′ Γ″ Ξ} → (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ⁿᵉ Ξ) →
                   mono⊢⋆ⁿᵉ η′ (mono⊢⋆ⁿᵉ η ξ) ≡ mono⊢⋆ⁿᵉ (trans⊇ η′ η) ξ
assocmono⊢⋆ⁿᵉ η′ η ∅       = refl
assocmono⊢⋆ⁿᵉ η′ η (ξ , 𝒟) = cong² _,_ (assocmono⊢⋆ⁿᵉ η′ η ξ) (assocmono⊢ⁿᵉ η′ η 𝒟)


-- Example derivations.

v₀ : ∀ {Γ A} →
       Γ , A ⊢ A
v₀ = var zero

v₁ : ∀ {Γ A B} →
       Γ , A , B ⊢ A
v₁ = var (suc zero)

v₂ : ∀ {Γ A B C} →
       Γ , A , B , C ⊢ A
v₂ = var (suc (suc zero))

iᶜ : ∀ {Γ A} →
       Γ ⊢ A ⇒ A
iᶜ = lam v₀

kᶜ : ∀ {Γ A B} →
       Γ ⊢ A ⇒ B ⇒ A
kᶜ = lam (lam v₁)

sᶜ : ∀ {Γ A B C} →
       Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
sᶜ = lam (lam (lam
       (app (app v₂ v₀) (app v₁ v₀))))

cᶜ : ∀ {Γ A B C} →
       Γ ⊢ (A ⇒ B ⇒ C) ⇒ B ⇒ A ⇒ C
cᶜ = lam (lam (lam
       (app (app v₂ v₀) v₁)))

bᶜ : ∀ {Γ A B C} →
       Γ ⊢ (B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
bᶜ = lam (lam (lam
       (app v₂ (app v₁ v₀))))

aᶜ : ∀ {Γ A B} →
       Γ ⊢ (A ⇒ A ⇒ B) ⇒ A ⇒ B
aᶜ = lam (lam
       (app (app v₁ v₀) v₀))


-- Example inference rules on derivations.

exch : ∀ {Γ A B C} →
         Γ ⊢ A ⇒ B ⇒ C →
         Γ ⊢ B ⇒ A ⇒ C
exch 𝒟 = app cᶜ 𝒟

comp : ∀ {Γ A B C} →
         Γ ⊢ B ⇒ C → Γ ⊢ A ⇒ B →
         Γ ⊢ A ⇒ C
comp 𝒟 ℰ = app (app bᶜ 𝒟) ℰ

cont : ∀ {Γ A B} →
         Γ ⊢ A ⇒ A ⇒ B →
         Γ ⊢ A ⇒ B
cont 𝒟 = app aᶜ 𝒟

det : ∀ {Γ A B} →
        Γ ⊢ A ⇒ B →
        Γ , A ⊢ B
det 𝒟 = app (mono⊢ (weak refl⊇) 𝒟) v₀
