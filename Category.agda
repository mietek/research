module Category where

open import Prelude


--------------------------------------------------------------------------------


record Category {ℓ ℓ′} (X : Set ℓ) (_▻_ : X → X → Set ℓ′)
                     : Set (ℓ ⊔ ℓ′)
  where
    field
      id : ∀ {x} → x ▻ x

      _∘_ : ∀ {x y z} → y ▻ x → z ▻ y
                      → z ▻ x

      lid∘ : ∀ {x y} → (f : y ▻ x)
                     → id ∘ f ≡ f

      rid∘ : ∀ {x y} → (f : y ▻ x)
                     → f ∘ id ≡ f

      assoc∘ : ∀ {x y z a} → (f : y ▻ x) (g : z ▻ y) (h : a ▻ z)
                           → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

open Category {{...}} public


--------------------------------------------------------------------------------


record Functor {ℓ ℓ′ ℓ″ ℓ‴} {X : Set ℓ} {_▻_ : X → X → Set ℓ′}
                            {Y : Set ℓ″} {_►_ : Y → Y → Set ℓ‴}
                            (C : Category X _▻_) (D : Category Y _►_)
                            (f : X → Y) (ℱ : ∀ {x y} → y ▻ x → f y ► f x)
                          : Set (ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ ℓ‴)
  where
    private
      instance _ = C
      instance _ = D

    field
      idℱ : ∀ {x} → ℱ (id {x = x}) ≡ id

      compℱ : ∀ {x y z} → (f : z ▻ y) (g : y ▻ x)
                        → ℱ (g ∘ f) ≡ ℱ g ∘ ℱ f


--------------------------------------------------------------------------------


Opposite : ∀ {ℓ ℓ′} → {X : Set ℓ} {_▻_ : X → X → Set ℓ′}
                    → Category X _▻_
                    → Category X (flip _▻_)
Opposite C = record
               { id     = id
               ; _∘_    = flip _∘_
               ; lid∘   = rid∘
               ; rid∘   = lid∘
               ; assoc∘ = \ f g h → assoc∘ h g f ⁻¹
               }
  where
    private
      instance _ = C


instance
  𝗦𝗲𝘁 : (ℓ : Level) → Category (Set ℓ) Π
  𝗦𝗲𝘁 ℓ = record
            { id     = \ x → x
            ; _∘_    = \ f g x → f (g x)
            ; lid∘   = \ f → refl
            ; rid∘   = \ f → refl
            ; assoc∘ = \ f g h → refl
            }


instance
  𝗦𝗲𝘁₀ : Category Set₀ Π
  𝗦𝗲𝘁₀ = 𝗦𝗲𝘁 lzero


Presheaf : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ′} {_▻_ : X → X → Set ℓ″}
                          (C : Category X _▻_)
                       → (P : X → Set ℓ) (ℱ : ∀ {x y} → x ▻ y → P y → P x)
                       → Set _
Presheaf {ℓ} C = Functor (Opposite C) (𝗦𝗲𝘁 ℓ)


--------------------------------------------------------------------------------


record NatTrans {ℓ ℓ′ ℓ″ ℓ‴} {X : Set ℓ} {_▻_ : X → X → Set ℓ′}
                             {Y : Set ℓ″} {_►_ : Y → Y → Set ℓ‴}
                             {{C : Category X _▻_}} {{D : Category Y _►_}}
                             {f : X → Y} {ℱ : ∀ {x y} → y ▻ x → f y ► f x}
                             {g : X → Y} {𝒢 : ∀ {x y} → y ▻ x → g y ► g x}
                             (F : Functor C D f ℱ) (G : Functor C D g 𝒢)
                           : Set (ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ ℓ‴)
  where
    field
      𝛼 : ∀ {x} → f x ► g x

      nat𝛼 : ∀ {x y} → (f : x ▻ y)
                     → 𝛼 ∘ ℱ f ≡ 𝒢 f ∘ 𝛼


--------------------------------------------------------------------------------
