{-# OPTIONS --rewriting #-}

module A201801.Category where

open import A201801.Prelude


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


Product : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {_▻_ : X → X → Set ℓ′}
                            {Y : Set ℓ″} {_►_ : Y → Y → Set ℓ‴}
                         → Category X _▻_ → Category Y _►_
                         → Category (X × Y) (\ { (x , a) (y , b) → x ▻ y × a ► b })
Product C D = record
                { id     = id , id
                ; _∘_    = \ { (f , p) (g , q) → f ∘ g , p ∘ q }
                ; lid∘   = \ { (f , p) → _,_ & lid∘ f ⊗ lid∘ p }
                ; rid∘   = \ { (f , p) → _,_ & rid∘ f ⊗ rid∘ p }
                ; assoc∘ = \ { (f , p) (g , q) (h , r) → _,_ & assoc∘ f g h ⊗ assoc∘ p q r }
                }
  where
    private
      instance _ = C
      instance _ = D


--------------------------------------------------------------------------------


record Functor {ℓ ℓ′ ℓ″ ℓ‴} {X : Set ℓ} {_▻_ : X → X → Set ℓ′}
                            {Y : Set ℓ″} {_►_ : Y → Y → Set ℓ‴}
                            (C : Category X _▻_) (D : Category Y _►_)
                            (f : X → Y)
                          : Set (ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ ℓ‴)
  where
    private
      instance _ = C
      instance _ = D

    field
      ℱ : ∀ {x y} → y ▻ x → f y ► f x

      idℱ : ∀ {x : X} → ℱ (id {x = x}) ≡ id

      compℱ : ∀ {x y z} → (f : z ▻ y) (g : y ▻ x)
                        → ℱ (g ∘ f) ≡ ℱ g ∘ ℱ f

open Functor {{...}} public


--------------------------------------------------------------------------------


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
                       → (P : X → Set ℓ)
                       → Set _
Presheaf {ℓ} C = Functor (Opposite C) (𝗦𝗲𝘁 ℓ)


--------------------------------------------------------------------------------


-- TODO: broken
-- record NatTrans {ℓ ℓ′ ℓ″ ℓ‴} {X : Set ℓ} {_▻_ : X → X → Set ℓ′}
--                              {Y : Set ℓ″} {_►_ : Y → Y → Set ℓ‴}
--                              {{C : Category X _▻_}} {{D : Category Y _►_}}
--                              {f : X → Y}
--                              {g : X → Y}
--                              (F : Functor C D f) (G : Functor C D g)
--                            : Set (ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ ℓ‴)
--   where
--     field
--       𝛼 : ∀ {x} → f x ► g x

--       nat𝛼 : ∀ {x y} → (f : x ▻ y)
--                      → 𝛼 ∘ Functor.ℱ F f ≡ Functor.ℱ G f ∘ 𝛼


-- --------------------------------------------------------------------------------
