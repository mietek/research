{-# OPTIONS --rewriting #-}

module A201801.AllList where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas


--------------------------------------------------------------------------------


data All {X} (P : X → Set) : List X → Set
  where
    ∙   : All P ∙
    _,_ : ∀ {Ξ A} → All P Ξ → P A → All P (Ξ , A)


maps : ∀ {X P Q} → {Ξ : List X}
                 → (∀ {A} → P A → Q A) → All P Ξ
                 → All Q Ξ
maps f ∙       = ∙
maps f (ξ , a) = maps f ξ , f a


-- TODO: Remove this

-- gmaps : ∀ {X Y P Q} → {Ξ : List X} {f : X → Y}
--                     → (∀ {A} → P A → Q (f A)) → All P Ξ
--                     → All Q (map f Ξ)
-- gmaps p ∙       = ∙
-- gmaps p (ξ , a) = gmaps p ξ , p a


--------------------------------------------------------------------------------


get : ∀ {X P A} → {Ξ : List X}
                → All P Ξ → Ξ ∋ A
                → P A
get (ξ , a) zero    = a
get (ξ , b) (suc i) = get ξ i


gets : ∀ {X P} → {Ξ Ξ′ : List X}
               → All P Ξ′ → Ξ′ ⊇ Ξ
               → All P Ξ
gets ξ       done     = ∙
gets (ξ , b) (drop η) = gets ξ η
gets (ξ , a) (keep η) = gets ξ η , a


--------------------------------------------------------------------------------


infix 4 _⊇◇⟨_⟩_
data _⊇◇⟨_⟩_ {X P} : {Ξ Ξ′ : List X} → All P Ξ′ → Ξ′ ⊇ Ξ → All P Ξ → Set
  where
    done : ∙ ⊇◇⟨ done ⟩ ∙

    drop : ∀ {A Ξ Ξ′} → {η : Ξ′ ⊇ Ξ} {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                      → ξ′ ⊇◇⟨ η ⟩ ξ
                      → ξ′ , a ⊇◇⟨ drop η ⟩ ξ

    keep : ∀ {A Ξ Ξ′} → {η : Ξ′ ⊇ Ξ} {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                      → ξ′ ⊇◇⟨ η ⟩ ξ
                      → ξ′ , a ⊇◇⟨ keep η ⟩ ξ , a


id⊇◇ : ∀ {X P} → {Ξ : List X} {ξ : All P Ξ}
               → ξ ⊇◇⟨ id ⟩ ξ
id⊇◇ {ξ = ∙}     = done
id⊇◇ {ξ = ξ , a} = keep id⊇◇


_∘⊇◇_ : ∀ {X P} → {Ξ Ξ′ Ξ″ : List X} {η₁ : Ξ′ ⊇ Ξ} {η₂ : Ξ″ ⊇ Ξ′}
                   {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″}
                → ξ′ ⊇◇⟨ η₁ ⟩ ξ → ξ″ ⊇◇⟨ η₂ ⟩ ξ′
                → ξ″ ⊇◇⟨ η₁ ∘ η₂ ⟩ ξ
𝜂₁      ∘⊇◇ done    = 𝜂₁
𝜂₁      ∘⊇◇ drop 𝜂₂ = drop (𝜂₁ ∘⊇◇ 𝜂₂)
drop 𝜂₁ ∘⊇◇ keep 𝜂₂ = drop (𝜂₁ ∘⊇◇ 𝜂₂)
keep 𝜂₁ ∘⊇◇ keep 𝜂₂ = keep (𝜂₁ ∘⊇◇ 𝜂₂)


--------------------------------------------------------------------------------


infix 4 _∋◇⟨_⟩_
data _∋◇⟨_⟩_ {X P} : ∀ {A} → {Ξ : List X} → All P Ξ → Ξ ∋ A → P A → Set
  where
    zero : ∀ {Ξ A} → {a : P A} {ξ : All P Ξ}
                   → ξ , a ∋◇⟨ zero ⟩ a

    suc : ∀ {B Ξ A} → {i : Ξ ∋ A} {a : P A} {b : P B} {ξ : All P Ξ}
                    → ξ ∋◇⟨ i ⟩ a
                    → ξ , b ∋◇⟨ suc i ⟩ a


ren∋◇ : ∀ {X P A} → {Ξ Ξ′ : List X} {η : Ξ′ ⊇ Ξ} {i : Ξ ∋ A}
                     {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                  → ξ′ ⊇◇⟨ η ⟩ ξ → ξ ∋◇⟨ i ⟩ a
                  → ξ′ ∋◇⟨ ren∋ η i ⟩ a
ren∋◇ done     𝑖       = 𝑖
ren∋◇ (drop 𝜂) 𝑖       = suc (ren∋◇ 𝜂 𝑖)
ren∋◇ (keep 𝜂) zero    = zero
ren∋◇ (keep 𝜂) (suc 𝑖) = suc (ren∋◇ 𝜂 𝑖)


--------------------------------------------------------------------------------


-- data All◇ {X P} (𝑃 : ∀ {A : X} → P A → Set)
--               : ∀ {Ξ} → All P Ξ → Set
--   where
--     ∙ : All◇ 𝑃 ∙

--     _,_ : ∀ {Ξ A} → {ξ : All P Ξ} {a : P A}
--                   → All◇ 𝑃 ξ → 𝑃 a
--                   → All◇ 𝑃 (ξ , a)


-- get◇ : ∀ {X P A} → {Ξ : List X} {a : P A}
--                     {ξ : All P Ξ} {i : Ξ ∋ A}
--                     {𝑃 : ∀ {A} → P A → Set}
--                  → All◇ 𝑃 ξ → ξ ∋◇⟨ i ⟩ a
--                  → 𝑃 a
-- get◇ (𝜉 , 𝑎) zero    = 𝑎
-- get◇ (𝜉 , 𝑏) (suc 𝑖) = get◇ 𝜉 𝑖


-- gets◇ : ∀ {X P} → {Ξ Ξ′ : List X} {η : Ξ′ ⊇ Ξ}
--                    {ξ : All P Ξ} {ξ′ : All P Ξ′}
--                    {𝑃 : ∀ {A} → P A → Set}
--                 → All◇ 𝑃 ξ′ → ξ′ ⊇◇⟨ η ⟩ ξ
--                 → All◇ 𝑃 ξ
-- gets◇ ∙       done     = ∙
-- gets◇ (𝜉 , 𝑏) (drop 𝜂) = gets◇ 𝜉 𝜂
-- gets◇ (𝜉 , 𝑎) (keep 𝜂) = gets◇ 𝜉 𝜂 , 𝑎


-- maps◇ : ∀ {X P} → {Ξ : List X} {Q : X → Set}
--                    {f : ∀ {A} → P A → Q A} {ξ : All P Ξ}
--                    {𝑃 : ∀ {A} → P A → Set} {𝑄 : ∀ {A} → Q A → Set}
--                 → (∀ {A} → {a : P A} → 𝑃 a → 𝑄 (f a)) → All◇ 𝑃 ξ
--                 → All◇ 𝑄 (maps f ξ)
-- maps◇ 𝑓 ∙       = ∙
-- maps◇ 𝑓 (𝜉 , 𝑎) = maps◇ 𝑓 𝜉 , 𝑓 𝑎


-- --------------------------------------------------------------------------------
