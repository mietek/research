module Scratch2 where

open import Prelude
open import List
open import AllList



infix 4 _∋⋆_
_∋⋆_ : ∀ {X} → List X → List X → Set
Γ ∋⋆ Ξ = All (Γ ∋_) Ξ


rens∋ : ∀ {X} → {Γ Γ′ Ξ : List X}
              → (η : Γ′ ⊇ Γ) → Γ ∋⋆ Ξ
              → Γ′ ∋⋆ Ξ
rens∋ η ξ = maps (ren∋ η) ξ

wks∋ : ∀ {X A} → {Γ Ξ : List X}
               → Γ ∋⋆ Ξ
               → Γ , A ∋⋆ Ξ
wks∋ ξ = rens∋ (drop id⊇) ξ

lifts∋ : ∀ {X A} → {Γ Ξ : List X}
                 → Γ ∋⋆ Ξ
                 → Γ , A ∋⋆ Ξ , A
lifts∋ ξ = wks∋ ξ , zero

hyps∋ : ∀ {X} → {Γ Γ′ : List X}
              → (η : Γ′ ⊇ Γ)
              → Γ′ ∋⋆ Γ
hyps∋ done     = ∙
hyps∋ (drop η) = wks∋ (hyps∋ η)
hyps∋ (keep η) = lifts∋ (hyps∋ η)

ids∋ : ∀ {X} → {Γ : List X}
             → Γ ∋⋆ Γ
ids∋ = hyps∋ id⊇


sub∋ : ∀ {X A} → {Γ Ξ : List X}
               → Γ ∋⋆ Ξ → Ξ ∋ A
               → Γ ∋ A
sub∋ (ξ , 𝒾) zero    = 𝒾
sub∋ (ξ , 𝒿) (suc 𝒾) = sub∋ ξ 𝒾

subs∋ : ∀ {X} → {Γ Ξ Ψ : List X}
              → Γ ∋⋆ Ξ → Ξ ∋⋆ Ψ
              → Γ ∋⋆ Ψ
subs∋ ξ ψ = maps (sub∋ ξ) ψ


-- id-sub∋ : ∀ {X A} → {Γ : List X}
--                   → (𝒾 : Γ ∋ A)
--                   → sub∋ ids∋ 𝒾 ≡ 𝒾
-- id-sub∋ zero    = refl
-- id-sub∋ (suc 𝒾) = {!!}


-- lid-subs∋ : ∀ {X} → {Γ Ξ : List X}
--                   → (ξ : Γ ∋⋆ Ξ)
--                   → subs∋ ids∋ ξ ≡ ξ
-- lid-subs∋ ∙       = refl
-- lid-subs∋ (ξ , 𝒾) = _,_ & lid-subs∋ ξ ⊗ id-sub∋ 𝒾

-- rid-subs∋ : ∀ {X} → {Γ Ξ : List X}
--                   → (ξ : Γ ∋⋆ Ξ)
--                   → subs∋ ξ ids∋ ≡ ξ
-- rid-subs∋ = {!!}

-- assocs-subs∋ : ∀ {X} → {Γ Ξ Ψ Φ : List X}
--                      → (ξ : Γ ∋⋆ Ξ) (ψ : Ξ ∋⋆ Ψ) (φ : Ψ ∋⋆ Φ)
--                      → subs∋ (subs∋ ξ ψ) φ ≡ subs∋ ξ (subs∋ ψ φ)
-- assocs-subs∋ = {!!}


-- Wat : ∀ {X} → Category (List X) _∋⋆_
-- Wat = record
--         { id     = ids∋
--         ; _∘_    = flip subs∋
--         ; lid∘   = rid-subs∋
--         ; rid∘   = lid-subs∋
--         ; assoc∘ = \ ξ₁ ξ₂ ξ₃ → assocs-subs∋ ξ₃ ξ₂ ξ₁ ⁻¹
--         }


-- id-get : ∀ {X A} → {Ξ : List X}
--                  → (𝒾 : Ξ ∋ A)
--                  → get ids∋ 𝒾 ≡ 𝒾
-- id-get zero    = refl
-- id-get (suc 𝒾) = {!id-get 𝒾!}
