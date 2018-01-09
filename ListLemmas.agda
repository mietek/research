{-# OPTIONS --rewriting #-}

module ListLemmas where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import List


--------------------------------------------------------------------------------
{-
                      GET (GETS Ξ e) i ≡ (GET Ξ ∘ REN∋ e) i                     comp-GET-REN∋

                            GETS Ξ id≥ ≡ Ξ                                      id-GETS   ⎱ 𝐆𝐄𝐓𝐒
                      GETS Ξ (e₁ ∘ e₂) ≡ GETS (GETS Ξ e₂) e₁                    comp-GETS ⎰

                              id⊇ ∘⊇ η ≡ η                                      lid∘⊇   ⎫
                              η ∘⊇ id⊇ ≡ η                                      rid∘⊇   ⎬ 𝐎𝐏𝐄
                      (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)                       assoc∘⊇ ⎭

                            ren∋ id⊇ 𝒾 ≡ 𝒾                                      id-ren∋   ⎱ 𝐫𝐞𝐧∋
                      ren∋ (η₁ ∘ η₂) 𝒾 ≡ (ren∋ η₂ ∘ ren∋ η₁) 𝒾                  comp-ren∋ ⎰
-}
--------------------------------------------------------------------------------


len-GETS : ∀ {X n n′} → (Ξ : List X) {{_ : len Ξ ≡ n′}} (e : n′ ≥ n)
                      → len (GETS Ξ e) ≡ n
len-GETS ∙       {{refl}} done     = refl
len-GETS (Ξ , B) {{refl}} (drop e) = len-GETS Ξ e
len-GETS (Ξ , A) {{refl}} (keep e) = suc & len-GETS Ξ e


{-# REWRITE len-GETS #-}
comp-GET-REN∋ : ∀ {X n n′} → (Ξ : List X) {{_ : len Ξ ≡ n′}} (e : n′ ≥ n) (i : Fin n)
                           → GET (GETS Ξ e) i ≡ (GET Ξ ∘ REN∋ e) i
comp-GET-REN∋ ∙       {{refl}} done     ()
comp-GET-REN∋ (Ξ , B) {{refl}} (drop e) i       = comp-GET-REN∋ Ξ e i
comp-GET-REN∋ (Ξ , A) {{refl}} (keep e) zero    = refl
comp-GET-REN∋ (Ξ , B) {{refl}} (keep e) (suc i) = comp-GET-REN∋ Ξ e i


--------------------------------------------------------------------------------


id-GETS : ∀ {X n} → (Ξ : List X) {{p : len Ξ ≡ n}}
                  → GETS Ξ {{p}} id≥ ≡ Ξ
id-GETS ∙       {{refl}} = refl
id-GETS (Ξ , A) {{refl}} = (_, A) & id-GETS Ξ


comp-GETS : ∀ {X n n′ n″} → (Ξ : List X) {{_ : len Ξ ≡ n″}} (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′)
                          → GETS Ξ (e₁ ∘ e₂) ≡ GETS (GETS Ξ e₂) e₁
comp-GETS ∙       {{refl}} e₁        done      = refl
comp-GETS (Ξ , B) {{refl}} e₁        (drop e₂) = comp-GETS Ξ e₁ e₂
comp-GETS (Ξ , B) {{refl}} (drop e₁) (keep e₂) = comp-GETS Ξ e₁ e₂
comp-GETS (Ξ , A) {{refl}} (keep e₁) (keep e₂) = (_, A) & comp-GETS Ξ e₁ e₂


-- TODO: What is going on here?

-- 𝐆𝐄𝐓𝐒 : ∀ {X} → Presheaf {{Opposite 𝐆𝐄𝐐}} (\ n → Σ (List X) (\ Ξ → len Ξ ≡ n))
--                                           (\ { e (Ξ , refl) → GETS Ξ e , refl })
-- 𝐆𝐄𝐓𝐒 = record
--          { idℱ   = funext! (\ { (Ξ , refl) → {!(_, refl) & id-GETS Ξ!} })
--          ; compℱ = \ e₁ e₂ → funext! (\ { (Ξ , refl) → {!(_, refl) & comp-GETS Ξ e₂ e₁!} })
--          }


--------------------------------------------------------------------------------


lid∘⊇ : ∀ {X} → {Ξ Ξ′ : List X}
              → (η : Ξ′ ⊇ Ξ)
              → id⊇ ∘⊇ η ≡ η
lid∘⊇ done     = refl
lid∘⊇ (drop η) = drop & lid∘⊇ η
lid∘⊇ (keep η) = keep & lid∘⊇ η


rid∘⊇ : ∀ {X} → {Ξ Ξ′ : List X}
              → (η : Ξ′ ⊇ Ξ)
              → η ∘⊇ id⊇ ≡ η
rid∘⊇ done     = refl
rid∘⊇ (drop η) = drop & rid∘⊇ η
rid∘⊇ (keep η) = keep & rid∘⊇ η


assoc∘⊇ : ∀ {X} → {Ξ Ξ′ Ξ″ Ξ‴ : List X}
                → (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′) (η₃ : Ξ‴ ⊇ Ξ″)
                → (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)
assoc∘⊇ η₁        η₂        done      = refl
assoc∘⊇ η₁        η₂        (drop η₃) = drop & assoc∘⊇ η₁ η₂ η₃
assoc∘⊇ η₁        (drop η₂) (keep η₃) = drop & assoc∘⊇ η₁ η₂ η₃
assoc∘⊇ (drop η₁) (keep η₂) (keep η₃) = drop & assoc∘⊇ η₁ η₂ η₃
assoc∘⊇ (keep η₁) (keep η₂) (keep η₃) = keep & assoc∘⊇ η₁ η₂ η₃


instance
  𝐎𝐏𝐄 : ∀ {X} → Category (List X) _⊇_
  𝐎𝐏𝐄 = record
          { id     = id⊇
          ; _∘_    = _∘⊇_
          ; lid∘   = lid∘⊇
          ; rid∘   = rid∘⊇
          ; assoc∘ = assoc∘⊇
          }


--------------------------------------------------------------------------------


id-ren∋ : ∀ {X A} → {Ξ : List X}
                  → (𝒾 : Ξ ∋ A)
                  → ren∋ id⊇ 𝒾 ≡ 𝒾
id-ren∋ zero    = refl
id-ren∋ (suc 𝒾) = suc & id-ren∋ 𝒾


comp-ren∋ : ∀ {X A} → {Ξ Ξ′ Ξ″ : List X}
                    → (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′) (𝒾 : Ξ ∋ A)
                    → ren∋ (η₁ ∘ η₂) 𝒾 ≡ (ren∋ η₂ ∘ ren∋ η₁) 𝒾
comp-ren∋ η₁        done      𝒾       = refl
comp-ren∋ η₁        (drop η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (drop η₁) (keep η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (keep η₁) (keep η₂) zero    = refl
comp-ren∋ (keep η₁) (keep η₂) (suc 𝒾) = suc & comp-ren∋ η₁ η₂ 𝒾


𝐫𝐞𝐧∋ : ∀ {X} → {A : X} → Presheaf (_∋ A) ren∋
𝐫𝐞𝐧∋ = record
         { idℱ   = funext! id-ren∋
         ; compℱ = \ η₁ η₂ → funext! (comp-ren∋ η₁ η₂)
         }


--------------------------------------------------------------------------------
