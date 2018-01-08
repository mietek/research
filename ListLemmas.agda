{-# OPTIONS --rewriting #-}

module ListLemmas where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import List
open GetList


--------------------------------------------------------------------------------
{-
                      get (gets Ξ e) i ≡ (get Ξ ∘ renF e) i                     comp-get-renF

                            gets Ξ id≥ ≡ Ξ                                      id-gets
                     gets Ξ (e₁ ∘≥ e₂) ≡ gets (gets Ξ e₂) e₁                    comp-gets

                              id⊇ ∘⊇ η ≡ η                                      lid∘⊇
                              η ∘⊇ id⊇ ≡ η                                      rid∘⊇
                      (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)                       assoc∘⊇

                            ren∋ id⊇ 𝒾 ≡ 𝒾                                      id-ren∋
                     ren∋ (η₁ ∘⊇ η₂) 𝒾 ≡ (ren∋ η₂ ∘ ren∋ η₁) 𝒾                  comp-ren∋
-}
--------------------------------------------------------------------------------


len-gets : ∀ {X n n′} → (Ξ : List X) {{_ : len Ξ ≡ n′}} (e : n′ ≥ n)
                      → len (gets Ξ e) ≡ n
len-gets ∙       {{refl}} done     = refl
len-gets (Ξ , B) {{refl}} (drop e) = len-gets Ξ e
len-gets (Ξ , A) {{refl}} (keep e) = suc & len-gets Ξ e


{-# REWRITE len-gets #-}
comp-get-renF : ∀ {X n n′} → (Ξ : List X) {{_ : len Ξ ≡ n′}} (e : n′ ≥ n) (i : Fin n)
                           → get (gets Ξ e) i ≡ (get Ξ ∘ renF e) i
comp-get-renF ∙       {{refl}} done     ()
comp-get-renF (Ξ , B) {{refl}} (drop e) i       = comp-get-renF Ξ e i
comp-get-renF (Ξ , A) {{refl}} (keep e) zero    = refl
comp-get-renF (Ξ , B) {{refl}} (keep e) (suc i) = comp-get-renF Ξ e i


--------------------------------------------------------------------------------


module GetsList
  where
    id-gets : ∀ {X n} → (Ξ : List X) {{p : len Ξ ≡ n}}
                      → gets Ξ {{p}} id≥ ≡ Ξ
    id-gets ∙       {{refl}} = refl
    id-gets (Ξ , A) {{refl}} = (_, A) & id-gets Ξ


    comp-gets : ∀ {X n n′ n″} → (Ξ : List X) {{_ : len Ξ ≡ n″}} (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′)
                              → gets Ξ (e₁ ∘≥ e₂) ≡ gets (gets Ξ e₂) e₁
    comp-gets ∙       {{refl}} e₁        done      = refl
    comp-gets (Ξ , B) {{refl}} e₁        (drop e₂) = comp-gets Ξ e₁ e₂
    comp-gets (Ξ , B) {{refl}} (drop e₁) (keep e₂) = comp-gets Ξ e₁ e₂
    comp-gets (Ξ , A) {{refl}} (keep e₁) (keep e₂) = (_, A) & comp-gets Ξ e₁ e₂


    -- TODO: What is going on here?

    -- Gets : ∀ {X} → Presheaf {{Opposite Geq}} (\ n → Σ (List X) (\ Ξ → len Ξ ≡ n))
    --                                           (\ { e (Ξ , refl) → gets Ξ e , refl })
    -- Gets = record
    --          { idℱ   = funext! (\ { (Ξ , refl) → {!(_, refl) & id-gets Ξ!} })
    --          ; compℱ = \ e₁ e₂ → funext! (\ { (Ξ , refl) → {!(_, refl) & comp-gets Ξ e₂ e₁!} })
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
  OPE : ∀ {X} → Category (List X) _⊇_
  OPE = record
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
                    → ren∋ (η₁ ∘⊇ η₂) 𝒾 ≡ (ren∋ η₂ ∘ ren∋ η₁) 𝒾
comp-ren∋ η₁        done      𝒾       = refl
comp-ren∋ η₁        (drop η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (drop η₁) (keep η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (keep η₁) (keep η₂) zero    = refl
comp-ren∋ (keep η₁) (keep η₂) (suc 𝒾) = suc & comp-ren∋ η₁ η₂ 𝒾


Ren∋ : ∀ {X} → {A : X} → Presheaf (_∋ A) ren∋
Ren∋ = record
         { idℱ   = funext! id-ren∋
         ; compℱ = \ η₁ η₂ → funext! (comp-ren∋ η₁ η₂)
         }


--------------------------------------------------------------------------------
