{-# OPTIONS --rewriting #-}

module A201801.FinLemmas where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin


--------------------------------------------------------------------------------
{-
                              id≥ ∘≥ e ≡ e                                      lid∘≥
                              e ∘≥ id≥ ≡ e                                      rid∘≥
                      (e₁ ∘≥ e₂) ∘≥ e₃ ≡ e₁ ∘≥ (e₂ ∘≥ e₃)                       assoc∘≥
                                                                                𝐆𝐄𝐐

                             REN∋ id I ≡ I                                      id-REN∋
                     REN∋ (e₁ ∘≥ e₂) I ≡ (REN∋ e₂ ∘ REN∋ e₁) I                  comp-REN∋
                                                                                𝐑𝐄𝐍∋
-}
--------------------------------------------------------------------------------


lid∘≥ : ∀ {n n′} → (e : n′ ≥ n)
                 → id≥ ∘≥ e ≡ e
lid∘≥ done     = refl
lid∘≥ (drop e) = drop & lid∘≥ e
lid∘≥ (keep e) = keep & lid∘≥ e


rid∘≥ : ∀ {n n′} → (e : n′ ≥ n)
                 → e ∘≥ id≥ ≡ e
rid∘≥ done     = refl
rid∘≥ (drop e) = drop & rid∘≥ e
rid∘≥ (keep e) = keep & rid∘≥ e


assoc∘≥ : ∀ {n n′ n″ n‴} → (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′) (e₃ : n‴ ≥ n″)
                         → (e₁ ∘≥ e₂) ∘≥ e₃ ≡ e₁ ∘≥ (e₂ ∘≥ e₃)
assoc∘≥ e₁        e₂        done      = refl
assoc∘≥ e₁        e₂        (drop e₃) = drop & assoc∘≥ e₁ e₂ e₃
assoc∘≥ e₁        (drop e₂) (keep e₃) = drop & assoc∘≥ e₁ e₂ e₃
assoc∘≥ (drop e₁) (keep e₂) (keep e₃) = drop & assoc∘≥ e₁ e₂ e₃
assoc∘≥ (keep e₁) (keep e₂) (keep e₃) = keep & assoc∘≥ e₁ e₂ e₃


instance
  𝐆𝐄𝐐 : Category Nat _≥_
  𝐆𝐄𝐐 = record
          { id     = id≥
          ; _∘_    = _∘≥_
          ; lid∘   = lid∘≥
          ; rid∘   = rid∘≥
          ; assoc∘ = assoc∘≥
          }


--------------------------------------------------------------------------------


id-REN∋ : ∀ {n} → (I : Fin n)
                → REN∋ id I ≡ I
id-REN∋ zero    = refl
id-REN∋ (suc I) = suc & id-REN∋ I


comp-REN∋ : ∀ {n n′ n″} → (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′) (I : Fin n)
                        → REN∋ (e₁ ∘ e₂) I ≡ (REN∋ e₂ ∘ REN∋ e₁) I
comp-REN∋ e₁        done      I       = refl
comp-REN∋ e₁        (drop e₂) I       = suc & comp-REN∋ e₁ e₂ I
comp-REN∋ (drop e₁) (keep e₂) I       = suc & comp-REN∋ e₁ e₂ I
comp-REN∋ (keep e₁) (keep e₂) zero    = refl
comp-REN∋ (keep e₁) (keep e₂) (suc I) = suc & comp-REN∋ e₁ e₂ I


𝐑𝐄𝐍∋ : Presheaf 𝐆𝐄𝐐 Fin
𝐑𝐄𝐍∋ = record
         { ℱ     = REN∋
         ; idℱ   = funext! id-REN∋
         ; compℱ = \ e₁ e₂ → funext! (comp-REN∋ e₁ e₂)
         }


--------------------------------------------------------------------------------
