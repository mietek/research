module FinLemmas where

open import Prelude
open import Category
open import Fin


--------------------------------------------------------------------------------
{-
                              id≥ ∘≥ e ≡ e                                      lid∘≥
                              e ∘≥ id≥ ≡ e                                      rid∘≥
                      (e₁ ∘≥ e₂) ∘≥ e₃ ≡ e₁ ∘≥ (e₂ ∘≥ e₃)                       assoc∘≥

                            renF id≥ i ≡ i                                      id-renF
                     renF (e₁ ∘≥ e₂) i ≡ (renF e₂ ∘ renF e₁) i                  comp-renF
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
  Geq : Category Nat _≥_
  Geq = record
          { id     = id≥
          ; _∘_    = _∘≥_
          ; lid∘   = lid∘≥
          ; rid∘   = rid∘≥
          ; assoc∘ = assoc∘≥
          }


--------------------------------------------------------------------------------


id-renF : ∀ {n} → (i : Fin n)
                → renF id≥ i ≡ i
id-renF zero    = refl
id-renF (suc i) = suc & id-renF i


comp-renF : ∀ {n n′ n″} → (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′) (i : Fin n)
                        → renF (e₁ ∘≥ e₂) i ≡ (renF e₂ ∘ renF e₁) i
comp-renF e₁        done      i       = refl
comp-renF e₁        (drop e₂) i       = suc & comp-renF e₁ e₂ i
comp-renF (drop e₁) (keep e₂) i       = suc & comp-renF e₁ e₂ i
comp-renF (keep e₁) (keep e₂) zero    = refl
comp-renF (keep e₁) (keep e₂) (suc i) = suc & comp-renF e₁ e₂ i


RenF : Presheaf Fin renF
RenF = record
         { idℱ   = funext! id-renF
         ; compℱ = \ e₁ e₂ → funext! (comp-renF e₁ e₂)
         }


--------------------------------------------------------------------------------
