{-# OPTIONS --rewriting #-}

module VecLemmas where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open GetVec


--------------------------------------------------------------------------------
{-
                      get (gets Ξ e) i ≡ (get Ξ ∘ renF e) i                     comp-get-renF

                              id⊇ ∘⊇ η ≡ η                                      lid∘⊇
                              η ∘⊇ id⊇ ≡ η                                      rid∘⊇
                      (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)                       assoc∘⊇

                            ren∋ id⊇ 𝒾 ≡ 𝒾                                      id-ren∋
                     ren∋ (η₁ ∘⊇ η₂) 𝒾 ≡ (ren∋ η₂ ∘ ren∋ η₁) 𝒾                  comp-ren∋
-}
--------------------------------------------------------------------------------


comp-get-renF : ∀ {X n n′} → (Ξ : Vec X n′) (e : n′ ≥ n) (i : Fin n)
                           → get (gets Ξ e) i ≡ (get Ξ ∘ renF e) i
comp-get-renF ∙       done     ()
comp-get-renF (Ξ , B) (drop e) i       = comp-get-renF Ξ e i
comp-get-renF (Ξ , A) (keep e) zero    = refl
comp-get-renF (Ξ , B) (keep e) (suc i) = comp-get-renF Ξ e i


--------------------------------------------------------------------------------


{-# REWRITE lid∘≥ #-}
lid∘⊇ : ∀ {X n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                     → (η : Ξ′ ⊇⟨ e ⟩ Ξ)
                     → id⊇ ∘⊇ η ≡ η
lid∘⊇ done     = refl
lid∘⊇ (drop η) = drop & lid∘⊇ η
lid∘⊇ (keep η) = keep & lid∘⊇ η


{-# REWRITE rid∘≥ #-}
rid∘⊇ : ∀ {X n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                     → (η : Ξ′ ⊇⟨ e ⟩ Ξ)
                     → η ∘⊇ id⊇ ≡ η
rid∘⊇ done     = refl
rid∘⊇ (drop η) = drop & rid∘⊇ η
rid∘⊇ (keep η) = keep & rid∘⊇ η


{-# REWRITE assoc∘≥ #-}
assoc∘⊇ : ∀ {X n n′ n″ n‴ e₁ e₂ e₃} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″} {Ξ‴ : Vec X n‴}
                                    → (η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ) (η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′) (η₃ : Ξ‴ ⊇⟨ e₃ ⟩ Ξ″)
                                    → (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)
assoc∘⊇ η₁        η₂        done      = refl
assoc∘⊇ η₁        η₂        (drop η₃) = drop & assoc∘⊇ η₁ η₂ η₃
assoc∘⊇ η₁        (drop η₂) (keep η₃) = drop & assoc∘⊇ η₁ η₂ η₃
assoc∘⊇ (drop η₁) (keep η₂) (keep η₃) = drop & assoc∘⊇ η₁ η₂ η₃
assoc∘⊇ (keep η₁) (keep η₂) (keep η₃) = keep & assoc∘⊇ η₁ η₂ η₃


instance
  OPE : ∀ {X} → Category (Σ Nat (Vec X))
                          (\ { (n′ , Ξ′) (n , Ξ) →
                            Σ (n′ ≥ n) (\ e → Ξ′ ⊇⟨ e ⟩ Ξ )})
  OPE = record
          { id     = id≥ , id⊇
          ; _∘_    = \ { (e₁ , η₁) (e₂ , η₂) → e₁ ∘≥ e₂ , η₁ ∘⊇ η₂ }
          ; lid∘   = \ { (e , η) → (e ,_) & lid∘⊇ η }
          ; rid∘   = \ { (e , η) → (e ,_) & rid∘⊇ η }
          ; assoc∘ = \ { (e₁ , η₁) (e₂ , η₂) (e₃ , η₃) →
                       ((e₁ ∘≥ e₂) ∘≥ e₃ ,_) & assoc∘⊇ η₁ η₂ η₃ }
          }


--------------------------------------------------------------------------------


{-# REWRITE id-renF #-}
id-ren∋ : ∀ {X A n i} → {Ξ : Vec X n}
                      → (𝒾 : Ξ ∋⟨ i ⟩ A)
                      → ren∋ id⊇ 𝒾 ≡ 𝒾
id-ren∋ zero    = refl
id-ren∋ (suc 𝒾) = suc & id-ren∋ 𝒾


{-# REWRITE comp-renF #-}
comp-ren∋ : ∀ {X A n n′ n″ e₁ e₂ i} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                    → (η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ) (η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′) (𝒾 : Ξ ∋⟨ i ⟩ A)
                                    → ren∋ (η₁ ∘⊇ η₂) 𝒾 ≡ (ren∋ η₂ ∘ ren∋ η₁) 𝒾
comp-ren∋ η₁        done      𝒾       = refl
comp-ren∋ η₁        (drop η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (drop η₁) (keep η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (keep η₁) (keep η₂) zero    = refl
comp-ren∋ (keep η₁) (keep η₂) (suc 𝒾) = suc & comp-ren∋ η₁ η₂ 𝒾


Ren∋ : ∀ {X A} → Presheaf {{OPE {X}}}
                           (\ { (n , Ξ) →
                             Σ (Fin n) (\ i → Ξ ∋⟨ i ⟩ A) })
                           (\ { (e , η) (i , 𝒾) → renF e i , ren∋ η 𝒾 })
Ren∋ = record
         { idℱ   = funext! (\ { (i , 𝒾) →
                     (renF id≥ i ,_) & id-ren∋ 𝒾 })
         ; compℱ = \ { (e₁ , η₁) (e₂ , η₂) →
                     funext! (\ { (i , 𝒾) →
                       (renF (e₁ ∘≥ e₂) i ,_) & comp-ren∋ η₁ η₂ 𝒾 }) }
         }


--------------------------------------------------------------------------------
