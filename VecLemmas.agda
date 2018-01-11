{-# OPTIONS --rewriting #-}

module VecLemmas where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec


--------------------------------------------------------------------------------
{-
                      GET (GETS Ξ e) i ≡ (GET Ξ ∘ REN∋ e) i                     comp-GET-REN∋

                             GETS ξ id ≡ ξ                                      id-GETS   ⎱ 𝐆𝐄𝐓𝐒
                      GETS ξ (η₁ ∘ η₂) ≡ GETS (GETS ξ η₂) η₁                    comp-GETS ⎰

                              id⊇ ∘⊇ η ≡ η                                      lid∘⊇   ⎫
                              η ∘⊇ id⊇ ≡ η                                      rid∘⊇   ⎬ 𝐎𝐏𝐄
                      (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)                       assoc∘⊇ ⎭

                             ren∋ id 𝒾 ≡ 𝒾                                      id-ren∋   ⎱ 𝐫𝐞𝐧∋
                      ren∋ (η₁ ∘ η₂) 𝒾 ≡ (ren∋ η₂ ∘ ren∋ η₁) 𝒾                  comp-ren∋ ⎰
-}
--------------------------------------------------------------------------------


comp-GET-REN∋ : ∀ {X n n′} → (Ξ : Vec X n′) (e : n′ ≥ n) (i : Fin n)
                           → GET (GETS Ξ e) i ≡ (GET Ξ ∘ REN∋ e) i
comp-GET-REN∋ ∙       done     ()
comp-GET-REN∋ (Ξ , B) (drop e) i       = comp-GET-REN∋ Ξ e i
comp-GET-REN∋ (Ξ , A) (keep e) zero    = refl
comp-GET-REN∋ (Ξ , B) (keep e) (suc i) = comp-GET-REN∋ Ξ e i


--------------------------------------------------------------------------------


id-GETS : ∀ {X n} → (Ξ : Vec X n)
                  → GETS Ξ id ≡ Ξ
id-GETS ∙       = refl
id-GETS (Ξ , A) = (_, A) & id-GETS Ξ


comp-GETS : ∀ {X n n′ n″} → (Ξ : Vec X n″) (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′)
                          → GETS Ξ (e₁ ∘ e₂) ≡ GETS (GETS Ξ e₂) e₁
comp-GETS ∙       e₁        done      = refl
comp-GETS (Ξ , B) e₁        (drop e₂) = comp-GETS Ξ e₁ e₂
comp-GETS (Ξ , B) (drop e₁) (keep e₂) = comp-GETS Ξ e₁ e₂
comp-GETS (Ξ , A) (keep e₁) (keep e₂) = (_, A) & comp-GETS Ξ e₁ e₂


𝐆𝐄𝐓𝐒 : ∀ {X} → Presheaf (Opposite 𝐆𝐄𝐐) (Vec X) (flip GETS)
𝐆𝐄𝐓𝐒 = record
         { idℱ   = funext! id-GETS
         ; compℱ = \ e₁ e₂ → funext! (\ Ξ → comp-GETS Ξ e₂ e₁)
         }


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
  𝐎𝐏𝐄 : ∀ {X} → Category (Σ Nat (Vec X))
                          (\ { (n′ , Ξ′) (n , Ξ) →
                            Σ (n′ ≥ n) (\ e → Ξ′ ⊇⟨ e ⟩ Ξ )})
  𝐎𝐏𝐄 = record
          { id     = id , id⊇
          ; _∘_    = \ { (e₁ , η₁) (e₂ , η₂) → e₁ ∘ e₂ , η₁ ∘⊇ η₂ }
          ; lid∘   = \ { (e , η) → (e ,_) & lid∘⊇ η }
          ; rid∘   = \ { (e , η) → (e ,_) & rid∘⊇ η }
          ; assoc∘ = \ { (e₁ , η₁) (e₂ , η₂) (e₃ , η₃) →
                       ((e₁ ∘ e₂) ∘ e₃ ,_) & assoc∘⊇ η₁ η₂ η₃ }
          }


--------------------------------------------------------------------------------


{-# REWRITE id-REN∋ #-}
id-ren∋ : ∀ {X A n i} → {Ξ : Vec X n}
                      → (𝒾 : Ξ ∋⟨ i ⟩ A)
                      → ren∋ id⊇ 𝒾 ≡ 𝒾
id-ren∋ zero    = refl
id-ren∋ (suc 𝒾) = suc & id-ren∋ 𝒾


{-# REWRITE comp-REN∋ #-}
comp-ren∋ : ∀ {X A n n′ n″ e₁ e₂ i} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                    → (η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ) (η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′) (𝒾 : Ξ ∋⟨ i ⟩ A)
                                    → ren∋ (η₁ ∘⊇ η₂) 𝒾 ≡ (ren∋ η₂ ∘ ren∋ η₁) 𝒾
comp-ren∋ η₁        done      𝒾       = refl
comp-ren∋ η₁        (drop η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (drop η₁) (keep η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (keep η₁) (keep η₂) zero    = refl
comp-ren∋ (keep η₁) (keep η₂) (suc 𝒾) = suc & comp-ren∋ η₁ η₂ 𝒾


𝐫𝐞𝐧∋ : ∀ {X A} → Presheaf (𝐎𝐏𝐄 {X})
                           (\ { (n , Ξ) →
                             Σ (Fin n) (\ i → Ξ ∋⟨ i ⟩ A) })
                           (\ { (e , η) (i , 𝒾) → REN∋ e i , ren∋ η 𝒾 })
𝐫𝐞𝐧∋ = record
         { idℱ   = funext! (\ { (i , 𝒾) →
                     (REN∋ id i ,_) & id-ren∋ 𝒾 })
         ; compℱ = \ { (e₁ , η₁) (e₂ , η₂) →
                     funext! (\ { (i , 𝒾) →
                       (REN∋ (e₁ ∘ e₂) i ,_) & comp-ren∋ η₁ η₂ 𝒾 }) }
         }


--------------------------------------------------------------------------------
