{-# OPTIONS --rewriting #-}

module VecLemmas where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec


--------------------------------------------------------------------------------
{-
                      GET (GETS Ξ e) I ≡ (GET Ξ ∘ REN∋ e) I                     comp-GET-REN∋

                             GETS ξ id ≡ ξ                                      id-GETS
                      GETS ξ (η₁ ∘ η₂) ≡ GETS (GETS ξ η₂) η₁                    comp-GETS
                                                                                𝐆𝐄𝐓𝐒

                              id⊇ ∘⊇ η ≡ η                                      lid∘⊇
                              η ∘⊇ id⊇ ≡ η                                      rid∘⊇
                      (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)                       assoc∘⊇
                                                                                𝐎𝐏𝐄

                             ren∋ id 𝒾 ≡ 𝒾                                      id-ren∋
                      ren∋ (η₁ ∘ η₂) 𝒾 ≡ (ren∋ η₂ ∘ ren∋ η₁) 𝒾                  comp-ren∋
                                                                                𝐫𝐞𝐧∋
-}
--------------------------------------------------------------------------------


comp-GET-REN∋ : ∀ {X n n′} → (Ξ : Vec X n′) (e : n′ ≥ n) (I : Fin n)
                           → GET (GETS Ξ e) I ≡ (GET Ξ ∘ REN∋ e) I
comp-GET-REN∋ ∙       done     ()
comp-GET-REN∋ (Ξ , B) (drop e) I       = comp-GET-REN∋ Ξ e I
comp-GET-REN∋ (Ξ , A) (keep e) zero    = refl
comp-GET-REN∋ (Ξ , B) (keep e) (suc I) = comp-GET-REN∋ Ξ e I


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


𝐆𝐄𝐓𝐒 : ∀ {X} → Presheaf (Opposite 𝐆𝐄𝐐) (Vec X)
𝐆𝐄𝐓𝐒 = record
         { ℱ     = flip GETS
         ; idℱ   = funext! id-GETS
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
id-ren∋ : ∀ {X A n I} → {Ξ : Vec X n}
                      → (i : Ξ ∋⟨ I ⟩ A)
                      → ren∋ id⊇ i ≡ i
id-ren∋ zero    = refl
id-ren∋ (suc i) = suc & id-ren∋ i


{-# REWRITE comp-REN∋ #-}
comp-ren∋ : ∀ {X A n n′ n″ e₁ e₂ I} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                    → (η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ) (η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′) (i : Ξ ∋⟨ I ⟩ A)
                                    → ren∋ (η₁ ∘⊇ η₂) i ≡ (ren∋ η₂ ∘ ren∋ η₁) i
comp-ren∋ η₁        done      i       = refl
comp-ren∋ η₁        (drop η₂) i       = suc & comp-ren∋ η₁ η₂ i
comp-ren∋ (drop η₁) (keep η₂) i       = suc & comp-ren∋ η₁ η₂ i
comp-ren∋ (keep η₁) (keep η₂) zero    = refl
comp-ren∋ (keep η₁) (keep η₂) (suc i) = suc & comp-ren∋ η₁ η₂ i


𝐫𝐞𝐧∋ : ∀ {X A} → Presheaf (𝐎𝐏𝐄 {X})
                           (\ { (n , Ξ) →
                             Σ (Fin n) (\ I → Ξ ∋⟨ I ⟩ A) })
𝐫𝐞𝐧∋ = record
         { ℱ     = \ { (e , η) (I , i) → REN∋ e I , ren∋ η i }
         ; idℱ   = funext! (\ { (I , i) →
                     (REN∋ id I ,_) & id-ren∋ i })
         ; compℱ = \ { (e₁ , η₁) (e₂ , η₂) →
                     funext! (\ { (I , i) →
                       (REN∋ (e₁ ∘ e₂) I ,_) & comp-ren∋ η₁ η₂ i }) }
         }


--------------------------------------------------------------------------------


module _
  where
    open import List


    id-len-toList : ∀ {X n} → (Ξ : Vec X n)
                            → len (toList Ξ) ≡ n
    id-len-toList ∙       = refl
    id-len-toList (Ξ , A) = suc & id-len-toList Ξ


    {-# REWRITE id-len-toList #-}
    id-toFin-to∋ : ∀ {X n I A} → {Ξ : Vec X n}
                               → (i : Ξ ∋⟨ I ⟩ A)
                               → toFin (to∋ i) ≡ I
    id-toFin-to∋ zero    = refl
    id-toFin-to∋ (suc i) = suc & id-toFin-to∋ i


    id-toList-fromList : ∀ {X} → (Ξ : List X)
                               → toList (fromList Ξ) ≡ Ξ
    id-toList-fromList ∙       = refl
    id-toList-fromList (Ξ , A) = (_, A) & id-toList-fromList Ξ


    {-# REWRITE id-toList-fromList #-}
    id-to∋-from∋ : ∀ {X A} → {Ξ : List X}
                           → (i : Ξ ∋ A)
                           → to∋ (from∋ i) ≡ i
    id-to∋-from∋ zero    = refl
    id-to∋-from∋ (suc i) = suc & id-to∋-from∋ i


    id-fromList-toList : ∀ {X n} → (Ξ : Vec X n)
                                 → fromList (toList Ξ) ≡ Ξ
    id-fromList-toList ∙       = refl
    id-fromList-toList (Ξ , A) = (_, A) & id-fromList-toList Ξ


    {-# REWRITE id-toFin-to∋ #-}
    {-# REWRITE id-fromList-toList #-}
    id-from∋-to∋ : ∀ {X n I A} → {Ξ : Vec X n}
                               → (i : Ξ ∋⟨ I ⟩ A)
                               → from∋ (to∋ i) ≡ i
    id-from∋-to∋ zero    = refl
    id-from∋-to∋ (suc i) = suc & id-from∋-to∋ i


    -- NOTE: Needed in isomorphism modules

    {-# REWRITE id-to∋-from∋ #-}
    {-# REWRITE id-from∋-to∋ #-}


--------------------------------------------------------------------------------
