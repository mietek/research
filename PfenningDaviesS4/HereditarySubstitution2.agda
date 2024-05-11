{-# OPTIONS --allow-unsolved-metas #-}

module PfenningDaviesS4.HereditarySubstitution2 where

open import PfenningDaviesS4.Syntax public

open import Data.Product using (_×_) renaming (_,_ to _∙_)
open import Function using (_∘_)


-- Normal terms, neutral terms, and spines.

mutual
  data No (Γ Δ : Cx Ty) : Ty → Set where
    lamₙ  : ∀ {A B} → No (Γ , A) Δ B → No Γ Δ (A ⊃ B)
    pairₙ : ∀ {A B} → No Γ Δ A → No Γ Δ B → No Γ Δ (A ∧ B)
    unitₙ : No Γ Δ ⊤
    boxₙ  : ∀ {A} → No ∅ Δ A → No Γ Δ (□ A)
    neₙ   : Ne Γ Δ ι → No Γ Δ ι
    ne∅ₙ  : Ne∅ Δ ι → No Γ Δ ι

  data Ne (Γ Δ : Cx Ty) : Ty → Set where
    spₙ : ∀ {A B} → Sp Γ Δ (B ∙ A) → A ∈ Γ → Ne Γ Δ B

  data Ne∅ (Δ : Cx Ty) : Ty → Set where
    ⋆spₙ : ∀ {A B} → Sp ∅ Δ (B ∙ A) → A ∈ Δ → Ne∅ Δ B

  data Sp (Γ Δ : Cx Ty) : Ty × Ty → Set where
    ∅ₛ     : ∀ {A} → Sp Γ Δ (A ∙ A)
    appₛ   : ∀ {A B K} → Sp Γ Δ (K ∙ B) → No Γ Δ A → Sp Γ Δ (K ∙ (A ⊃ B))
    fstₛ   : ∀ {A B K} → Sp Γ Δ (K ∙ A) → Sp Γ Δ (K ∙ (A ∧ B))
    sndₛ   : ∀ {A B K} → Sp Γ Δ (K ∙ B) → Sp Γ Δ (K ∙ (A ∧ B))
    unboxₛ : ∀ {A C K} → Sp Γ Δ (K ∙ C) → No Γ (Δ , A) C → Sp Γ Δ (K ∙ (□ A))


-- Weakening.

mutual
  ren-no : ∀ {Γ Γ′ Δ} → Renᵢ Γ Γ′ → Ren (flip No Δ) Γ Γ′
  ren-no ρ (lamₙ t)    = lamₙ (ren-no (wk-renᵢ ρ) t)
  ren-no ρ (pairₙ t u) = pairₙ (ren-no ρ t) (ren-no ρ u)
  ren-no ρ unitₙ       = unitₙ
  ren-no ρ (boxₙ t)    = boxₙ t
  ren-no ρ (neₙ t)     = neₙ (ren-ne ρ t)
  ren-no ρ (ne∅ₙ t)    = ne∅ₙ t

  ren-ne : ∀ {Γ Γ′ Δ} → Renᵢ Γ Γ′ → Ren (flip Ne Δ) Γ Γ′
  ren-ne ρ (spₙ ss i) = spₙ (ren-sp ρ ss) (ρ i)

  ren-sp : ∀ {Γ Γ′ Δ} → Renᵢ Γ Γ′ → Ren (flip Sp Δ) Γ Γ′
  ren-sp ρ ∅ₛ            = ∅ₛ
  ren-sp ρ (appₛ ss t)   = appₛ (ren-sp ρ ss) (ren-no ρ t)
  ren-sp ρ (fstₛ ss)     = fstₛ (ren-sp ρ ss)
  ren-sp ρ (sndₛ ss)     = sndₛ (ren-sp ρ ss)
  ren-sp ρ (unboxₛ ss t) = unboxₛ (ren-sp ρ ss) (ren-no ρ t)

wk-no : ∀ {A Γ Δ} → Ren (flip No Δ) Γ (Γ , A)
wk-no = ren-no pop

wk-ne : ∀ {A Γ Δ} → Ren (flip Ne Δ) Γ (Γ , A)
wk-ne = ren-ne pop

wk-no∅ : ∀ {Γ Δ} → Ren (flip No Δ) ∅ Γ
wk-no∅ = ren-no (λ ())


-- Modal weakening.

mutual
  ⋆ren-no : ∀ {Γ Δ Δ′} → Renᵢ Δ Δ′ → Ren (No Γ) Δ Δ′
  ⋆ren-no ρ (lamₙ t)    = lamₙ (⋆ren-no ρ t)
  ⋆ren-no ρ (pairₙ t u) = pairₙ (⋆ren-no ρ t) (⋆ren-no ρ u)
  ⋆ren-no ρ unitₙ       = unitₙ
  ⋆ren-no ρ (boxₙ t)    = boxₙ (⋆ren-no ρ t)
  ⋆ren-no ρ (neₙ t)     = neₙ (⋆ren-ne ρ t)
  ⋆ren-no ρ (ne∅ₙ t)    = ne∅ₙ (⋆ren-ne∅ ρ t)

  ⋆ren-ne : ∀ {Γ Δ Δ′} → Renᵢ Δ Δ′ → Ren (Ne Γ) Δ Δ′
  ⋆ren-ne ρ (spₙ ss i) = spₙ (⋆ren-sp ρ ss) i

  ⋆ren-ne∅ : ∀ {Δ Δ′} → Renᵢ Δ Δ′ → Ren Ne∅ Δ Δ′
  ⋆ren-ne∅ ρ (⋆spₙ ss i) = ⋆spₙ (⋆ren-sp ρ ss) (ρ i)

  ⋆ren-sp : ∀ {Γ Δ Δ′} → Renᵢ Δ Δ′ → Ren (Sp Γ) Δ Δ′
  ⋆ren-sp ρ ∅ₛ            = ∅ₛ
  ⋆ren-sp ρ (appₛ ss t)   = appₛ (⋆ren-sp ρ ss) (⋆ren-no ρ t)
  ⋆ren-sp ρ (fstₛ ss)     = fstₛ (⋆ren-sp ρ ss)
  ⋆ren-sp ρ (sndₛ ss)     = sndₛ (⋆ren-sp ρ ss)
  ⋆ren-sp ρ (unboxₛ ss t) = unboxₛ (⋆ren-sp ρ ss) (⋆ren-no (wk-renᵢ ρ) t)

⋆wk-no : ∀ {A Γ Δ} → Ren (No Γ) Δ (Δ , A)
⋆wk-no = ⋆ren-no pop

⋆wk-ne : ∀ {A Γ Δ} → Ren (Ne Γ) Δ (Δ , A)
⋆wk-ne = ⋆ren-ne pop

⋆wk-no∅ : ∀ {A Δ} → Ren (No ∅) Δ (Δ , A)
⋆wk-no∅ = wk-no∅ ∘ ⋆wk-no


-- Hereditary substitution.

-- TODO: unfinished
mutual
  [_≔_]ₙ_ : ∀ {A Γ Δ} → (i : A ∈ Γ) → No (Γ -ᵢ i) Δ A → Sub (flip No Δ) Γ (Γ -ᵢ i)
  [ i ≔ ν ]ₙ (lamₙ t)           = lamₙ ([ pop i ≔ wk-no ν ]ₙ t)
  [ i ≔ ν ]ₙ (pairₙ t u)        = pairₙ ([ i ≔ ν ]ₙ t) ([ i ≔ ν ]ₙ u)
  [ i ≔ ν ]ₙ unitₙ              = unitₙ
  [ i ≔ ν ]ₙ (boxₙ t)           = boxₙ t
  [ i ≔ ν ]ₙ (neₙ (spₙ ss j))   with i ≟ᵢ j
  [ i ≔ ν ]ₙ (neₙ (spₙ ss .i))  | same   = reduce ([ i ≔ ν ]ₛ ss) ν
  [ i ≔ ν ]ₙ (neₙ (spₙ ss ._))  | diff j = neₙ (spₙ ([ i ≔ ν ]ₛ ss) j)
  [ i ≔ ν ]ₙ (ne∅ₙ (⋆spₙ ss j)) = ne∅ₙ (⋆spₙ ss j)

  [_≔_]ₛ_ : ∀ {A Γ Δ} → (i : A ∈ Γ) → No (Γ -ᵢ i) Δ A → Sub (flip Sp Δ) Γ (Γ -ᵢ i)
  [ i ≔ ν ]ₛ ∅ₛ            = ∅ₛ
  [ i ≔ ν ]ₛ (appₛ ss t)   = appₛ ([ i ≔ ν ]ₛ ss) ([ i ≔ ν ]ₙ t)
  [ i ≔ ν ]ₛ (fstₛ ss)     = fstₛ ([ i ≔ ν ]ₛ ss)
  [ i ≔ ν ]ₛ (sndₛ ss)     = sndₛ ([ i ≔ ν ]ₛ ss)
  [ i ≔ ν ]ₛ (unboxₛ ss t) = unboxₛ ([ i ≔ ν ]ₛ ss) ([ i ≔ ⋆wk-no ν ]ₙ t)

  ⋆[_≔_]ₙ_ : ∀ {A Γ Δ} → (i : A ∈ Δ) → No ∅ (Δ -ᵢ i) A → Sub (No Γ) Δ (Δ -ᵢ i)
  ⋆[ i ≔ ν ]ₙ (lamₙ t)            = lamₙ (⋆[ i ≔ ν ]ₙ t)
  ⋆[ i ≔ ν ]ₙ (pairₙ t u)         = pairₙ (⋆[ i ≔ ν ]ₙ t) (⋆[ i ≔ ν ]ₙ u)
  ⋆[ i ≔ ν ]ₙ unitₙ               = unitₙ
  ⋆[ i ≔ ν ]ₙ (boxₙ t)            = boxₙ (⋆[ i ≔ ν ]ₙ t)
  ⋆[ i ≔ ν ]ₙ (neₙ (spₙ ss j))    = neₙ (spₙ (⋆[ i ≔ ν ]ₛ ss) j)
  ⋆[ i ≔ ν ]ₙ (ne∅ₙ (⋆spₙ ss j))  with i ≟ᵢ j
  ⋆[ i ≔ ν ]ₙ (ne∅ₙ (⋆spₙ ss .i)) | same   = wk-no∅ (reduce (⋆[ i ≔ ν ]ₛ ss) ν)
  ⋆[ i ≔ ν ]ₙ (ne∅ₙ (⋆spₙ ss ._)) | diff j = ne∅ₙ (⋆spₙ (⋆[ i ≔ ν ]ₛ ss) j)

  ⋆[_≔_]ₛ_ : ∀ {A Γ Δ} → (i : A ∈ Δ) → No ∅ (Δ -ᵢ i) A → Sub (Sp Γ) Δ (Δ -ᵢ i)
  ⋆[ i ≔ ν ]ₛ ∅ₛ            = ∅ₛ
  ⋆[ i ≔ ν ]ₛ (appₛ ss t)   = appₛ (⋆[ i ≔ ν ]ₛ ss) (⋆[ i ≔ ν ]ₙ t)
  ⋆[ i ≔ ν ]ₛ (fstₛ ss)     = fstₛ (⋆[ i ≔ ν ]ₛ ss)
  ⋆[ i ≔ ν ]ₛ (sndₛ ss)     = sndₛ (⋆[ i ≔ ν ]ₛ ss)
  ⋆[ i ≔ ν ]ₛ (unboxₛ ss t) = unboxₛ (⋆[ i ≔ ν ]ₛ ss) {!!} -- (⋆wk-no∅ (reduce (⋆[ i ≔ ν ]ₛ {!ss!}) ν))
  -- (⋆[ pop i ≔ ⋆wk-no ν ]ₙ t)

  reduce : ∀ {A B Γ Δ} → Sp Γ Δ (B ∙ A) → No Γ Δ A → No Γ Δ B
  reduce ∅ₛ            t           = t
  reduce (appₛ ss u)   (lamₙ t)    = reduce ss ([ top ≔ u ]ₙ t)
  reduce (fstₛ ss)     (pairₙ t u) = reduce ss t
  reduce (sndₛ ss)     (pairₙ t u) = reduce ss u
  reduce (unboxₛ ss u) (boxₙ t)    = {!!} -- reduce ss (⋆[ top ≔ t ]ₙ u)
