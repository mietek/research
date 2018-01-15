module StdIPLSequentCalculus where

open import Prelude
open import List
open import AllList
open import StdIPL using (Prop ; BASE ; _⊃_)
-- open import StdIPLVerifications


--------------------------------------------------------------------------------


-- “A left” to correspond to “A ↑”, which is read as “A has a verification”

infix 7 _left
record Left : Set
  where
    constructor _left
    field
      A : Prop


-- “A right” to correspond to “A ↓”, which is read as “A may be used”

infix 7 _right
record Right : Set
  where
    constructor _right
    field
      A : Prop


--------------------------------------------------------------------------------


module With
  where
    infix 3 _⟹_
    data _⟹_ : List Left → Right → Set
      where
        vz : ∀ {A Γ} → Γ , A left ⟹ A right

        wk : ∀ {A C Γ} → Γ ⟹ C right
                       → Γ , A left ⟹ C right

        ct : ∀ {A C Γ} → Γ , A left , A left ⟹ C right
                       → Γ , A left ⟹ C right

        ex : ∀ {A B C Γ} → Γ , A left , B left ⟹ C right
                         → Γ , B left , A left ⟹ C right

        cut : ∀ {A C Γ} → Γ ⟹ A right → Γ , A left ⟹ C right
                        → Γ ⟹ C right

        lam : ∀ {A B Γ} → Γ , A left ⟹ B right
                        → Γ ⟹ A ⊃ B right

        app : ∀ {A B C Γ} → Γ , A ⊃ B left ⟹ A right → Γ , A ⊃ B left , B left ⟹ C right
                          → Γ , A ⊃ B left ⟹ C right


module Without
  where
    infix 3 _⟹_
    data _⟹_ : List Left → Right → Set
      where
        vz : ∀ {A Γ} → Γ , A left ⟹ A right

        wk : ∀ {A C Γ} → Γ ⟹ C right
                       → Γ , A left ⟹ C right

        ct : ∀ {A C Γ} → Γ , A left , A left ⟹ C right
                       → Γ , A left ⟹ C right

        ex : ∀ {A B C Γ} → Γ , A left , B left ⟹ C right
                         → Γ , B left , A left ⟹ C right

        lam : ∀ {A B Γ} → Γ , A left ⟹ B right
                        → Γ ⟹ A ⊃ B right

        app : ∀ {A B C Γ} → Γ , A ⊃ B left ⟹ A right → Γ , A ⊃ B left , B left ⟹ C right
                          → Γ , A ⊃ B left ⟹ C right


    cut : ∀ {A C Γ} → Γ ⟹ A right → Γ , A left ⟹ C right
                    → Γ ⟹ C right
    cut vz ℰ = ct ℰ
    cut 𝒟 vz = 𝒟
    cut (lam 𝒟) (app ℰ₁ ℰ₂) = {!cut (ex (wk 𝒟)) (ex (wk ℰ₂)) !}
    cut (wk 𝒟) ℰ = {!!}
    cut (ct 𝒟) ℰ = {!!}
    cut (ex 𝒟) ℰ = {!!}
    cut (lam 𝒟) ℰ = {!!}
    cut (app 𝒟₁ 𝒟₂) ℰ = {!!}


-- mutual
--   infix 3 _⊢ₙ_
--   data _⊢ₙ_ : List Use → Verification → Set
--     where
--       lam : ∀ {A B Γ} → Γ , A ↓ ⊢ₙ B ↑
--                       → Γ ⊢ₙ A ⊃ B ↑
--
--       use : ∀ {Γ} → Γ ⊢ᵣ BASE ↓
--                   → Γ ⊢ₙ BASE ↑
--
--   infix 3 _⊢ᵣ_
--   data _⊢ᵣ_ : List Use → Use → Set
--     where
--       var : ∀ {A Γ} → Γ ∋ A ↓
--                     → Γ ⊢ᵣ A ↓
--
--       app : ∀ {A B Γ} → Γ ⊢ᵣ A ⊃ B ↓ → Γ ⊢ₙ A ↑
--                       → Γ ⊢ᵣ B ↓


--------------------------------------------------------------------------------


-- v2l : Verification → Left
-- v2l (A ↑) = A left


-- l2v : Left → Verification
-- l2v (A left) = A ↑


-- u2r : Use → Right
-- u2r (A ↓) = A right


-- r2u : Right → Use
-- r2u (A right) = A ↓


-- --------------------------------------------------------------------------------


-- -- module G3₋
-- --   where
-- --     infix 3 _⋙_
-- --     data _⋙_ : List Prop → Prop → Set
-- --       where
-- --         vz : ∀ {A Γ} → Γ , A ⋙ A

-- --         ri : ∀ {A B Γ} → Γ , A ⋙ B
-- --                        → Γ ⋙ A ⊃ B

-- --         li : ∀ {A B C Γ} → Γ , A ⊃ B ⋙ A → Γ , A ⊃ B , B ⋙ C
-- --                          → Γ , A ⊃ B ⋙ C


-- --     postulate
-- --       ex : ∀ {A B C Γ} → Γ , A , B ⋙ C
-- --                        → Γ , B , A ⋙ C

-- --       ex₂ : ∀ {A B C D Γ} → Γ , A , B , C ⋙ D
-- --                           → Γ , C , A , B ⋙ D


-- --     wk : ∀ {A C Γ} → Γ ⋙ C
-- --                    → Γ , A ⋙ C
-- --     wk vz       = ex vz
-- --     wk (ri 𝒟)   = ri (ex (wk 𝒟))
-- --     wk (li 𝒟 ℰ) = ex (li (ex (wk 𝒟)) (ex₂ (wk ℰ)))


-- --     ct : ∀ {A C Γ} → Γ , A , A ⋙ C
-- --                    → Γ ⋙ C
-- --     ct vz       = {!!}
-- --     ct (ri 𝒟)   = {!!}
-- --     ct (li 𝒟 ℰ) = {!!}


-- -- --------------------------------------------------------------------------------


-- -- module G3
-- --   where
-- --     infix 3 _⋙_
-- --     data _⋙_ : List Prop → Prop → Set
-- --       where
-- --         vz : ∀ {A Γ} → Γ , A ⋙ A

-- --         ri : ∀ {A B Γ} → Γ , A ⋙ B
-- --                        → Γ ⋙ A ⊃ B

-- --         li : ∀ {A B C Γ} → Γ , A ⊃ B ⋙ A → Γ , A ⊃ B , B ⋙ C
-- --                          → Γ , A ⊃ B ⋙ C

-- --         cut : ∀ {A C Γ} → Γ ⋙ A → Γ , A ⋙ C
-- --                         → Γ ⋙ C


-- --     ex : ∀ {A B C Γ} → Γ , A , B ⋙ C
-- --                      → Γ , B , A ⋙ C
-- --     ex vz        = {!!}
-- --     ex (ri 𝒟)    = {!!}
-- --     ex (li 𝒟 ℰ)  = {!!}
-- --     ex (cut 𝒟 ℰ) = {!!}


-- --     wk : ∀ {A C Γ} → Γ ⋙ C
-- --                    → Γ , A ⋙ C
-- --     wk vz        = {!!}
-- --     wk (ri 𝒟)    = {!!}
-- --     wk (li 𝒟 ℰ)  = {!!}
-- --     wk (cut 𝒟 ℰ) = {!!}


-- --     ct : ∀ {A C Γ} → Γ , A , A ⋙ C
-- --                    → Γ ⋙ C
-- --     ct vz        = {!!}
-- --     ct (ri 𝒟)    = {!!}
-- --     ct (li 𝒟 ℰ)  = {!!}
-- --     ct (cut 𝒟 ℰ) = {!!}


-- -- --------------------------------------------------------------------------------


-- -- --------------------------------------------------------------------------------


-- -- --------------------------------------------------------------------------------
