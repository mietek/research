---------------------------------------------------------------------------------------------------------------
--
-- Mealy-like machines

module 0-1-2-Prelude-MealyLikeMachines where

open import 0-1-Prelude
open import 0-1-1-Prelude-StutteringColists using (Cocolist ; [] ; -∷_ ; _∷_)


---------------------------------------------------------------------------------------------------------------

mutual
  record Machine {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    coinductive
    field
      on   : A → Results A B
      done : Results A B

  infixr 4 _▻_
  data Results {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    _▻_  : B → Results A B → Results A B
    go   : Machine A B → Results A B
    stop : Results A B

open Machine public


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Bisimilarity?

private
  mutual
    infix 3 _≈ₘ_
    record _≈ₘ_ {a b} {A : Set a} {B : Set b} (m m′ : Machine A B) : Set (a ⊔ b) where
      coinductive
      field
        on   : ∀ (x : A) → m .on x ≈ᵣₛ m′ .on x
        done : m .done ≈ᵣₛ m′ .done

    infix 3 _≈ᵣₛ_
    data _≈ᵣₛ_ {a b} {A : Set a} {B : Set b} : Rel (Results A B) (a ⊔ b) where
      _▻_  : ∀ {rs rs′ y} → rs ≈ᵣₛ rs′ → y ▻ rs ≈ᵣₛ y ▻ rs′
      go   : ∀ {m m′} → m ≈ₘ m′ → go m ≈ᵣₛ go m′
      stop : stop ≈ᵣₛ stop

  open _≈ₘ_ public


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Compositionality?

private
  liftₘ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Machine A B
  liftₘ f .on x = f x ▻ go (liftₘ f)
  liftₘ f .done = stop

  idₘ : ∀ {a} {A : Set a} → Machine A A
  idₘ .on x = x ▻ go idₘ
  idₘ .done = stop

  _∘ₘ_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → Machine A B → Machine B C → Machine A C
  (m₁ ∘ₘ m₂) .on x = process₁ m₂ (m₁ .on x)
    where process₁ : Machine _ _ → Results _ _ → Results _ _
          process₁ m₂′ (y ▻ rs₁) = process₂ (m₂′ .on y)
            where process₂ : Results _ _ → Results _ _
                  process₂ (z ▻ rs₂) = z ▻ process₂ rs₂
                  process₂ (go m₂″)  = process₁ m₂″ rs₁
                  process₂ stop      = process₁ m₂′ rs₁
          process₁ m₂′ (go m₁′)  = go (m₁′ ∘ₘ m₂′)
          process₁ m₂′ stop      = stop
  (m₁ ∘ₘ m₂) .done = stop


---------------------------------------------------------------------------------------------------------------

runOnce : ∀ {a b} {A : Set a} {B : Set b} → Machine A B → List A → Maybe B
runOnce m []       = process (m .done)
  where process : Results _ _ → Maybe _
        process (y ▻ rs) = just y
        process (go m′)  = nothing
        process stop     = nothing
runOnce m (x ∷ xs) = process (m .on x)
  where process : Results _ _ → Maybe _
        process (y ▻ rs) = just y
        process (go m′)  = runOnce m′ xs
        process stop     = nothing

run : ∀ {a b} {A : Set a} {B : Set b} → Machine A B → List A → List B
run m []       = process (m .done)
  where process : Results _ _ → List _
        process (y ▻ rs) = y ∷ process rs
        process (go m′)  = []
        process stop     = []
run m (x ∷ xs) = process (m .on x)
  where process : Results _ _ → List _
        process (y ▻ rs) = y ∷ process rs
        process (go m′)  = run m′ xs
        process stop     = []

cocorun : ∀ {a b i} {A : Set a} {B : Set b} → Machine A B → Cocolist A i → Cocolist B i
cocorun         m []       = process (m .done)
  where process : Results _ _ → Cocolist _ _
        process (y ▻ rs) = y ∷ λ where .force → process rs
        process (go m′)  = []
        process stop     = []
cocorun         m (-∷ xs)  = -∷ λ where .force → cocorun m (xs .force)
cocorun {i = i} m (x ∷ xs) = process (m .on x)
  where process : Results _ _ → Cocolist _ i
        process (y ▻ rs) = y ∷ λ where .force → process rs
        process (go m′)  = -∷ λ where .force → cocorun m′ (xs .force)
        process stop     = []


---------------------------------------------------------------------------------------------------------------
