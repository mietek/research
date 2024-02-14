----------------------------------------------------------------------------------------------------

-- order-preserving embeddings

module OPE {𝓍} {X : Set 𝓍} where

open import DBI public


----------------------------------------------------------------------------------------------------

infix 4 _⊑_
data _⊑_ : List X → List X → Set 𝓍 where
  stop⊑ : [] ⊑ []
  wk⊑   : ∀ {B Γ Γ′} (e : Γ ⊑ Γ′) → Γ ⊑ B ∷ Γ′
  lift⊑ : ∀ {B Γ Γ′} (e : Γ ⊑ Γ′) → B ∷ Γ ⊑ B ∷ Γ′

id⊑ refl⊑ : ∀ {Γ} → Γ ⊑ Γ
id⊑ {[]}    = stop⊑
id⊑ {A ∷ Γ} = lift⊑ id⊑
refl⊑ = id⊑

-- Kovacs: flip _∘ₑ_
_∘⊑_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊑ Γ″ → Γ ⊑ Γ′ → Γ ⊑ Γ″
stop⊑    ∘⊑ e       = e
wk⊑ e′   ∘⊑ e       = wk⊑ (e′ ∘⊑ e)
lift⊑ e′ ∘⊑ wk⊑ e   = wk⊑ (e′ ∘⊑ e)
lift⊑ e′ ∘⊑ lift⊑ e = lift⊑ (e′ ∘⊑ e)

trans⊑ _○_ : ∀ {Γ Γ′ Γ″} → Γ ⊑ Γ′ → Γ′ ⊑ Γ″ → Γ ⊑ Γ″
trans⊑ = flip _∘⊑_
_○_ = trans⊑

lid⊑ : ∀ {Γ Γ′} (e : Γ ⊑ Γ′) → id⊑ ∘⊑ e ≡ e
lid⊑ stop⊑     = refl
lid⊑ (wk⊑ e)   = wk⊑ & lid⊑ e
lid⊑ (lift⊑ e) = lift⊑ & lid⊑ e

rid⊑ : ∀ {Γ Γ′} (e : Γ ⊑ Γ′) → e ∘⊑ id⊑ ≡ e
rid⊑ stop⊑     = refl
rid⊑ (wk⊑ e)   = wk⊑ & rid⊑ e
rid⊑ (lift⊑ e) = lift⊑ & rid⊑ e

ass⊑ : ∀ {Γ Γ′ Γ″ Γ‴} (e″ : Γ″ ⊑ Γ‴) (e′ : Γ′ ⊑ Γ″) (e : Γ ⊑ Γ′) →
       e″ ∘⊑ (e′ ∘⊑ e) ≡ (e″ ∘⊑ e′) ∘⊑ e
ass⊑ stop⊑      e′         e         = refl
ass⊑ (wk⊑ e″)   e′         e         = wk⊑ & ass⊑ e″ e′ e
ass⊑ (lift⊑ e″) (wk⊑ e′)   e         = wk⊑ & ass⊑ e″ e′ e
ass⊑ (lift⊑ e″) (lift⊑ e′) (wk⊑ e)   = wk⊑ & ass⊑ e″ e′ e
ass⊑ (lift⊑ e″) (lift⊑ e′) (lift⊑ e) = lift⊑ & ass⊑ e″ e′ e


----------------------------------------------------------------------------------------------------

ren∋ : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ∋ A → Γ′ ∋ A
ren∋ stop⊑     i       = i
ren∋ (wk⊑ e)   i       = suc (ren∋ e i)
ren∋ (lift⊑ e) zero    = zero
ren∋ (lift⊑ e) (suc i) = suc (ren∋ e i)

wk∋ : ∀ {B Γ A} → Γ ∋ A → B ∷ Γ ∋ A
wk∋ i = ren∋ (wk⊑ id⊑) i

idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊑ i ≡ i
idren∋ zero    = refl
idren∋ (suc i) = suc & idren∋ i

compren∋ : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊑ Γ″) (e : Γ ⊑ Γ′) (i : Γ ∋ A) →
           ren∋ (e′ ∘⊑ e) i ≡ (ren∋ e′ ∘ ren∋ e) i
compren∋ stop⊑      e         i       = refl
compren∋ (wk⊑ e′)   e         i       = suc & compren∋ e′ e i
compren∋ (lift⊑ e′) (wk⊑ e)   i       = suc & compren∋ e′ e i
compren∋ (lift⊑ e′) (lift⊑ e) zero    = refl
compren∋ (lift⊑ e′) (lift⊑ e) (suc i) = suc & compren∋ e′ e i


----------------------------------------------------------------------------------------------------

-- TODO: delete?

injren∋ : ∀ {Γ Γ′ A} {e : Γ ⊑ Γ′} {i i′ : Γ ∋ A} → ren∋ e i ≡ ren∋ e i′ → i ≡ i′
injren∋ {e = stop⊑}   {i}     {i′}     eq   = eq
injren∋ {e = wk⊑ e}   {i}     {i′}     eq   = injren∋ (injsuc eq)
injren∋ {e = lift⊑ e} {zero}  {zero}   refl = refl
injren∋ {e = lift⊑ e} {suc i} {suc i′} eq   = suc & (injren∋ (injsuc eq))

unren∋ : ∀ {Γ Γ′ A} (e : Γ ⊑ Γ′) (i′ : Γ′ ∋ A) → Dec (Σ (Γ ∋ A) λ i → i′ ≡ ren∋ e i)
unren∋ stop⊑     i′       = yes (i′ , refl)
unren∋ (wk⊑ e)   zero     = no λ ()
unren∋ (wk⊑ e)   (suc i′) with unren∋ e i′
... | no ¬p                 = no λ { (i , refl) → (i , refl) ↯ ¬p }
... | yes (i , refl)        = yes (i , refl)
unren∋ (lift⊑ e) zero     = yes (zero , refl)
unren∋ (lift⊑ e) (suc i′) with unren∋ e i′
... | no ¬p                 = no λ { (suc i , refl) → (i , refl) ↯ ¬p }
... | yes (i , refl)        = yes (suc i , refl)


----------------------------------------------------------------------------------------------------
