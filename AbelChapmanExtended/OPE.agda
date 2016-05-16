module AbelChapmanExtended.OPE where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import AbelChapmanExtended.Syntax




data _⊇_ : (Γ Γ′ : Cx) → Set where
  base :                          ∅        ⊇ ∅
  weak : ∀ {Γ Γ′ a} → Γ′ ⊇ Γ → (Γ′ , a) ⊇ Γ
  lift : ∀ {Γ Γ′ a} → Γ′ ⊇ Γ → (Γ′ , a) ⊇ (Γ , a)


id : ∀ {Γ} → Γ ⊇ Γ
id {∅}     = base
id {Γ , a} = lift (id {Γ})

_•_ : ∀ {Γ Γ′ Γ″} → Γ″ ⊇ Γ′ → Γ′ ⊇ Γ → Γ″ ⊇ Γ
base    • η      = η
weak η′ • η      = weak (η′ • η)
lift η′ • weak η = weak (η′ • η)
lift η′ • lift η = lift (η′ • η)


η•id : ∀ {Γ Γ′} (η : Γ′ ⊇ Γ) → η • id ≡ η
η•id base     = refl
η•id (weak η) = cong weak (η•id η)
η•id (lift η) = cong lift (η•id η)

id•η : ∀ {Γ Γ′} (η : Γ′ ⊇ Γ) → id • η ≡ η
id•η base     = refl
id•η (weak η) = cong weak (id•η η)
id•η (lift η) = cong lift (id•η η)

•assoc : ∀ {Γ‴ Γ″ Γ′ Γ} (η″ : Γ‴ ⊇ Γ″) (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) →
         (η″ • η′) • η ≡ η″ • (η′ • η)
•assoc base      η′        η        = refl
•assoc (weak η″) η′        η        = cong weak (•assoc η″ η′ η)
•assoc (lift η″) (weak η′) η        = cong weak (•assoc η″ η′ η)
•assoc (lift η″) (lift η′) (weak η) = cong weak (•assoc η″ η′ η)
•assoc (lift η″) (lift η′) (lift η) = cong lift (•assoc η″ η′ η)




-- module NonStandardLibrary where
--   open import Categories.Category using (Category)
--   open import Function using (flip)
--   open import Relation.Binary.PropositionalEquality using (sym ; cong₂ ; isEquivalence)

--   OPE : Category _ _ _
--   OPE = record
--     { Obj       = Cx
--     ; _⇒_      = _⊇_
--     ; _≡_       = _≡_
--     ; _∘_       = flip _•_
--     ; id        = id
--     ; assoc     = λ {_} {_} {_} {_} {η″} {η′} {η} → sym (•assoc η″ η′ η)
--     ; identityˡ = λ {_} {_} {η} → η•id η
--     ; identityʳ = λ {_} {_} {η} → id•η η
--     ; equiv     = isEquivalence
--     ; ∘-resp-≡  = cong₂ (flip _•_)
--     }
