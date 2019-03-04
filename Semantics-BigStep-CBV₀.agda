---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-CBV₀ where

open import Semantics-BigStep
open CBV₀ public
open import Semantics-SmallStep-CBV₀


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV₀ goes to V

v-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → V e′
v-⇓ lam                = lam
v-⇓ (applam r r₁ x r₂) = v-⇓ r₂


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV₀ is reflexive

refl-⇓ : ∀ {n} {e : Tm n} → V e → e ⇓ e
refl-⇓ lam = lam


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV₀ implies SS-CBV₀

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
            e₁ ⇒* lam e₁′ → e₂ ⇒* e₂′ → V e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
            app e₁ e₂ ⇒* e′
bs-applam rs₁ rs₂ p₂′ rs = app₁* rs₁ ◅◅ app₂* lam rs₂ ◅◅ applam* p₂′ ◅◅ rs

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
ss←bs lam                 = ε
ss←bs (applam r₁ r₂ p₂ r) = bs-applam (ss←bs r₁) (ss←bs r₂) p₂ (ss←bs r)


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV₀ to V implies BS-CBV₀

rev-app-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              app e₁ e₂ ⇒*⟨ i ⟩ e′ → V e′ →
              (∃² λ e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ lam e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × V e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′)
rev-app-⇒* ε                 ()
rev-app-⇒* (app₁ r₁ ◅ rs)    p′ with rev-app-⇒* rs p′
... | _ , rs₁ , rs₂ , p₂′ , rs′  = _ , r₁ ◅ rs₁ , rs₂ , p₂′ , rs′
rev-app-⇒* (app₂ p₁ r₂ ◅ rs) p′ with rev-app-⇒* rs p′
... | _ , rs₁ , rs₂ , p₂′ , rs′  = _ , rs₁ , r₂ ◅ rs₂ , p₂′ , rs′
rev-app-⇒* (applam p₂ ◅ rs)  p′ = _ , ε , ε , p₂ , rs

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → V e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → V e″ → e ⇓ e″
  bs←ss′ (app₁ r₁)    rs p″      with rev-app-⇒* rs p″
  ... | _ , rs₁ , rs₂ , p₂′ , rs′ = applam (bs←ss′ r₁ rs₁ lam)
                                           (bs←ss rs₂ p₂′) p₂′
                                           (bs←ss rs′ p″)
  bs←ss′ (app₂ p₁ r₂) rs p″      with rev-app-⇒* rs p″
  ... | _ , rs₁ , rs₂ , p₂′ , rs′ = applam (bs←ss rs₁ lam)
                                           (bs←ss′ r₂ rs₂ p₂′) p₂′
                                           (bs←ss rs′ p″)
  bs←ss′ (applam p₂)  rs p″      = applam lam (refl-⇓ p₂) p₂ (bs←ss rs p″)


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV₀ and SS-CBV₀ to V coincide

bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × V e′)
bs↔ss = (λ r → ss←bs r , v-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
