---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-CBN-V where

open import Semantics-BigStep
open CBN-V public
open import Semantics-SmallStep-CBN
import Semantics-BigStep-CBN as BS-CBN


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN-V goes to V

v-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → V e′
v-⇓ lam           = lam
v-⇓ (applam r₁ r) = v-⇓ r


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN-V is reflexive

refl-⇓ : ∀ {n} {e : Tm n} → V e → e ⇓ e
refl-⇓ lam = lam


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN-V implies SS-CBN

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
ss←bs lam           = ε
ss←bs (applam r₁ r) = BS-CBN.bs-applam (ss←bs r₁) (ss←bs r)


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBN to V implies BS-CBN-V

rev-app₁-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
               app e₁ e₂ ⇒*⟨ i ⟩ e′ → V e′ →
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ lam e₁′ × e₁′ [ e₂ ] ⇒*⟨ i ⟩ e′)
rev-app₁-⇒* ε              ()
rev-app₁-⇒* (applam ◅ rs)  p′ = _ , ε , rs
rev-app₁-⇒* (app₁ r₁ ◅ rs) p′ with rev-app₁-⇒* rs p′
... | _ , rs₁ , rs′            = _ , r₁ ◅ rs₁ , rs′

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → V e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → V e″ → e ⇓ e″
  bs←ss′ applam    rs p″ = applam lam (bs←ss rs p″)
  bs←ss′ (app₁ r₁) rs p″ with rev-app₁-⇒* rs p″
  ... | _ , rs′ , rs″     = applam (bs←ss′ r₁ rs′ lam) (bs←ss rs″ p″)


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN-V and SS-CBN to V coincide

bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × V e′)
bs↔ss = (λ r → ss←bs r , v-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
