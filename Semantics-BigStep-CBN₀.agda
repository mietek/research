---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-CBN₀ where

open import Semantics-BigStep
open CBN₀ public
import Semantics-SmallStep-CBN as SS-CBN


---------------------------------------------------------------------------------------------------------------

v-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → V e′
v-⇓ lam           = lam
v-⇓ (applam r₁ r) = v-⇓ r

refl-⇓ : ∀ {n} {e : Tm n} → V e → e ⇓ e
refl-⇓ lam = lam


---------------------------------------------------------------------------------------------------------------

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e SS-CBN.⇒* e′
ss←bs lam           = ε
ss←bs (applam r₁ r) = SS-CBN.bs-applam (ss←bs r₁) (ss←bs r)

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e SS-CBN.⇒*⟨ i ⟩ e′ → V e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e SS-CBN.⇒ e′ → e′ SS-CBN.⇒*⟨ i ⟩ e″ → V e″ → e ⇓ e″
  bs←ss′ SS-CBN.applam    rs p″ = applam lam (bs←ss rs p″)
  bs←ss′ (SS-CBN.app₁ r₁) rs p″ with SS-CBN.rev-app₀-⇒* rs p″
  ... | _ , rs′ , rs″            = applam (bs←ss′ r₁ rs′ lam) (bs←ss rs″ p″)

ss↔bs : ∀ {n} {e : Tm n} {e′} → V e′ → e SS-CBN.⇒* e′ ↔ e ⇓ e′
ss↔bs p′ = (λ r → bs←ss r p′) , ss←bs


---------------------------------------------------------------------------------------------------------------
