---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-CBV₀ where

open import Semantics-BigStep
open CBV₀ public
import Semantics-SmallStep-CBV₀ as SS-CBV₀


---------------------------------------------------------------------------------------------------------------

v-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → V e′
v-⇓ lam                = lam
v-⇓ (applam r r₁ x r₂) = v-⇓ r₂

refl-⇓ : ∀ {n} {e : Tm n} → V e → e ⇓ e
refl-⇓ lam = lam


---------------------------------------------------------------------------------------------------------------

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e SS-CBV₀.⇒* e′
ss←bs lam                 = ε
ss←bs (applam r₁ r₂ p₂ r) = SS-CBV₀.bs-applam (ss←bs r₁) (ss←bs r₂) p₂ (ss←bs r)

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e SS-CBV₀.⇒*⟨ i ⟩ e′ → V e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e SS-CBV₀.⇒ e′ → e′ SS-CBV₀.⇒*⟨ i ⟩ e″ → V e″ → e ⇓ e″
  bs←ss′ (SS-CBV₀.app₁ r₁)    rs p″ with SS-CBV₀.rev-app-⇒* rs p″
  ... | _ , rs₁ , rs₂ , p₂′ , rs′    = applam (bs←ss′ r₁ rs₁ lam)
                                              (bs←ss rs₂ p₂′) p₂′
                                              (bs←ss rs′ p″)
  bs←ss′ (SS-CBV₀.app₂ p₁ r₂) rs p″ with SS-CBV₀.rev-app-⇒* rs p″
  ... | _ , rs₁ , rs₂ , p₂′ , rs′    = applam (bs←ss rs₁ lam)
                                              (bs←ss′ r₂ rs₂ p₂′) p₂′
                                              (bs←ss rs′ p″)
  bs←ss′ (SS-CBV₀.applam p₂)  rs p″ = applam lam (refl-⇓ p₂) p₂ (bs←ss rs p″)

ss↔bs : ∀ {n} {e : Tm n} {e′} → V e′ → e SS-CBV₀.⇒* e′ ↔ e ⇓ e′
ss↔bs p′ = (λ r → bs←ss r p′) , ss←bs


---------------------------------------------------------------------------------------------------------------
