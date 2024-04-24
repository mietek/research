module A201801.LPTTAsserts where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.S4TTTerms
open import A201801.S4TTTermsLemmas
open import A201801.LPTTTypes
open import A201801.LPTTTypesLemmas


--------------------------------------------------------------------------------


record Assert (d : Nat) : Set
  where
    constructor ⟪⊫_⦂_⟫
    field
      M : Term d zero
      A : Type d


data Asserts : Nat → Set
  where
    ∙ : Asserts zero

    _,_ : ∀ {d} → Asserts d → Assert d
                → Asserts (suc d)


--------------------------------------------------------------------------------


infix 4 _⊇◆⟨_⟩_
data _⊇◆⟨_⟩_ : ∀ {d d′} → Asserts d′ → d′ ≥ d → Asserts d → Set
  where
    done : ∙ ⊇◆⟨ done ⟩ ∙

    drop : ∀ {d d′ e M A} → {Δ : Asserts d} {Δ′ : Asserts d′}
                          → Δ′ ⊇◆⟨ e ⟩ Δ
                          → Δ′ , ⟪⊫ M ⦂ A ⟫ ⊇◆⟨ drop e ⟩ Δ

    keep : ∀ {d d′ e M M′ A A′} → {Δ : Asserts d} {Δ′ : Asserts d′}
                                   {{p : MREN e M ≡ M′}} {{q : TMREN e A ≡ A′}}
                                → Δ′ ⊇◆⟨ e ⟩ Δ
                                → Δ′ , ⟪⊫ M′ ⦂ A′ ⟫ ⊇◆⟨ keep e ⟩ Δ , ⟪⊫ M ⦂ A ⟫


id⊇◆ : ∀ {d} → {Δ : Asserts d}
             → Δ ⊇◆⟨ id ⟩ Δ
id⊇◆ {Δ = ∙}               = done
id⊇◆ {Δ = Δ , ⟪⊫ M ⦂ A ⟫} = keep {{id-MREN M}} {{id-TMREN A}} id⊇◆


_∘⊇◆_ : ∀ {d d′ d″ e₁ e₂} → {Δ : Asserts d} {Δ′ : Asserts d′} {Δ″ : Asserts d″}
                          → Δ′ ⊇◆⟨ e₁ ⟩ Δ → Δ″ ⊇◆⟨ e₂ ⟩ Δ′
                          → Δ″ ⊇◆⟨ e₁ ∘ e₂ ⟩ Δ
η₁      ∘⊇◆ done    = η₁
η₁      ∘⊇◆ drop η₂ = drop (η₁ ∘⊇◆ η₂)
drop η₁ ∘⊇◆ keep η₂ = drop (η₁ ∘⊇◆ η₂)
keep {e = e₁} {M = M} {A = A} {{refl}} {{refl}} η₁ ∘⊇◆ keep {e = e₂} {{refl}} {{refl}} η₂
  = keep {{comp-MREN e₁ e₂ M}} {{comp-TMREN e₁ e₂ A}} (η₁ ∘⊇◆ η₂)


--------------------------------------------------------------------------------


infix 3 _∋◆⟨_⟩_
data _∋◆⟨_⟩_ : ∀ {d} → Asserts d → Fin d → Assert d → Set
  where
    zero : ∀ {d M M′ A A′} → {Δ : Asserts d} {{p : MWK M ≡ M′}} {{q : TMWK A ≡ A′}}
                           → Δ , ⟪⊫ M ⦂ A ⟫ ∋◆⟨ zero ⟩ ⟪⊫ M′ ⦂ A′ ⟫

    suc : ∀ {d I M M′ N A A′ B} → {Δ : Asserts d} {{p : MWK M ≡ M′}} {{q : TMWK A ≡ A′}}
                                → Δ ∋◆⟨ I ⟩ ⟪⊫ M ⦂ A ⟫
                                → Δ , ⟪⊫ N ⦂ B ⟫ ∋◆⟨ suc I ⟩ ⟪⊫ M′ ⦂ A′ ⟫


ren∋◆ : ∀ {d d′ e I M A} → {Δ : Asserts d} {Δ′ : Asserts d′}
                         → Δ′ ⊇◆⟨ e ⟩ Δ → Δ ∋◆⟨ I ⟩ ⟪⊫ M ⦂ A ⟫
                         → Δ′ ∋◆⟨ REN∋ e I ⟩ ⟪⊫ MREN e M ⦂ TMREN e A ⟫
ren∋◆ {I = I} {M = M} {A} done i
  = coerce i ( (\ M′ A′ → ∙ ∋◆⟨ I ⟩ ⟪⊫ M′ ⦂ A′ ⟫)
                 & id-MREN M ⁻¹
                 ⊗ id-TMREN A ⁻¹
             )
ren∋◆ {M = M} {A} (drop {e = e} η) i
  = suc {{comp-MWK-MREN-drop e M ⁻¹}}
        {{comp-TMWK-TMREN-drop e A ⁻¹}}
        (ren∋◆ η i)
ren∋◆ (keep {e = e} {M = M} {A = A} {{refl}} {{refl}} η) (zero {{refl}} {{refl}})
  = zero {{comp-MWK-MREN-keep e M ⁻¹}}
         {{comp-TMWK-TMREN-keep e A ⁻¹}}
ren∋◆ (keep {e = e} {{refl}} {{refl}} η) (suc {M = M} {A = A} {{refl}} {{refl}} i)
  = suc {{comp-MWK-MREN-keep e M ⁻¹}}
        {{comp-TMWK-TMREN-keep e A ⁻¹}}
        (ren∋◆ η i)


--------------------------------------------------------------------------------
