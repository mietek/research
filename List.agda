module List where

open import Prelude
open import Fin


--------------------------------------------------------------------------------


data List (X : Set) : Set
  where
    ∙   : List X
    _,_ : List X → X → List X


len : ∀ {X} → List X
            → Nat
len ∙       = zero
len (Ξ , A) = suc (len Ξ)


map : ∀ {X Y} → (X → Y) → List X
              → List Y
map F ∙       = ∙
map F (Ξ , A) = map F Ξ , F A


module GetList
  where
    get : ∀ {X n} → (Ξ : List X) {{_ : len Ξ ≡ n}} → Fin n
                  → X
    get ∙       {{refl}} ()
    get (Ξ , A) {{refl}} zero    = A
    get (Ξ , B) {{refl}} (suc i) = get Ξ i


    gets : ∀ {X n n′} → (Ξ : List X) {{_ : len Ξ ≡ n′}} → n′ ≥ n
                      → List X
    gets ∙       {{refl}} done     = ∙
    gets (Ξ , B) {{refl}} (drop e) = gets Ξ e
    gets (Ξ , A) {{refl}} (keep e) = gets Ξ e , A


--------------------------------------------------------------------------------


infix 4 _⊇_
data _⊇_ {X} : List X → List X → Set
  where
    done : ∙ ⊇ ∙

    drop : ∀ {A Ξ Ξ′} → Ξ′ ⊇ Ξ
                      → Ξ′ , A ⊇ Ξ

    keep : ∀ {A Ξ Ξ′} → Ξ′ ⊇ Ξ
                      → Ξ′ , A ⊇ Ξ , A


id⊇ : ∀ {X} → {Ξ : List X}
            → Ξ ⊇ Ξ
id⊇ {Ξ = ∙}     = done
id⊇ {Ξ = Ξ , A} = keep id⊇


_∘⊇_ : ∀ {X} → {Ξ Ξ′ Ξ″ : List X}
             → Ξ′ ⊇ Ξ → Ξ″ ⊇ Ξ′
             → Ξ″ ⊇ Ξ
η₁      ∘⊇ done    = η₁
η₁      ∘⊇ drop η₂ = drop (η₁ ∘⊇ η₂)
drop η₁ ∘⊇ keep η₂ = drop (η₁ ∘⊇ η₂)
keep η₁ ∘⊇ keep η₂ = keep (η₁ ∘⊇ η₂)


--------------------------------------------------------------------------------


infix 4 _∋_
data _∋_ {X} : List X → X → Set
  where
    zero : ∀ {A Ξ} → Ξ , A ∋ A

    suc : ∀ {A B Ξ} → Ξ ∋ A
                    → Ξ , B ∋ A


ren∋ : ∀ {X A} → {Ξ Ξ′ : List X}
               → Ξ′ ⊇ Ξ → Ξ ∋ A
               → Ξ′ ∋ A
ren∋ done     𝒾       = 𝒾
ren∋ (drop η) 𝒾       = suc (ren∋ η 𝒾)
ren∋ (keep η) zero    = zero
ren∋ (keep η) (suc 𝒾) = suc (ren∋ η 𝒾)


--------------------------------------------------------------------------------
