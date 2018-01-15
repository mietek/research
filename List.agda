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
map f ∙       = ∙
map f (Ξ , A) = map f Ξ , f A


--------------------------------------------------------------------------------


GET : ∀ {X n} → (Ξ : List X) {{_ : len Ξ ≡ n}} → Fin n
              → X
GET ∙       {{refl}} ()
GET (Ξ , A) {{refl}} zero    = A
GET (Ξ , B) {{refl}} (suc I) = GET Ξ I


GETS : ∀ {X n n′} → (Ξ : List X) {{_ : len Ξ ≡ n′}} → n′ ≥ n
                  → List X
GETS ∙       {{refl}} done     = ∙
GETS (Ξ , B) {{refl}} (drop e) = GETS Ξ e
GETS (Ξ , A) {{refl}} (keep e) = GETS Ξ e , A


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


map⊇ : ∀ {X Y} → {Ξ Ξ′ : List X} {f : X → Y}
               → Ξ′ ⊇ Ξ
               → map f Ξ′ ⊇ map f Ξ
map⊇ done     = done
map⊇ (drop η) = drop (map⊇ η)
map⊇ (keep η) = keep (map⊇ η)


--------------------------------------------------------------------------------


infix 4 _∋_
data _∋_ {X} : List X → X → Set
  where
    zero : ∀ {A Ξ} → Ξ , A ∋ A

    suc : ∀ {A B Ξ} → Ξ ∋ A
                    → Ξ , B ∋ A


map∋ : ∀ {X Y A} → {Ξ : List X} {f : X → Y}
                 → Ξ ∋ A
                 → map f Ξ ∋ f A
map∋ zero    = zero
map∋ (suc 𝒾) = suc (map∋ 𝒾)


ren∋ : ∀ {X A} → {Ξ Ξ′ : List X}
               → Ξ′ ⊇ Ξ → Ξ ∋ A
               → Ξ′ ∋ A
ren∋ done     𝒾       = 𝒾
ren∋ (drop η) 𝒾       = suc (ren∋ η 𝒾)
ren∋ (keep η) zero    = zero
ren∋ (keep η) (suc 𝒾) = suc (ren∋ η 𝒾)


--------------------------------------------------------------------------------



module List²
  where
    List² : Set → Set → Set
    List² X Y = List X × List Y


    infix 5 _⨾_
    pattern _⨾_ Δ Γ = _,_ Δ Γ


    infix 4 _⊇²_
    _⊇²_ : ∀ {X Y} → List² X Y → List² X Y → Set
    Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ = Δ′ ⊇ Δ × Γ′ ⊇ Γ


    drop₁ : ∀ {X Y A} → {Δ Δ′ : List X} {Γ Γ′ : List Y}
                      → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ
                      → Δ′ , A ⨾ Γ′ ⊇² Δ ⨾ Γ
    drop₁ η = drop (proj₁ η) , proj₂ η


    drop₂ : ∀ {X Y A} → {Δ Δ′ : List X} {Γ Γ′ : List Y}
                      → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ
                      → Δ′ ⨾ Γ′ , A ⊇² Δ ⨾ Γ
    drop₂ η = proj₁ η , drop (proj₂ η)


--------------------------------------------------------------------------------
