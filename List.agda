module List where

open import Prelude
open import Fin


--------------------------------------------------------------------------------


data List (X : Set) : Set
  where
    ∙   : List X
    _,_ : List X → X → List X


len : ∀ {X} → List X → Nat
len ∙       = zero
len (Ξ , A) = suc (len Ξ)


get : ∀ {X} → (Ξ : List X) → Fin (len Ξ)
            → X
get ∙       ()
get (Ξ , A) zero    = A
get (Ξ , B) (suc i) = get Ξ i


gets : ∀ {X n} → (Ξ : List X) → len Ξ ≥ n
               → List X
gets ∙       done     = ∙
gets (Ξ , A) (drop e) = gets Ξ e
gets (Ξ , A) (keep e) = gets Ξ e , A


map : ∀ {X Y} → (X → Y) → List X
              → List Y
map F ∙       = ∙
map F (Ξ , A) = map F Ξ , F A


--------------------------------------------------------------------------------


infix 4 _⊇_
data _⊇_ {X} : List X → List X → Set
  where
    done : ∙ ⊇ ∙

    drop : ∀ {A Ξ Ξ′} → Ξ′ ⊇ Ξ
                      → Ξ′ , A ⊇ Ξ

    keep : ∀ {A Ξ Ξ′} → Ξ′ ⊇ Ξ
                      → Ξ′ , A ⊇ Ξ , A


bot⊇ : ∀ {X} → {Ξ : List X}
             → Ξ ⊇ ∙
bot⊇ {Ξ = ∙}     = done
bot⊇ {Ξ = Ξ , A} = drop bot⊇


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


⌊_⌋⊇ : ∀ {X} → {Ξ Ξ′ : List X}
             → Ξ′ ⊇ Ξ
             → len Ξ′ ≥ len Ξ
⌊ done ⌋⊇   = done
⌊ drop η ⌋⊇ = drop ⌊ η ⌋⊇
⌊ keep η ⌋⊇ = keep ⌊ η ⌋⊇


--------------------------------------------------------------------------------


infix 4 _∋_
data _∋_ {X} : List X → X → Set
  where
    zero : ∀ {Ξ A} → Ξ , A ∋ A

    suc : ∀ {B Ξ A} → Ξ ∋ A
                    → Ξ , B ∋ A


ren∋ : ∀ {X A} → {Ξ Ξ′ : List X}
               → Ξ′ ⊇ Ξ → Ξ ∋ A
               → Ξ′ ∋ A
ren∋ done     𝒾       = 𝒾
ren∋ (drop η) 𝒾       = suc (ren∋ η 𝒾)
ren∋ (keep η) zero    = zero
ren∋ (keep η) (suc 𝒾) = suc (ren∋ η 𝒾)


find : ∀ {X} → (Ξ : List X) (i : Fin (len Ξ))
             → Ξ ∋ get Ξ i
find ∙       ()
find (Ξ , A) zero    = zero
find (Ξ , B) (suc i) = suc (find Ξ i)


⌊_⌋∋ : ∀ {X A} → {Ξ : List X}
               → Ξ ∋ A
               → Fin (len Ξ)
⌊ zero ⌋∋  = zero
⌊ suc 𝒾 ⌋∋ = suc ⌊ 𝒾 ⌋∋


--------------------------------------------------------------------------------


data All {X} (P : X → Set) : List X → Set
  where
    ∙ : All P ∙

    _,_ : ∀ {Ξ A} → All P Ξ → P A
                  → All P (Ξ , A)


lookup : ∀ {X P A} → {Ξ : List X}
                   → All P Ξ → Ξ ∋ A
                   → P A
lookup (ξ , x) zero    = x
lookup (ξ , y) (suc 𝒾) = lookup ξ 𝒾


lookups : ∀ {X P} → {Ξ Ξ′ : List X}
                  → All P Ξ′ → Ξ′ ⊇ Ξ
                  → All P Ξ
lookups ξ       done     = ∙
lookups (ξ , x) (drop η) = lookups ξ η
lookups (ξ , x) (keep η) = lookups ξ η , x


mapAll : ∀ {X P Q} → {Ξ : List X}
                   → (∀ {A} → P A → Q A) → All P Ξ
                   → All Q Ξ
mapAll f ∙       = ∙
mapAll f (ξ , x) = mapAll f ξ , f x


fromList : ∀ {X P} → (Ξ : List X)
                   → (∀ A → P A)
                   → All P Ξ
fromList ∙       p = ∙
fromList (Ξ , A) p = fromList Ξ p , p A


--------------------------------------------------------------------------------
