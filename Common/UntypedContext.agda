module Common.UntypedContext where

open import Common.Context public


-- Naturals, as a projection of contexts.

ᴺ⌊_⌋ : ∀ {U} → Cx U → ℕ
ᴺ⌊ ⌀ ⌋     = zero
ᴺ⌊ Γ , A ⌋ = suc ᴺ⌊ Γ ⌋


-- Inversion principle for naturals.

invsuc : ∀ {n n′} → ℕ.suc n ≡ suc n′ → n ≡ n′
invsuc refl = refl


-- Finite naturals, or nameless untyped de Bruijn indices, as a projection of context membership.

ⁱ⌊_⌋ : ∀ {U} {A : U} {Γ} → A ∈ Γ → Fin ᴺ⌊ Γ ⌋
ⁱ⌊ top ⌋   = zero
ⁱ⌊ pop i ⌋ = suc ⁱ⌊ i ⌋


-- Preorder on naturals, as a projection of context inclusion.

infix 3 _≤_
data _≤_ : ℕ → ℕ → Set where
  done : zero ≤ zero
  skip : ∀ {n n′} → n ≤ n′ → n ≤ suc n′
  keep : ∀ {n n′} → n ≤ n′ → suc n ≤ suc n′

≤⌊_⌋ : ∀ {U} {Γ Γ′ : Cx U} → Γ ⊆ Γ′ → ᴺ⌊ Γ ⌋ ≤ ᴺ⌊ Γ′ ⌋
≤⌊ done ⌋   = done
≤⌊ skip η ⌋ = skip ≤⌊ η ⌋
≤⌊ keep η ⌋ = keep ≤⌊ η ⌋

refl≤ : ∀ {n} → n ≤ n
refl≤ {zero}  = done
refl≤ {suc n} = keep refl≤

trans≤ : ∀ {n n′ n″} → n ≤ n′ → n′ ≤ n″ → n ≤ n″
trans≤ η        done      = η
trans≤ η        (skip η′) = skip (trans≤ η η′)
trans≤ (skip η) (keep η′) = skip (trans≤ η η′)
trans≤ (keep η) (keep η′) = keep (trans≤ η η′)

unskip≤ : ∀ {n n′} → suc n ≤ n′ → n ≤ n′
unskip≤ (skip η) = skip (unskip≤ η)
unskip≤ (keep η) = skip η

unkeep≤ : ∀ {n n′} → suc n ≤ suc n′ → n ≤ n′
unkeep≤ (skip η) = unskip≤ η
unkeep≤ (keep η) = η

weak≤ : ∀ {n} → n ≤ suc n
weak≤ = skip refl≤

bot≤ : ∀ {n} → zero ≤ n
bot≤ {zero}  = done
bot≤ {suc n} = skip bot≤


-- Monotonicity of finite naturals with respect to preorder on naturals.

monoFin : ∀ {n n′} → n ≤ n′ → Fin n → Fin n′
monoFin done     ()
monoFin (skip η) i       = suc (monoFin η i)
monoFin (keep η) zero    = zero
monoFin (keep η) (suc i) = suc (monoFin η i)

reflmonoFin : ∀ {n} → (i : Fin n) → i ≡ monoFin refl≤ i
reflmonoFin zero    = refl
reflmonoFin (suc i) = cong suc (reflmonoFin i)

transmonoFin : ∀ {n n′ n″} → (η : n ≤ n′) (η′ : n′ ≤ n″) (i : Fin n)
               → monoFin η′ (monoFin η i) ≡ monoFin (trans≤ η η′) i
transmonoFin done     η′        ()
transmonoFin η        (skip η′) i       = cong suc (transmonoFin η η′ i)
transmonoFin (skip η) (keep η′) i       = cong suc (transmonoFin η η′ i)
transmonoFin (keep η) (keep η′) zero    = refl
transmonoFin (keep η) (keep η′) (suc i) = cong suc (transmonoFin η η′ i)


-- Addition of naturals, as a projection of context concatenation.

_+_ : ℕ → ℕ → ℕ
n + zero     = n
n + (suc n′) = suc (n + n′)

id+ₗ : ∀ {n} → n + zero ≡ n
id+ₗ = refl

id+ᵣ : ∀ {n} → zero + n ≡ n
id+ᵣ {zero}  = refl
id+ᵣ {suc n} = cong suc id+ᵣ

weak≤+ₗ : ∀ {n} n′ → n ≤ n + n′
weak≤+ₗ zero     = refl≤
weak≤+ₗ (suc n′) = skip (weak≤+ₗ n′)

weak≤+ᵣ : ∀ {n n′} → n′ ≤ n + n′
weak≤+ᵣ {n} {zero}   = bot≤
weak≤+ᵣ {n} {suc n′} = keep weak≤+ᵣ


-- Subtraction of naturals, as a projection of context thinning.

_-_ : (n : ℕ) → Fin n → ℕ
zero  - ()
suc n - zero  = n
suc n - suc i = suc (n - i)

thin≤ : ∀ {n} → (i : Fin n) → n - i ≤ n
thin≤ zero    = weak≤
thin≤ (suc i) = keep (thin≤ i)


-- Decidable equality of finite naturals.

data _=Fin_ {n} (i : Fin n) : Fin n → Set where
  same : i =Fin i
  diff : (j : Fin (n - i)) → i =Fin monoFin (thin≤ i) j

_≟Fin_ : ∀ {n} → (i j : Fin n) → i =Fin j
zero  ≟Fin zero   = same
zero  ≟Fin suc j  rewrite reflmonoFin j = diff j
suc i ≟Fin zero   = diff zero
suc i ≟Fin suc j  with i ≟Fin j
suc i ≟Fin suc .i | same   = same
suc i ≟Fin suc ._ | diff j = diff (suc j)
