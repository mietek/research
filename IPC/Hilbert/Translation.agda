module IPC.Hilbert.Translation where

open import IPC public

import IPC.Hilbert.List as L
import IPC.Hilbert.Tree as T
import IPC.Hilbert.ListWithContext as LC
import IPC.Hilbert.TreeWithContext as TC

open LC using () renaming (_⊢×_ to LC⟨_⊢×_⟩ ; _⊢_ to LC⟨_⊢_⟩) public
open TC using () renaming (_⊢_ to TC⟨_⊢_⟩) public


-- Translation from list-shaped to tree-shaped variant.

l→t : ∀ {A} → L.⊢ A → T.⊢ A
l→t (Π , ts) = l×→t ts top
  where
    l×→t : ∀ {A Π} → L.⊢× Π → A ∈ Π → T.⊢ A
    l×→t (L.mp i j ts) top     = T.app (l×→t ts i) (l×→t ts j)
    l×→t (L.ci ts)     top     = T.ci
    l×→t (L.ck ts)     top     = T.ck
    l×→t (L.cs ts)     top     = T.cs
    l×→t (L.cpair ts)  top     = T.cpair
    l×→t (L.cfst ts)   top     = T.cfst
    l×→t (L.csnd ts)   top     = T.csnd
    l×→t (L.tt ts)     top     = T.tt
    l×→t (L.cboom ts)  top     = T.cboom
    l×→t (L.cinl ts)   top     = T.cinl
    l×→t (L.cinr ts)   top     = T.cinr
    l×→t (L.ccase ts)  top     = T.ccase
    l×→t (L.mp i j ts) (pop k) = l×→t ts k
    l×→t (L.ci ts)     (pop k) = l×→t ts k
    l×→t (L.ck ts)     (pop k) = l×→t ts k
    l×→t (L.cs ts)     (pop k) = l×→t ts k
    l×→t (L.cpair ts)  (pop k) = l×→t ts k
    l×→t (L.cfst ts)   (pop k) = l×→t ts k
    l×→t (L.csnd ts)   (pop k) = l×→t ts k
    l×→t (L.tt ts)     (pop k) = l×→t ts k
    l×→t (L.cboom ts)  (pop k) = l×→t ts k
    l×→t (L.cinl ts)   (pop k) = l×→t ts k
    l×→t (L.cinr ts)   (pop k) = l×→t ts k
    l×→t (L.ccase ts)  (pop k) = l×→t ts k


-- Translation from tree-shaped to list-shaped variant.

t→l : ∀ {A} → T.⊢ A → L.⊢ A
t→l (T.app t u) = L.app (t→l t) (t→l u)
t→l T.ci        = ⌀ , L.ci L.nil
t→l T.ck        = ⌀ , L.ck L.nil
t→l T.cs        = ⌀ , L.cs L.nil
t→l T.cpair     = ⌀ , L.cpair L.nil
t→l T.cfst      = ⌀ , L.cfst L.nil
t→l T.csnd      = ⌀ , L.csnd L.nil
t→l T.tt        = ⌀ , L.tt L.nil
t→l T.cboom     = ⌀ , L.cboom L.nil
t→l T.cinl      = ⌀ , L.cinl L.nil
t→l T.cinr      = ⌀ , L.cinr L.nil
t→l T.ccase     = ⌀ , L.ccase L.nil


-- Translation from list-shaped to tree-shaped variant, with context.

lc→tc : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
lc→tc (Π , ts) = lc×→tc ts top
  where
    lc×→tc : ∀ {A Γ Π} → LC⟨ Γ ⊢× Π ⟩ → A ∈ Π → TC⟨ Γ ⊢ A ⟩
    lc×→tc (LC.var i ts)  top     = TC.var i
    lc×→tc (LC.mp i j ts) top     = TC.app (lc×→tc ts i) (lc×→tc ts j)
    lc×→tc (LC.ci ts)     top     = TC.ci
    lc×→tc (LC.ck ts)     top     = TC.ck
    lc×→tc (LC.cs ts)     top     = TC.cs
    lc×→tc (LC.cpair ts)  top     = TC.cpair
    lc×→tc (LC.cfst ts)   top     = TC.cfst
    lc×→tc (LC.csnd ts)   top     = TC.csnd
    lc×→tc (LC.tt ts)     top     = TC.tt
    lc×→tc (LC.cboom ts)  top     = TC.cboom
    lc×→tc (LC.cinl ts)   top     = TC.cinl
    lc×→tc (LC.cinr ts)   top     = TC.cinr
    lc×→tc (LC.ccase ts)  top     = TC.ccase
    lc×→tc (LC.var i ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.mp i j ts) (pop k) = lc×→tc ts k
    lc×→tc (LC.ci ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.ck ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.cs ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.cpair ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.cfst ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.csnd ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.tt ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.cboom ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.cinl ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.cinr ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.ccase ts)  (pop k) = lc×→tc ts k


-- Translation from tree-shaped to list-shaped variant, with context.

tc→lc : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
tc→lc (TC.var i)   = ⌀ , LC.var i LC.nil
tc→lc (TC.app t u) = LC.app (tc→lc t) (tc→lc u)
tc→lc TC.ci        = ⌀ , LC.ci LC.nil
tc→lc TC.ck        = ⌀ , LC.ck LC.nil
tc→lc TC.cs        = ⌀ , LC.cs LC.nil
tc→lc TC.cpair     = ⌀ , LC.cpair LC.nil
tc→lc TC.cfst      = ⌀ , LC.cfst LC.nil
tc→lc TC.csnd      = ⌀ , LC.csnd LC.nil
tc→lc TC.tt        = ⌀ , LC.tt LC.nil
tc→lc TC.cboom     = ⌀ , LC.cboom LC.nil
tc→lc TC.cinl      = ⌀ , LC.cinl LC.nil
tc→lc TC.cinr      = ⌀ , LC.cinr LC.nil
tc→lc TC.ccase     = ⌀ , LC.ccase LC.nil


-- Deduction and detachment theorem for list-shaped variant, with context.

lc-lam : ∀ {A B Γ} → LC⟨ Γ , A ⊢ B ⟩ → LC⟨ Γ ⊢ A ▻ B ⟩
lc-lam = tc→lc ∘ TC.lam ∘ lc→tc

lc-lam⋆₀ : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → LC⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩
lc-lam⋆₀ = tc→lc ∘ TC.lam⋆₀ ∘ lc→tc

lc-det : ∀ {A B Γ} → LC⟨ Γ ⊢ A ▻ B ⟩ → LC⟨ Γ , A ⊢ B ⟩
lc-det = tc→lc ∘ TC.det ∘ lc→tc

lc-det⋆₀ : ∀ {A Γ} → LC⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩ → LC⟨ Γ ⊢ A ⟩
lc-det⋆₀ = tc→lc ∘ TC.det⋆₀ ∘ lc→tc


-- Translation between list-shaped variants, with and without context.

l→lc₀ : ∀ {A} → L.⊢ A → LC⟨ ⌀ ⊢ A ⟩
l→lc₀ (Π , ts) = (Π , l×→lc₀× ts)
  where
    l×→lc₀× : ∀ {Π} → L.⊢× Π → LC⟨ ⌀ ⊢× Π ⟩
    l×→lc₀× L.nil         = LC.nil
    l×→lc₀× (L.mp i j ts) = LC.mp i j (l×→lc₀× ts)
    l×→lc₀× (L.ci ts)     = LC.ci (l×→lc₀× ts)
    l×→lc₀× (L.ck ts)     = LC.ck (l×→lc₀× ts)
    l×→lc₀× (L.cs ts)     = LC.cs (l×→lc₀× ts)
    l×→lc₀× (L.cpair ts)  = LC.cpair (l×→lc₀× ts)
    l×→lc₀× (L.cfst ts)   = LC.cfst (l×→lc₀× ts)
    l×→lc₀× (L.csnd ts)   = LC.csnd (l×→lc₀× ts)
    l×→lc₀× (L.tt ts)     = LC.tt (l×→lc₀× ts)
    l×→lc₀× (L.cboom ts)  = LC.cboom (l×→lc₀× ts)
    l×→lc₀× (L.cinl ts)   = LC.cinl (l×→lc₀× ts)
    l×→lc₀× (L.cinr ts)   = LC.cinr (l×→lc₀× ts)
    l×→lc₀× (L.ccase ts)  = LC.ccase (l×→lc₀× ts)

l→lc : ∀ {A Γ} → L.⊢ Γ ▻⋯▻ A → LC⟨ Γ ⊢ A ⟩
l→lc t = lc-det⋆₀ (l→lc₀ t)

lc₀→l : ∀ {A} → LC⟨ ⌀ ⊢ A ⟩ → L.⊢ A
lc₀→l (Π , ts) = (Π , lc₀×→lc× ts)
  where
    lc₀×→lc× : ∀ {Π} → LC⟨ ⌀ ⊢× Π ⟩ → L.⊢× Π
    lc₀×→lc× LC.nil         = L.nil
    lc₀×→lc× (LC.var () ts)
    lc₀×→lc× (LC.mp i j ts) = L.mp i j (lc₀×→lc× ts)
    lc₀×→lc× (LC.ci ts)     = L.ci (lc₀×→lc× ts)
    lc₀×→lc× (LC.ck ts)     = L.ck (lc₀×→lc× ts)
    lc₀×→lc× (LC.cs ts)     = L.cs (lc₀×→lc× ts)
    lc₀×→lc× (LC.cpair ts)  = L.cpair (lc₀×→lc× ts)
    lc₀×→lc× (LC.cfst ts)   = L.cfst (lc₀×→lc× ts)
    lc₀×→lc× (LC.csnd ts)   = L.csnd (lc₀×→lc× ts)
    lc₀×→lc× (LC.tt ts)     = L.tt (lc₀×→lc× ts)
    lc₀×→lc× (LC.cboom ts)  = L.cboom (lc₀×→lc× ts)
    lc₀×→lc× (LC.cinl ts)   = L.cinl (lc₀×→lc× ts)
    lc₀×→lc× (LC.cinr ts)   = L.cinr (lc₀×→lc× ts)
    lc₀×→lc× (LC.ccase ts)  = L.ccase (lc₀×→lc× ts)

lc→l : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → L.⊢ Γ ▻⋯▻ A
lc→l t = lc₀→l (lc-lam⋆₀ t)


-- Translation between tree-shaped variants, with and without context.

t→tc₀ : ∀ {A} → T.⊢ A → TC⟨ ⌀ ⊢ A ⟩
t→tc₀ (T.app t u) = TC.app (t→tc₀ t) (t→tc₀ u)
t→tc₀ T.ci        = TC.ci
t→tc₀ T.ck        = TC.ck
t→tc₀ T.cs        = TC.cs
t→tc₀ T.cpair     = TC.cpair
t→tc₀ T.cfst      = TC.cfst
t→tc₀ T.csnd      = TC.csnd
t→tc₀ T.tt        = TC.tt
t→tc₀ T.cboom     = TC.cboom
t→tc₀ T.cinl      = TC.cinl
t→tc₀ T.cinr      = TC.cinr
t→tc₀ T.ccase     = TC.ccase

t→tc : ∀ {A Γ} → T.⊢ Γ ▻⋯▻ A → TC⟨ Γ ⊢ A ⟩
t→tc t = TC.det⋆₀ (t→tc₀ t)

tc₀→t : ∀ {A} → TC⟨ ⌀ ⊢ A ⟩ → T.⊢ A
tc₀→t (TC.var ())
tc₀→t (TC.app t u) = T.app (tc₀→t t) (tc₀→t u)
tc₀→t TC.ci        = T.ci
tc₀→t TC.ck        = T.ck
tc₀→t TC.cs        = T.cs
tc₀→t TC.cpair     = T.cpair
tc₀→t TC.cfst      = T.cfst
tc₀→t TC.csnd      = T.csnd
tc₀→t TC.tt        = T.tt
tc₀→t TC.cboom     = T.cboom
tc₀→t TC.cinl      = T.cinl
tc₀→t TC.cinr      = T.cinr
tc₀→t TC.ccase     = T.ccase

tc→t : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → T.⊢ Γ ▻⋯▻ A
tc→t t = tc₀→t (TC.lam⋆₀ t)


-- Additional useful translations.

tc₀→l : ∀ {A} → TC⟨ ⌀ ⊢ A ⟩ → L.⊢ A
tc₀→l = t→l ∘ tc₀→t

tc→l : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → L.⊢ Γ ▻⋯▻ A
tc→l = t→l ∘ tc→t

lc₀→t : ∀ {A} → LC⟨ ⌀ ⊢ A ⟩ → T.⊢ A
lc₀→t = l→t ∘ lc₀→l

lc→t : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → T.⊢ Γ ▻⋯▻ A
lc→t = l→t ∘ lc→l

l→tc₀ : ∀ {A} → L.⊢ A → TC⟨ ⌀ ⊢ A ⟩
l→tc₀ = t→tc₀ ∘ l→t

l→tc : ∀ {A Γ} → L.⊢ Γ ▻⋯▻ A → TC⟨ Γ ⊢ A ⟩
l→tc = t→tc ∘ l→t

t→lc₀ : ∀ {A} → T.⊢ A → LC⟨ ⌀ ⊢ A ⟩
t→lc₀ = l→lc₀ ∘ t→l

t→lc : ∀ {A Γ} → T.⊢ Γ ▻⋯▻ A → LC⟨ Γ ⊢ A ⟩
t→lc = l→lc ∘ t→l
