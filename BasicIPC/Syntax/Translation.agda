-- Translation between different formalisations of syntax.

module BasicIPC.Syntax.Translation where

open import BasicIPC.Syntax.Common public

import BasicIPC.Syntax.ClosedHilbertSequential as CHS
import BasicIPC.Syntax.ClosedHilbert as CH
import BasicIPC.Syntax.HilbertSequential as HS
import BasicIPC.Syntax.Hilbert as H
import BasicIPC.Syntax.Gentzen as G

open HS using () renaming (_⊢×_ to HS⟨_⊢×_⟩ ; _⊢_ to HS⟨_⊢_⟩) public
open H using () renaming (_⊢_ to H⟨_⊢_⟩) public
open G using () renaming (_⊢_ to G⟨_⊢_⟩) public


-- Available translations.
--
--       ┌─────┬─────┬─────┬─────┬─────┐
--       │ CHS │ CH  │ HS  │ H   │ G   │
-- ┌─────┼─────┼─────┼─────┼─────┼─────┤
-- │ CHS │     │ d   │ d   │ ∘   │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ CH  │ d   │     │ ∘   │ d   │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ HS  │ d   │ ∘   │     │ d   │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ H   │ ∘   │ d   │ d   │     │ d   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ G   │ ∘   │ ∘   │ ∘   │ d   │     │
-- └─────┴─────┴─────┴─────┴─────┴─────┘
--
-- d : Direct translation.
-- ∘ : Composition of translations.


-- Translation from closed Hilbert-style linear to closed Hilbert-style.

chs→ch : ∀ {A} → CHS.⊢ A → CH.⊢ A
chs→ch (Ξ , ts) = chs×→ch ts top
  where
    chs×→ch : ∀ {A Ξ} → CHS.⊢× Ξ → A ∈ Ξ → CH.⊢ A
    chs×→ch (CHS.mp i j ts) top     = CH.app (chs×→ch ts i) (chs×→ch ts j)
    chs×→ch (CHS.ci ts)     top     = CH.ci
    chs×→ch (CHS.ck ts)     top     = CH.ck
    chs×→ch (CHS.cs ts)     top     = CH.cs
    chs×→ch (CHS.cpair ts)  top     = CH.cpair
    chs×→ch (CHS.cfst ts)   top     = CH.cfst
    chs×→ch (CHS.csnd ts)   top     = CH.csnd
    chs×→ch (CHS.tt ts)     top     = CH.tt
    chs×→ch (CHS.mp i j ts) (pop k) = chs×→ch ts k
    chs×→ch (CHS.ci ts)     (pop k) = chs×→ch ts k
    chs×→ch (CHS.ck ts)     (pop k) = chs×→ch ts k
    chs×→ch (CHS.cs ts)     (pop k) = chs×→ch ts k
    chs×→ch (CHS.cpair ts)  (pop k) = chs×→ch ts k
    chs×→ch (CHS.cfst ts)   (pop k) = chs×→ch ts k
    chs×→ch (CHS.csnd ts)   (pop k) = chs×→ch ts k
    chs×→ch (CHS.tt ts)     (pop k) = chs×→ch ts k


-- Translation from closed Hilbert-style to closed Hilbert-style linear.

ch→chs : ∀ {A} → CH.⊢ A → CHS.⊢ A
ch→chs (CH.app t u) = CHS.app (ch→chs t) (ch→chs u)
ch→chs CH.ci        = ⌀ , CHS.ci CHS.nil
ch→chs CH.ck        = ⌀ , CHS.ck CHS.nil
ch→chs CH.cs        = ⌀ , CHS.cs CHS.nil
ch→chs CH.cpair     = ⌀ , CHS.cpair CHS.nil
ch→chs CH.cfst      = ⌀ , CHS.cfst CHS.nil
ch→chs CH.csnd      = ⌀ , CHS.csnd CHS.nil
ch→chs CH.tt        = ⌀ , CHS.tt CHS.nil


-- Translation from Hilbert-style linear to Hilbert-style.

hs→h : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
hs→h (Ξ , ts) = hs×→h ts top
  where
    hs×→h : ∀ {A Ξ Γ} → HS⟨ Γ ⊢× Ξ ⟩ → A ∈ Ξ → H⟨ Γ ⊢ A ⟩
    hs×→h (HS.var i ts)  top     = H.var i
    hs×→h (HS.mp i j ts) top     = H.app (hs×→h ts i) (hs×→h ts j)
    hs×→h (HS.ci ts)     top     = H.ci
    hs×→h (HS.ck ts)     top     = H.ck
    hs×→h (HS.cs ts)     top     = H.cs
    hs×→h (HS.cpair ts)  top     = H.cpair
    hs×→h (HS.cfst ts)   top     = H.cfst
    hs×→h (HS.csnd ts)   top     = H.csnd
    hs×→h (HS.tt ts)     top     = H.tt
    hs×→h (HS.var i ts)  (pop k) = hs×→h ts k
    hs×→h (HS.mp i j ts) (pop k) = hs×→h ts k
    hs×→h (HS.ci ts)     (pop k) = hs×→h ts k
    hs×→h (HS.ck ts)     (pop k) = hs×→h ts k
    hs×→h (HS.cs ts)     (pop k) = hs×→h ts k
    hs×→h (HS.cpair ts)  (pop k) = hs×→h ts k
    hs×→h (HS.cfst ts)   (pop k) = hs×→h ts k
    hs×→h (HS.csnd ts)   (pop k) = hs×→h ts k
    hs×→h (HS.tt ts)     (pop k) = hs×→h ts k


-- Translation from Hilbert-style to Hilbert-style linear.

h→hs : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
h→hs (H.var i)   = ⌀ , HS.var i HS.nil
h→hs (H.app t u) = HS.app (h→hs t) (h→hs u)
h→hs H.ci        = ⌀ , HS.ci HS.nil
h→hs H.ck        = ⌀ , HS.ck HS.nil
h→hs H.cs        = ⌀ , HS.cs HS.nil
h→hs H.cpair     = ⌀ , HS.cpair HS.nil
h→hs H.cfst      = ⌀ , HS.cfst HS.nil
h→hs H.csnd      = ⌀ , HS.csnd HS.nil
h→hs H.tt        = ⌀ , HS.tt HS.nil


-- Deduction and detachment theorems for Hilbert-style linear.

hs-lam : ∀ {A B Γ} → HS⟨ Γ , A ⊢ B ⟩ → HS⟨ Γ ⊢ A ▻ B ⟩
hs-lam = h→hs ∘ H.lam ∘ hs→h

hs-lam⋆₀ : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → HS⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩
hs-lam⋆₀ = h→hs ∘ H.lam⋆₀ ∘ hs→h

hs-det : ∀ {A B Γ} → HS⟨ Γ ⊢ A ▻ B ⟩ → HS⟨ Γ , A ⊢ B ⟩
hs-det = h→hs ∘ H.det ∘ hs→h

hs-det⋆₀ : ∀ {A Γ} → HS⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩ → HS⟨ Γ ⊢ A ⟩
hs-det⋆₀ = h→hs ∘ H.det⋆₀ ∘ hs→h


-- Translation from closed Hilbert-style linear to Hilbert-style linear.

chs→hs₀ : ∀ {A} → CHS.⊢ A → HS⟨ ⌀ ⊢ A ⟩
chs→hs₀ (Ξ , ts) = Ξ , chs×→hs₀× ts
  where
    chs×→hs₀× : ∀ {Ξ} → CHS.⊢× Ξ → HS⟨ ⌀ ⊢× Ξ ⟩
    chs×→hs₀× CHS.nil         = HS.nil
    chs×→hs₀× (CHS.mp i j ts) = HS.mp i j (chs×→hs₀× ts)
    chs×→hs₀× (CHS.ci ts)     = HS.ci (chs×→hs₀× ts)
    chs×→hs₀× (CHS.ck ts)     = HS.ck (chs×→hs₀× ts)
    chs×→hs₀× (CHS.cs ts)     = HS.cs (chs×→hs₀× ts)
    chs×→hs₀× (CHS.cpair ts)  = HS.cpair (chs×→hs₀× ts)
    chs×→hs₀× (CHS.cfst ts)   = HS.cfst (chs×→hs₀× ts)
    chs×→hs₀× (CHS.csnd ts)   = HS.csnd (chs×→hs₀× ts)
    chs×→hs₀× (CHS.tt ts)     = HS.tt (chs×→hs₀× ts)

chs→hs : ∀ {A Γ} → CHS.⊢ Γ ▻⋯▻ A → HS⟨ Γ ⊢ A ⟩
chs→hs t = hs-det⋆₀ (chs→hs₀ t)


-- Translation from Hilbert-style linear to closed Hilbert-style linear.

hs₀→chs : ∀ {A} → HS⟨ ⌀ ⊢ A ⟩ → CHS.⊢ A
hs₀→chs (Ξ , ts) = Ξ , hs₀×→chs× ts
  where
    hs₀×→chs× : ∀ {Ξ} → HS⟨ ⌀ ⊢× Ξ ⟩ → CHS.⊢× Ξ
    hs₀×→chs× HS.nil         = CHS.nil
    hs₀×→chs× (HS.var () ts)
    hs₀×→chs× (HS.mp i j ts) = CHS.mp i j (hs₀×→chs× ts)
    hs₀×→chs× (HS.ci ts)     = CHS.ci (hs₀×→chs× ts)
    hs₀×→chs× (HS.ck ts)     = CHS.ck (hs₀×→chs× ts)
    hs₀×→chs× (HS.cs ts)     = CHS.cs (hs₀×→chs× ts)
    hs₀×→chs× (HS.cpair ts)  = CHS.cpair (hs₀×→chs× ts)
    hs₀×→chs× (HS.cfst ts)   = CHS.cfst (hs₀×→chs× ts)
    hs₀×→chs× (HS.csnd ts)   = CHS.csnd (hs₀×→chs× ts)
    hs₀×→chs× (HS.tt ts)     = CHS.tt (hs₀×→chs× ts)

hs→chs : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → CHS.⊢ Γ ▻⋯▻ A
hs→chs t = hs₀→chs (hs-lam⋆₀ t)


-- Translation from closed Hilbert-style to Hilbert-style.

ch→h₀ : ∀ {A} → CH.⊢ A → H⟨ ⌀ ⊢ A ⟩
ch→h₀ (CH.app t u) = H.app (ch→h₀ t) (ch→h₀ u)
ch→h₀ CH.ci        = H.ci
ch→h₀ CH.ck        = H.ck
ch→h₀ CH.cs        = H.cs
ch→h₀ CH.cpair     = H.cpair
ch→h₀ CH.cfst      = H.cfst
ch→h₀ CH.csnd      = H.csnd
ch→h₀ CH.tt        = H.tt

ch→h : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → H⟨ Γ ⊢ A ⟩
ch→h t = H.det⋆₀ (ch→h₀ t)


-- Translation from Hilbert-style to closed Hilbert-style.

h₀→ch : ∀ {A} → H⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
h₀→ch (H.var ())
h₀→ch (H.app t u) = CH.app (h₀→ch t) (h₀→ch u)
h₀→ch H.ci        = CH.ci
h₀→ch H.ck        = CH.ck
h₀→ch H.cs        = CH.cs
h₀→ch H.cpair     = CH.cpair
h₀→ch H.cfst      = CH.cfst
h₀→ch H.csnd      = CH.csnd
h₀→ch H.tt        = CH.tt

h→ch : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
h→ch t = h₀→ch (H.lam⋆₀ t)


-- Translation from Hilbert-style to Gentzen-style.

h→g : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
h→g (H.var i)   = G.var i
h→g (H.app t u) = G.app (h→g t) (h→g u)
h→g H.ci        = G.ci
h→g H.ck        = G.ck
h→g H.cs        = G.cs
h→g H.cpair     = G.cpair
h→g H.cfst      = G.cfst
h→g H.csnd      = G.csnd
h→g H.tt        = G.tt


-- Translation from Gentzen-style to Hilbert-style.

g→h : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
g→h (G.var i)    = H.var i
g→h (G.lam t)    = H.lam (g→h t)
g→h (G.app t u)  = H.app (g→h t) (g→h u)
g→h (G.pair t u) = H.pair (g→h t) (g→h u)
g→h (G.fst t)    = H.fst (g→h t)
g→h (G.snd t)    = H.snd (g→h t)
g→h G.tt         = H.tt


-- Additional translations from closed Hilbert-style linear.

chs→h₀ : ∀ {A} → CHS.⊢ A → H⟨ ⌀ ⊢ A ⟩
chs→h₀ = ch→h₀ ∘ chs→ch

chs→h : ∀ {A Γ} → CHS.⊢ Γ ▻⋯▻ A → H⟨ Γ ⊢ A ⟩
chs→h = ch→h ∘ chs→ch

chs→g₀ : ∀ {A} → CHS.⊢ A → G⟨ ⌀ ⊢ A ⟩
chs→g₀ = h→g ∘ chs→h₀

chs→g : ∀ {A Γ} → CHS.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
chs→g = h→g ∘ chs→h


-- Additional translations from closed Hilbert-style.

ch→hs₀ : ∀ {A} → CH.⊢ A → HS⟨ ⌀ ⊢ A ⟩
ch→hs₀ = chs→hs₀ ∘ ch→chs

ch→hs : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → HS⟨ Γ ⊢ A ⟩
ch→hs = chs→hs ∘ ch→chs

ch→g₀ : ∀ {A} → CH.⊢ A → G⟨ ⌀ ⊢ A ⟩
ch→g₀ = h→g ∘ ch→h₀

ch→g : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
ch→g = h→g ∘ ch→h


-- Additional translations from Hilbert-style linear.

hs₀→ch : ∀ {A} → HS⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
hs₀→ch = chs→ch ∘ hs₀→chs

hs→ch : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
hs→ch = chs→ch ∘ hs→chs

hs→g : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
hs→g = h→g ∘ hs→h


-- Additional translations from Hilbert-style.

h₀→chs : ∀ {A} → H⟨ ⌀ ⊢ A ⟩ → CHS.⊢ A
h₀→chs = ch→chs ∘ h₀→ch

h→chs : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → CHS.⊢ Γ ▻⋯▻ A
h→chs = ch→chs ∘ h→ch


-- Additional translations from Gentzen-style.

g₀→chs : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → CHS.⊢ A
g₀→chs = h₀→chs ∘ g→h

g→chs : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → CHS.⊢ Γ ▻⋯▻ A
g→chs = h→chs ∘ g→h

g₀→ch : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
g₀→ch = h₀→ch ∘ g→h

g→ch : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
g→ch = h→ch ∘ g→h

g→hs : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
g→hs = h→hs ∘ g→h
