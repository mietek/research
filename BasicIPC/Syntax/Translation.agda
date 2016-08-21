-- Translation between different formalisations of syntax.

module BasicIPC.Syntax.Translation where

open import BasicIPC.Syntax.Common public

import BasicIPC.Syntax.ClosedHilbertLinear as CHL
import BasicIPC.Syntax.ClosedHilbert as CH
import BasicIPC.Syntax.HilbertLinear as HL
import BasicIPC.Syntax.Hilbert as H
import BasicIPC.Syntax.Gentzen as G

open HL using () renaming (_⊢×_ to HL⟨_⊢×_⟩ ; _⊢_ to HL⟨_⊢_⟩) public
open H using () renaming (_⊢_ to H⟨_⊢_⟩) public
open G using () renaming (_⊢_ to G⟨_⊢_⟩) public


-- Available translations.
--
--         ┌─────┬─────┬─────┬─────┬─────┐
--         │ CHL │ CH  │ HL  │ H   │ G   │
--   ┌─────┼─────┼─────┼─────┼─────┼─────┤
--   │ CHL │     │  □  │  □  │  ∘  │  ∘  │
--   ├─────┼─────┼─────┼─────┼─────┼─────┤
--   │ CH  │  □  │     │  ∘  │  □  │  ∘  │
--   ├─────┼─────┼─────┼─────┼─────┼─────┤
--   │ HL  │  □  │  ∘  │     │  □  │  ∘  │
--   ├─────┼─────┼─────┼─────┼─────┼─────┤
--   │ H   │  ∘  │  □  │  □  │     │  □  │
--   ├─────┼─────┼─────┼─────┼─────┼─────┤
--   │ G   │  ∘  │  ∘  │  ∘  │  □  │     │
--   └─────┴─────┴─────┴─────┴─────┴─────┘
--
-- □ : Direct translation.
-- ∘ : Composition of translations.


-- Translation from closed Hilbert-style linear to closed Hilbert-style.

chl→ch : ∀ {A} → CHL.⊢ A → CH.⊢ A
chl→ch (Π , ts) = chl×→ch ts top
  where
    chl×→ch : ∀ {A Π} → CHL.⊢× Π → A ∈ Π → CH.⊢ A
    chl×→ch (CHL.mp i j ts) top     = CH.app (chl×→ch ts i) (chl×→ch ts j)
    chl×→ch (CHL.ci ts)     top     = CH.ci
    chl×→ch (CHL.ck ts)     top     = CH.ck
    chl×→ch (CHL.cs ts)     top     = CH.cs
    chl×→ch (CHL.cpair ts)  top     = CH.cpair
    chl×→ch (CHL.cfst ts)   top     = CH.cfst
    chl×→ch (CHL.csnd ts)   top     = CH.csnd
    chl×→ch (CHL.tt ts)     top     = CH.tt
    chl×→ch (CHL.mp i j ts) (pop k) = chl×→ch ts k
    chl×→ch (CHL.ci ts)     (pop k) = chl×→ch ts k
    chl×→ch (CHL.ck ts)     (pop k) = chl×→ch ts k
    chl×→ch (CHL.cs ts)     (pop k) = chl×→ch ts k
    chl×→ch (CHL.cpair ts)  (pop k) = chl×→ch ts k
    chl×→ch (CHL.cfst ts)   (pop k) = chl×→ch ts k
    chl×→ch (CHL.csnd ts)   (pop k) = chl×→ch ts k
    chl×→ch (CHL.tt ts)     (pop k) = chl×→ch ts k


-- Translation from closed Hilbert-style to closed Hilbert-style linear.

ch→chl : ∀ {A} → CH.⊢ A → CHL.⊢ A
ch→chl (CH.app t u) = CHL.app (ch→chl t) (ch→chl u)
ch→chl CH.ci        = ⌀ , CHL.ci CHL.nil
ch→chl CH.ck        = ⌀ , CHL.ck CHL.nil
ch→chl CH.cs        = ⌀ , CHL.cs CHL.nil
ch→chl CH.cpair     = ⌀ , CHL.cpair CHL.nil
ch→chl CH.cfst      = ⌀ , CHL.cfst CHL.nil
ch→chl CH.csnd      = ⌀ , CHL.csnd CHL.nil
ch→chl CH.tt        = ⌀ , CHL.tt CHL.nil


-- Translation from Hilbert-style linear to Hilbert-style.

hl→h : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
hl→h (Π , ts) = hl×→h ts top
  where
    hl×→h : ∀ {A Π Γ} → HL⟨ Γ ⊢× Π ⟩ → A ∈ Π → H⟨ Γ ⊢ A ⟩
    hl×→h (HL.var i ts)  top     = H.var i
    hl×→h (HL.mp i j ts) top     = H.app (hl×→h ts i) (hl×→h ts j)
    hl×→h (HL.ci ts)     top     = H.ci
    hl×→h (HL.ck ts)     top     = H.ck
    hl×→h (HL.cs ts)     top     = H.cs
    hl×→h (HL.cpair ts)  top     = H.cpair
    hl×→h (HL.cfst ts)   top     = H.cfst
    hl×→h (HL.csnd ts)   top     = H.csnd
    hl×→h (HL.tt ts)     top     = H.tt
    hl×→h (HL.var i ts)  (pop k) = hl×→h ts k
    hl×→h (HL.mp i j ts) (pop k) = hl×→h ts k
    hl×→h (HL.ci ts)     (pop k) = hl×→h ts k
    hl×→h (HL.ck ts)     (pop k) = hl×→h ts k
    hl×→h (HL.cs ts)     (pop k) = hl×→h ts k
    hl×→h (HL.cpair ts)  (pop k) = hl×→h ts k
    hl×→h (HL.cfst ts)   (pop k) = hl×→h ts k
    hl×→h (HL.csnd ts)   (pop k) = hl×→h ts k
    hl×→h (HL.tt ts)     (pop k) = hl×→h ts k


-- Translation from Hilbert-style to Hilbert-style linear.

h→hl : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → HL⟨ Γ ⊢ A ⟩
h→hl (H.var i)   = ⌀ , HL.var i HL.nil
h→hl (H.app t u) = HL.app (h→hl t) (h→hl u)
h→hl H.ci        = ⌀ , HL.ci HL.nil
h→hl H.ck        = ⌀ , HL.ck HL.nil
h→hl H.cs        = ⌀ , HL.cs HL.nil
h→hl H.cpair     = ⌀ , HL.cpair HL.nil
h→hl H.cfst      = ⌀ , HL.cfst HL.nil
h→hl H.csnd      = ⌀ , HL.csnd HL.nil
h→hl H.tt        = ⌀ , HL.tt HL.nil


-- Deduction and detachment theorems for Hilbert-style linear.

hl-lam : ∀ {A B Γ} → HL⟨ Γ , A ⊢ B ⟩ → HL⟨ Γ ⊢ A ▻ B ⟩
hl-lam = h→hl ∘ H.lam ∘ hl→h

hl-lam⋆₀ : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → HL⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩
hl-lam⋆₀ = h→hl ∘ H.lam⋆₀ ∘ hl→h

hl-det : ∀ {A B Γ} → HL⟨ Γ ⊢ A ▻ B ⟩ → HL⟨ Γ , A ⊢ B ⟩
hl-det = h→hl ∘ H.det ∘ hl→h

hl-det⋆₀ : ∀ {A Γ} → HL⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩ → HL⟨ Γ ⊢ A ⟩
hl-det⋆₀ = h→hl ∘ H.det⋆₀ ∘ hl→h


-- Translation from closed Hilbert-style linear to Hilbert-style linear.

chl→hl₀ : ∀ {A} → CHL.⊢ A → HL⟨ ⌀ ⊢ A ⟩
chl→hl₀ (Π , ts) = Π , chl×→hl₀× ts
  where
    chl×→hl₀× : ∀ {Π} → CHL.⊢× Π → HL⟨ ⌀ ⊢× Π ⟩
    chl×→hl₀× CHL.nil         = HL.nil
    chl×→hl₀× (CHL.mp i j ts) = HL.mp i j (chl×→hl₀× ts)
    chl×→hl₀× (CHL.ci ts)     = HL.ci (chl×→hl₀× ts)
    chl×→hl₀× (CHL.ck ts)     = HL.ck (chl×→hl₀× ts)
    chl×→hl₀× (CHL.cs ts)     = HL.cs (chl×→hl₀× ts)
    chl×→hl₀× (CHL.cpair ts)  = HL.cpair (chl×→hl₀× ts)
    chl×→hl₀× (CHL.cfst ts)   = HL.cfst (chl×→hl₀× ts)
    chl×→hl₀× (CHL.csnd ts)   = HL.csnd (chl×→hl₀× ts)
    chl×→hl₀× (CHL.tt ts)     = HL.tt (chl×→hl₀× ts)

chl→hl : ∀ {A Γ} → CHL.⊢ Γ ▻⋯▻ A → HL⟨ Γ ⊢ A ⟩
chl→hl t = hl-det⋆₀ (chl→hl₀ t)


-- Translation from Hilbert-style linear to closed Hilbert-style linear.

hl₀→chl : ∀ {A} → HL⟨ ⌀ ⊢ A ⟩ → CHL.⊢ A
hl₀→chl (Π , ts) = Π , hl₀×→chl× ts
  where
    hl₀×→chl× : ∀ {Π} → HL⟨ ⌀ ⊢× Π ⟩ → CHL.⊢× Π
    hl₀×→chl× HL.nil         = CHL.nil
    hl₀×→chl× (HL.var () ts)
    hl₀×→chl× (HL.mp i j ts) = CHL.mp i j (hl₀×→chl× ts)
    hl₀×→chl× (HL.ci ts)     = CHL.ci (hl₀×→chl× ts)
    hl₀×→chl× (HL.ck ts)     = CHL.ck (hl₀×→chl× ts)
    hl₀×→chl× (HL.cs ts)     = CHL.cs (hl₀×→chl× ts)
    hl₀×→chl× (HL.cpair ts)  = CHL.cpair (hl₀×→chl× ts)
    hl₀×→chl× (HL.cfst ts)   = CHL.cfst (hl₀×→chl× ts)
    hl₀×→chl× (HL.csnd ts)   = CHL.csnd (hl₀×→chl× ts)
    hl₀×→chl× (HL.tt ts)     = CHL.tt (hl₀×→chl× ts)

hl→chl : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → CHL.⊢ Γ ▻⋯▻ A
hl→chl t = hl₀→chl (hl-lam⋆₀ t)


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

chl→h₀ : ∀ {A} → CHL.⊢ A → H⟨ ⌀ ⊢ A ⟩
chl→h₀ = ch→h₀ ∘ chl→ch

chl→h : ∀ {A Γ} → CHL.⊢ Γ ▻⋯▻ A → H⟨ Γ ⊢ A ⟩
chl→h = ch→h ∘ chl→ch

chl→g₀ : ∀ {A} → CHL.⊢ A → G⟨ ⌀ ⊢ A ⟩
chl→g₀ = h→g ∘ chl→h₀

chl→g : ∀ {A Γ} → CHL.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
chl→g = h→g ∘ chl→h


-- Additional translations from closed Hilbert-style.

ch→hl₀ : ∀ {A} → CH.⊢ A → HL⟨ ⌀ ⊢ A ⟩
ch→hl₀ = chl→hl₀ ∘ ch→chl

ch→hl : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → HL⟨ Γ ⊢ A ⟩
ch→hl = chl→hl ∘ ch→chl

ch→g₀ : ∀ {A} → CH.⊢ A → G⟨ ⌀ ⊢ A ⟩
ch→g₀ = h→g ∘ ch→h₀

ch→g : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
ch→g = h→g ∘ ch→h


-- Additional translations from Hilbert-style linear.

hl₀→ch : ∀ {A} → HL⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
hl₀→ch = chl→ch ∘ hl₀→chl

hl→ch : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
hl→ch = chl→ch ∘ hl→chl

hl→g : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
hl→g = h→g ∘ hl→h


-- Additional translations from Hilbert-style.

h₀→chl : ∀ {A} → H⟨ ⌀ ⊢ A ⟩ → CHL.⊢ A
h₀→chl = ch→chl ∘ h₀→ch

h→chl : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → CHL.⊢ Γ ▻⋯▻ A
h→chl = ch→chl ∘ h→ch


-- Additional translations from Gentzen-style.

g₀→chl : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → CHL.⊢ A
g₀→chl = h₀→chl ∘ g→h

g→chl : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → CHL.⊢ Γ ▻⋯▻ A
g→chl = h→chl ∘ g→h

g₀→ch : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
g₀→ch = h₀→ch ∘ g→h

g→ch : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
g→ch = h→ch ∘ g→h

g→hl : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HL⟨ Γ ⊢ A ⟩
g→hl = h→hl ∘ g→h
