module AltArtemov.G.Vec.Core where

open import AltArtemov.G.Tm public


data Ty : Set where
  ⊥  : Ty
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  _∶_ : Tm 0 → Ty → Ty

infixr 5 _⊃_
infixr 15 _∶_


data Vec (g : ℕ) : ℕ → Set where
  []  : Vec g zero
  _∷_ : ∀ {n} → Tm g → Vec g n → Vec g (suc n)

_∴_ : ∀ {n} → Vec 0 n → Ty → Ty
[]       ∴ A = A
(t ∷ ts) ∴ A = t ∶ (ts ∴ A)

infixr 15 _∴_
infixr 15 _∷_

[_] : ∀ {g} → Tm g → Vec g (suc zero)
[ t ] = t ∷ []

VARs[_] : ∀ {g} → (n : ℕ) → Fin g → Vec g n
VARs[ zero ]  i = []
VARs[ suc n ] i = VAR[ n ] i ∷ VARs[ n ] i

LAMs[_] : ∀ {g} → (n : ℕ) → Vec (suc g) n → Vec g n
LAMs[ zero ]  []       = []
LAMs[ suc n ] (t ∷ ts) = LAM[ n ] t ∷ LAMs[ n ] ts

APPs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n → Vec g n
APPs[ zero ]  []       []       = []
APPs[ suc n ] (t ∷ ts) (u ∷ us) = APP[ n ] t u ∷ APPs[ n ] ts us

PAIRs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n → Vec g n
PAIRs[ zero ]  []       []       = []
PAIRs[ suc n ] (t ∷ ts) (u ∷ us) = PAIR[ n ] t u ∷ PAIRs[ n ] ts us

FSTs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n
FSTs[ zero ]  []       = []
FSTs[ suc n ] (t ∷ ts) = FST[ n ] t ∷ FSTs[ n ] ts

SNDs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n
SNDs[ zero ]  []       = []
SNDs[ suc n ] (t ∷ ts) = SND[ n ] t ∷ SNDs[ n ] ts

UPs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n
UPs[ zero ]  []       = []
UPs[ suc n ] (t ∷ ts) = UP[ n ] t ∷ UPs[ n ] ts

DOWNs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n
DOWNs[ zero ]  []       = []
DOWNs[ suc n ] (t ∷ ts) = DOWN[ n ] t ∷ DOWNs[ n ] ts

head : ∀ {g n} → Vec g (suc n) → Tm g
head (t ∷ ts) = t

head-LAMs : ∀ {g n} (ts : Vec (suc g) (suc n)) → head (LAMs[ suc n ] ts) ≡ LAM[ n ] (head ts)
head-LAMs (t ∷ ts) = refl

head-APPs : ∀ {g n} (ts us : Vec g (suc n)) → head (APPs[ suc n ] ts us) ≡ APP[ n ] (head ts) (head us)
head-APPs (t ∷ ts) (u ∷ us) = refl

head-PAIRs : ∀ {g n} (ts us : Vec g (suc n)) → head (PAIRs[ suc n ] ts us) ≡ PAIR[ n ] (head ts) (head us)
head-PAIRs (t ∷ ts) (u ∷ us) = refl

head-FSTs : ∀ {g n} (ts : Vec g (suc n)) → head (FSTs[ suc n ] ts) ≡ FST[ n ] (head ts)
head-FSTs (t ∷ ts) = refl

head-SNDs : ∀ {g n} (ts : Vec g (suc n)) → head (SNDs[ suc n ] ts) ≡ SND[ n ] (head ts)
head-SNDs (t ∷ ts) = refl

head-UPs : ∀ {g n} (ts : Vec g (suc n)) → head (UPs[ suc n ] ts) ≡ UP[ n ] (head ts)
head-UPs (t ∷ ts) = refl

head-DOWNs : ∀ {g n} (ts : Vec g (suc n)) → head (DOWNs[ suc n ] ts) ≡ DOWN[ n ] (head ts)
head-DOWNs (t ∷ ts) = refl

tail : ∀ {g n} → Vec g (suc n) → Vec g n
tail (t ∷ ts) = ts

tail-LAMs : ∀ {g n} (ts : Vec (suc g) (suc n)) → tail (LAMs[ suc n ] ts) ≡ LAMs[ n ] (tail ts)
tail-LAMs (t ∷ ts) = refl

tail-APPs : ∀ {g n} (ts us : Vec g (suc n)) → tail (APPs[ suc n ] ts us) ≡ APPs[ n ] (tail ts) (tail us)
tail-APPs (t ∷ ts) (u ∷ us) = refl

tail-PAIRs : ∀ {g n} (ts us : Vec g (suc n)) → tail (PAIRs[ suc n ] ts us) ≡ PAIRs[ n ] (tail ts) (tail us)
tail-PAIRs (t ∷ ts) (u ∷ us) = refl

tail-FSTs : ∀ {g n} (ts : Vec g (suc n)) → tail (FSTs[ suc n ] ts) ≡ FSTs[ n ] (tail ts)
tail-FSTs (t ∷ ts) = refl

tail-SNDs : ∀ {g n} (ts : Vec g (suc n)) → tail (SNDs[ suc n ] ts) ≡ SNDs[ n ] (tail ts)
tail-SNDs (t ∷ ts) = refl

tail-UPs : ∀ {g n} (ts : Vec g (suc n)) → tail (UPs[ suc n ] ts) ≡ UPs[ n ] (tail ts)
tail-UPs (t ∷ ts) = refl

tail-DOWNs : ∀ {g n} (ts : Vec g (suc n)) → tail (DOWNs[ suc n ] ts) ≡ DOWNs[ n ] (tail ts)
tail-DOWNs (t ∷ ts) = refl

ren-vec : ∀ {g g′ n} → g′ ≥ g → Vec g n → Vec g′ n
ren-vec h []       = []
ren-vec h (t ∷ ts) = ren-tm h t ∷ ren-vec h ts

wk-vec : ∀ {g n} → Vec g n → Vec (suc g) n
wk-vec = ren-vec ≥wk

wk*-vec : ∀ {g n} → Vec 0 n → Vec g n
wk*-vec = ren-vec ≥to

ren-vec-id : ∀ {g n} (ts : Vec g n) → ren-vec ≥id ts ≡ ts
ren-vec-id []       = refl
ren-vec-id (t ∷ ts) = cong₂ _∷_ (ren-tm-id t) (ren-vec-id ts)

ren-vec-○ : ∀ {g g′ g″ n} (h′ : g″ ≥ g′) (h : g′ ≥ g) (ts : Vec g n) →
              ren-vec h′ (ren-vec h ts) ≡ ren-vec (h′ ○ h) ts
ren-vec-○ h′ h []       = refl
ren-vec-○ h′ h (t ∷ ts) = cong₂ _∷_ (ren-tm-○ h′ h t) (ren-vec-○ h′ h ts)

ren-VARs : ∀ {n g g′} (h : g′ ≥ g) (i : Fin g) →
             ren-vec h (VARs[ n ] i) ≡ VARs[ n ] (ren-fin h i)
ren-VARs {zero}  h i = refl
ren-VARs {suc n} h i = cong₂ _∷_ refl (ren-VARs h i)

ren-LAMs : ∀ {g g′ n} (h : g′ ≥ g) (ts : Vec (suc g) n) →
             ren-vec h (LAMs[ n ] ts) ≡ LAMs[ n ] (ren-vec (lift h) ts)
ren-LAMs h []       = refl
ren-LAMs h (t ∷ ts) = cong₂ _∷_ refl (ren-LAMs h ts)

ren-APPs : ∀ {g g′ n} (h : g′ ≥ g) (ts us : Vec g n) →
            ren-vec h (APPs[ n ] ts us) ≡ APPs[ n ] (ren-vec h ts) (ren-vec h us)
ren-APPs h []       []       = refl
ren-APPs h (t ∷ ts) (u ∷ us) = cong₂ _∷_ refl (ren-APPs h ts us)

ren-PAIRs : ∀ {g g′ n} (h : g′ ≥ g) (ts us : Vec g n) →
              ren-vec h (PAIRs[ n ] ts us) ≡ PAIRs[ n ] (ren-vec h ts) (ren-vec h us)
ren-PAIRs h []       []       = refl
ren-PAIRs h (t ∷ ts) (u ∷ us) = cong₂ _∷_ refl (ren-PAIRs h ts us)

ren-FSTs : ∀ {g g′ n} (h : g′ ≥ g) (ts : Vec g n) →
             ren-vec h (FSTs[ n ] ts) ≡ FSTs[ n ] (ren-vec h ts)
ren-FSTs h []       = refl
ren-FSTs h (t ∷ ts) = cong₂ _∷_ refl (ren-FSTs h ts)

ren-SNDs : ∀ {g g′ n} (h : g′ ≥ g) (ts : Vec g n) →
             ren-vec h (SNDs[ n ] ts) ≡ SNDs[ n ] (ren-vec h ts)
ren-SNDs h []       = refl
ren-SNDs h (t ∷ ts) = cong₂ _∷_ refl (ren-SNDs h ts)

ren-UPs : ∀ {g g′ n} (h : g′ ≥ g) (ts : Vec g n) →
            ren-vec h (UPs[ n ] ts) ≡ UPs[ n ] (ren-vec h ts)
ren-UPs h []       = refl
ren-UPs h (t ∷ ts) = cong₂ _∷_ refl (ren-UPs h ts)

ren-DOWNs : ∀ {g g′ n} (h : g′ ≥ g) (ts : Vec g n) →
              ren-vec h (DOWNs[ n ] ts) ≡ DOWNs[ n ] (ren-vec h ts)
ren-DOWNs h []       = refl
ren-DOWNs h (t ∷ ts) = cong₂ _∷_ refl (ren-DOWNs h ts)


data Cx : Set where
  ∅ : Cx
  _,_ : Cx → Ty → Cx

ᵍ⌊_⌋ : Cx → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋


data _⊇_ : Cx → Cx → Set where
  base : ∅ ⊇ ∅
  weak : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ Γ
  lift : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ (Γ , A)

ʰ⌊_⌋ : ∀ {Γ Γ′} → Γ′ ⊇ Γ → ᵍ⌊ Γ′ ⌋ ≥ ᵍ⌊ Γ ⌋
ʰ⌊ base ⌋   = base
ʰ⌊ weak η ⌋ = weak ʰ⌊ η ⌋
ʰ⌊ lift η ⌋ = lift ʰ⌊ η ⌋

⊇id : ∀ {Γ} → Γ ⊇ Γ
⊇id {∅}     = base
⊇id {Γ , A} = lift ⊇id

⊇to : ∀ {Γ} → Γ ⊇ ∅
⊇to {∅}     = base
⊇to {Γ , A} = weak ⊇to

⊇wk : ∀ {Γ A} → (Γ , A) ⊇ Γ
⊇wk = weak ⊇id

⊇str : ∀ {Γ Γ′ A} → Γ′ ⊇ (Γ , A) → Γ′ ⊇ Γ
⊇str (weak η) = weak (⊇str η)
⊇str (lift η) = weak η

⊇drop : ∀ {Γ Γ′ A} → (Γ′ , A) ⊇ (Γ , A) → Γ′ ⊇ Γ
⊇drop (weak η) = ⊇str η
⊇drop (lift η) = η

_●_ : ∀ {Γ Γ′ Γ″} → Γ″ ⊇ Γ′ → Γ′ ⊇ Γ → Γ″ ⊇ Γ
base    ● η      = η
weak η′ ● η      = weak (η′ ● η)
lift η′ ● weak η = weak (η′ ● η)
lift η′ ● lift η = lift (η′ ● η)

η●id : ∀ {Γ Γ′} (η : Γ′ ⊇ Γ) → η ● ⊇id ≡ η
η●id base     = refl
η●id (weak η) = cong weak (η●id η)
η●id (lift η) = cong lift (η●id η)

id●η : ∀ {Γ Γ′} (η : Γ′ ⊇ Γ) → ⊇id ● η ≡ η
id●η base     = refl
id●η (weak η) = cong weak (id●η η)
id●η (lift η) = cong lift (id●η η)

id-⌊⌋-id : ∀ Γ → ʰ⌊ ⊇id {Γ} ⌋ ≡ ≥id {ᵍ⌊ Γ ⌋}
id-⌊⌋-id ∅       = refl
id-⌊⌋-id (Γ , A) = cong lift (id-⌊⌋-id Γ)

to-⌊⌋-to : ∀ Γ → ʰ⌊ ⊇to {Γ} ⌋ ≡ ≥to {ᵍ⌊ Γ ⌋}
to-⌊⌋-to ∅       = refl
to-⌊⌋-to (Γ , A) = cong weak (to-⌊⌋-to Γ)

ren-fin-⌊⌋-id : ∀ {Γ} (i : Fin ᵍ⌊ Γ ⌋) → ren-fin ʰ⌊ ⊇id ⌋ i ≡ i
ren-fin-⌊⌋-id {Γ} i rewrite id-⌊⌋-id Γ = ren-fin-id i

ren-tm-⌊⌋-id : ∀ {Γ} (t : Tm ᵍ⌊ Γ ⌋) → ren-tm ʰ⌊ ⊇id ⌋ t ≡ t
ren-tm-⌊⌋-id {Γ} t rewrite id-⌊⌋-id Γ = ren-tm-id t

ren-vec-⌊⌋-id : ∀ {Γ n} (ts : Vec ᵍ⌊ Γ ⌋ n) → ren-vec ʰ⌊ ⊇id ⌋ ts ≡ ts
ren-vec-⌊⌋-id {Γ} ts rewrite id-⌊⌋-id Γ = ren-vec-id ts


data Var : Cx → Ty → Set where
  top : ∀ {Γ A} → Var (Γ , A) A
  pop : ∀ {Γ A B} → Var Γ A → Var (Γ , B) A

ⁱ⌊_⌋ : ∀ {Γ A} → Var Γ A → Fin ᵍ⌊ Γ ⌋
ⁱ⌊ top ⌋   = zero
ⁱ⌊ pop x ⌋ = suc ⁱ⌊ x ⌋

ren-var : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Var Γ A → Var Γ′ A
ren-var base     x       = x
ren-var (weak η) x       = pop (ren-var η x)
ren-var (lift η) top     = top
ren-var (lift η) (pop x) = pop (ren-var η x)

wk-var : ∀ {Γ A C} → Var Γ C → Var (Γ , A) C
wk-var = ren-var ⊇wk

wk*-var : ∀ {Γ C} → Var ∅ C → Var Γ C
wk*-var ()

ren-var-id : ∀ {Γ A} (x : Var Γ A) → ren-var ⊇id x ≡ x
ren-var-id top     = refl
ren-var-id (pop x) = cong pop (ren-var-id x)

ren-var-● : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (x : Var Γ A) →
              ren-var η′ (ren-var η x) ≡ ren-var (η′ ● η) x
ren-var-● base      η        x       = refl
ren-var-● (weak η′) η        x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (weak η) x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (lift η) top     = refl
ren-var-● (lift η′) (lift η) (pop x) = cong pop (ren-var-● η′ η x)

ren-fin-⌊⌋-var : ∀ {Γ Γ′ A} (η : Γ′ ⊇ Γ) (x : Var Γ A) →
                   ren-fin ʰ⌊ η ⌋ ⁱ⌊ x ⌋ ≡ ⁱ⌊ ren-var η x ⌋
ren-fin-⌊⌋-var base     x       = refl
ren-fin-⌊⌋-var (weak η) x       = cong suc (ren-fin-⌊⌋-var η x)
ren-fin-⌊⌋-var (lift η) top     = refl
ren-fin-⌊⌋-var (lift η) (pop x) = cong suc (ren-fin-⌊⌋-var η x)

x₀ : ∀ {Γ A} → Var (Γ , A) A
x₀ = top

x₁ : ∀ {Γ A B} → Var ((Γ , A) , B) A
x₁ = pop x₀

x₂ : ∀ {Γ A B C} → Var (((Γ , A) , B) , C) A
x₂ = pop x₁
