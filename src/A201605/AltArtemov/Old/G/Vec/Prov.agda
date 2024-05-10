module A201605.AltArtemov.Old.G.Vec.Prov where

open import A201605.AltArtemov.Old.G.Vec.True renaming (ᵗ⌊_⌋ to ᵗ⌊_⌋ᵀ) public


data Prov (Γ : Cx) : ∀ {n} → Vec ᵍ⌊ Γ ⌋ n → Ty → Set where
  var[_]  : ∀ n {A} (x : Var Γ A) →
              Prov Γ (VARs[ n ] ⁱ⌊ x ⌋) A
  lam[_]  : ∀ n {ts : Vec (suc ᵍ⌊ Γ ⌋) n} {A B} → Prov (Γ , A) ts B →
              Prov Γ (LAMs[ n ] ts) (A ⊃ B)
  app[_]  : ∀ n {ts us : Vec ᵍ⌊ Γ ⌋ n} {A B} → Prov Γ ts (A ⊃ B) → Prov Γ us A →
              Prov Γ (APPs[ n ] ts us) B
  pair[_] : ∀ n {ts us : Vec ᵍ⌊ Γ ⌋ n} {A B} → Prov Γ ts A → Prov Γ us B →
              Prov Γ (PAIRs[ n ] ts us) (A ∧ B)
  fst[_]  : ∀ n {ts : Vec ᵍ⌊ Γ ⌋ n} {A B} → Prov Γ ts (A ∧ B) →
              Prov Γ (FSTs[ n ] ts) A
  snd[_]  : ∀ n {ts : Vec ᵍ⌊ Γ ⌋ n} {A B} → Prov Γ ts (A ∧ B) →
              Prov Γ (SNDs[ n ] ts) B
  up[_]   : ∀ n {ts : Vec ᵍ⌊ Γ ⌋ n} {u A} → Prov Γ ts (u ∶ A) →
              Prov Γ (UPs[ n ] ts) (! u ∶ u ∶ A)
  down[_] : ∀ n {ts : Vec ᵍ⌊ Γ ⌋ n} {u A} → Prov Γ ts (u ∶ A) →
              Prov Γ (DOWNs[ n ] ts) A

ᵗ⌊_⌋ : ∀ {Γ n A} {ts : Vec ᵍ⌊ Γ ⌋ n} → Prov Γ ts A → Tm ᵍ⌊ Γ ⌋
ᵗ⌊ var[ n ] x ⌋      = VAR[ n ] ⁱ⌊ x ⌋
ᵗ⌊ lam[ n ] j ⌋      = LAM[ n ] ᵗ⌊ j ⌋
ᵗ⌊ app[ n ] j₁ j₂ ⌋  = APP[ n ] ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ pair[ n ] j₁ j₂ ⌋ = PAIR[ n ] ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ fst[ n ] j ⌋      = FST[ n ] ᵗ⌊ j ⌋
ᵗ⌊ snd[ n ] j ⌋      = SND[ n ] ᵗ⌊ j ⌋
ᵗ⌊ up[ n ] j ⌋       = UP[ n ] ᵗ⌊ j ⌋
ᵗ⌊ down[ n ] j ⌋     = DOWN[ n ] ᵗ⌊ j ⌋

true⇒ : ∀ {Γ A} → True Γ A → Prov Γ [] A
true⇒ (var x)      = var[ 0 ] x
true⇒ (lam j)      = lam[ 0 ] (true⇒ j)
true⇒ (app j₁ j₂)  = app[ 0 ] (true⇒ j₁) (true⇒ j₂)
true⇒ (pair j₁ j₂) = pair[ 0 ] (true⇒ j₁) (true⇒ j₂)
true⇒ (fst j)      = fst[ 0 ] (true⇒ j)
true⇒ (snd j)      = snd[ 0 ] (true⇒ j)
true⇒ (up j)       = up[ 0 ] (true⇒ j)
true⇒ (down j)     = down[ 0 ] (true⇒ j)

true⇐ : ∀ {Γ A} {ts : Vec ᵍ⌊ Γ ⌋ 0} → Prov Γ ts A → True Γ A
true⇐ (var[ .0 ] x)      = var x
true⇐ (lam[ .0 ] j)      = lam (true⇐ j)
true⇐ (app[ .0 ] j₁ j₂)  = app (true⇐ j₁) (true⇐ j₂)
true⇐ (pair[ .0 ] j₁ j₂) = pair (true⇐ j₁) (true⇐ j₂)
true⇐ (fst[ .0 ] j)      = fst (true⇐ j)
true⇐ (snd[ .0 ] j)      = snd (true⇐ j)
true⇐ (up[ .0 ] j)       = up (true⇐ j)
true⇐ (down[ .0 ] j)     = down (true⇐ j)

true⇒⇐-id : ∀ {Γ A} (j : True Γ A) → true⇐ (true⇒ j) ≡ j
true⇒⇐-id (var x)      = refl
true⇒⇐-id (lam j)      = cong lam (true⇒⇐-id j)
true⇒⇐-id (app j₁ j₂)  = cong₂ app (true⇒⇐-id j₁) (true⇒⇐-id j₂)
true⇒⇐-id (pair j₁ j₂) = cong₂ pair (true⇒⇐-id j₁) (true⇒⇐-id j₂)
true⇒⇐-id (fst j)      = cong fst (true⇒⇐-id j)
true⇒⇐-id (snd j)      = cong snd (true⇒⇐-id j)
true⇒⇐-id (up j)       = cong up (true⇒⇐-id j)
true⇒⇐-id (down j)     = cong down (true⇒⇐-id j)

true⇗ : ∀ {Γ A} (j : True Γ A) → Prov Γ [ ᵗ⌊ j ⌋ᵀ ] A
true⇗ (var x)      = var[ 1 ] x
true⇗ (lam j)      = lam[ 1 ] (true⇗ j)
true⇗ (app j₁ j₂)  = app[ 1 ] (true⇗ j₁) (true⇗ j₂)
true⇗ (pair j₁ j₂) = pair[ 1 ] (true⇗ j₁) (true⇗ j₂)
true⇗ (fst j)      = fst[ 1 ] (true⇗ j)
true⇗ (snd j)      = snd[ 1 ] (true⇗ j)
true⇗ (up j)       = up[ 1 ] (true⇗ j)
true⇗ (down j)     = down[ 1 ] (true⇗ j)

true⇙ : ∀ {Γ n A} {ts : Vec ᵍ⌊ Γ ⌋ n} → Prov Γ ts A → True Γ A
true⇙ (var[ n ] x)      = var x
true⇙ (lam[ n ] j)      = lam (true⇙ j)
true⇙ (app[ n ] j₁ j₂)  = app (true⇙ j₁) (true⇙ j₂)
true⇙ (pair[ n ] j₁ j₂) = pair (true⇙ j₁) (true⇙ j₂)
true⇙ (fst[ n ] j)      = fst (true⇙ j)
true⇙ (snd[ n ] j)      = snd (true⇙ j)
true⇙ (up[ n ] j)       = up (true⇙ j)
true⇙ (down[ n ] j)     = down (true⇙ j)

true⇗⇙-id : ∀ {Γ A} (j : True Γ A) → true⇙ (true⇗ j) ≡ j
true⇗⇙-id (var x)      = refl
true⇗⇙-id (lam j)      = cong lam (true⇗⇙-id j)
true⇗⇙-id (app j₁ j₂)  = cong₂ app (true⇗⇙-id j₁) (true⇗⇙-id j₂)
true⇗⇙-id (pair j₁ j₂) = cong₂ pair (true⇗⇙-id j₁) (true⇗⇙-id j₂)
true⇗⇙-id (fst j)      = cong fst (true⇗⇙-id j)
true⇗⇙-id (snd j)      = cong snd (true⇗⇙-id j)
true⇗⇙-id (up j)       = cong up (true⇗⇙-id j)
true⇗⇙-id (down j)     = cong down (true⇗⇙-id j)

prov⇗ : ∀ {Γ n A} {ts : Vec ᵍ⌊ Γ ⌋ n} (j : Prov Γ ts A) →
          Prov Γ (ᵗ⌊ j ⌋ ∷ ts) A
prov⇗ (var[ n ] x)      = var[ suc n ] x
prov⇗ (lam[ n ] j)      = lam[ suc n ] (prov⇗ j)
prov⇗ (app[ n ] j₁ j₂)  = app[ suc n ] (prov⇗ j₁) (prov⇗ j₂)
prov⇗ (pair[ n ] j₁ j₂) = pair[ suc n ] (prov⇗ j₁) (prov⇗ j₂)
prov⇗ (fst[ n ] j)      = fst[ suc n ] (prov⇗ j)
prov⇗ (snd[ n ] j)      = snd[ suc n ] (prov⇗ j)
prov⇗ (up[ n ] j)       = up[ suc n ] (prov⇗ j)
prov⇗ (down[ n ] j)     = down[ suc n ] (prov⇗ j)

prov⇙ : ∀ {n Γ A} {ts : Vec ᵍ⌊ Γ ⌋ (suc n)} (j : Prov Γ ts A) →
          Prov Γ (tail ts) A
prov⇙ {n} (var[ .(suc n) ] x)                = var[ n ] x
prov⇙ {n} (lam[ .(suc n) ] {ts} j)           rewrite tail-LAMs ts =
                                                lam[ n ] (prov⇙ j)
prov⇙ {n} (app[ .(suc n) ] {ts} {us} j₁ j₂)  rewrite tail-APPs ts us =
                                                app[ n ] (prov⇙ j₁) (prov⇙ j₂)
prov⇙ {n} (pair[ .(suc n) ] {ts} {us} j₁ j₂) rewrite tail-PAIRs ts us =
                                                pair[ n ] (prov⇙ j₁) (prov⇙ j₂)
prov⇙ {n} (fst[ .(suc n) ] {ts} j)           rewrite tail-FSTs ts =
                                                fst[ n ] (prov⇙ j)
prov⇙ {n} (snd[ .(suc n) ] {ts} j)           rewrite tail-SNDs ts =
                                                snd[ n ] (prov⇙ j)
prov⇙ {n} (up[ .(suc n) ] {ts} j)            rewrite tail-UPs ts =
                                                up[ n ] (prov⇙ j)
prov⇙ {n} (down[ .(suc n) ] {ts} j)          rewrite tail-DOWNs ts =
                                                down[ n ] (prov⇙ j)

prov⇗⇙-id : ∀ {Γ n A} {ts : Vec ᵍ⌊ Γ ⌋ n} (j : Prov Γ ts A) →
              prov⇙ (prov⇗ j) ≡ j
prov⇗⇙-id (var[ n ] x)      = refl
prov⇗⇙-id (lam[ n ] j)      = cong lam[ n ] (prov⇗⇙-id j)
prov⇗⇙-id (app[ n ] j₁ j₂)  = cong₂ app[ n ] (prov⇗⇙-id j₁) (prov⇗⇙-id j₂)
prov⇗⇙-id (pair[ n ] j₁ j₂) = cong₂ pair[ n ] (prov⇗⇙-id j₁) (prov⇗⇙-id j₂)
prov⇗⇙-id (fst[ n ] j)      = cong fst[ n ] (prov⇗⇙-id j)
prov⇗⇙-id (snd[ n ] j)      = cong snd[ n ] (prov⇗⇙-id j)
prov⇗⇙-id (up[ n ] j)       = cong up[ n ] (prov⇗⇙-id j)
prov⇗⇙-id (down[ n ] j)     = cong down[ n ] (prov⇗⇙-id j)

ren-prov : ∀ {Γ Γ′ n A} {ts : Vec ᵍ⌊ Γ ⌋ n} (η : Γ′ ⊇ Γ) → Prov Γ ts A →
             Prov Γ′ (ren-vec ʰ⌊ η ⌋ ts) A
ren-prov η (var[ n ] x)                rewrite ren-VARs {n} ʰ⌊ η ⌋ ⁱ⌊ x ⌋ |
                                               ren-fin-⌊⌋-var η x =
                                         var[ n ] (ren-var η x)
ren-prov η (lam[ n ] {ts} j)           rewrite ren-LAMs ʰ⌊ η ⌋ ts =
                                         lam[ n ] (ren-prov (lift η) j)
ren-prov η (app[ n ] {ts} {us} j₁ j₂)  rewrite ren-APPs ʰ⌊ η ⌋ ts us =
                                         app[ n ] (ren-prov η j₁) (ren-prov η j₂)
ren-prov η (pair[ n ] {ts} {us} j₁ j₂) rewrite ren-PAIRs ʰ⌊ η ⌋ ts us =
                                         pair[ n ] (ren-prov η j₁) (ren-prov η j₂)
ren-prov η (fst[ n ] {ts} j)           rewrite ren-FSTs ʰ⌊ η ⌋ ts =
                                         fst[ n ] (ren-prov η j)
ren-prov η (snd[ n ] {ts} j)           rewrite ren-SNDs ʰ⌊ η ⌋ ts =
                                         snd[ n ] (ren-prov η j)
ren-prov η (up[ n ] {ts} j)            rewrite ren-UPs ʰ⌊ η ⌋ ts =
                                         up[ n ] (ren-prov η j)
ren-prov η (down[ n ] {ts} j)          rewrite ren-DOWNs ʰ⌊ η ⌋ ts =
                                         down[ n ] (ren-prov η j)

wk-prov : ∀ {Γ n A C} {ts : Vec ᵍ⌊ Γ ⌋ n} → Prov Γ ts C →
              Prov (Γ , A) (wk-vec ts) C
wk-prov {Γ} rewrite sym (id-⌊⌋-id Γ) = ren-prov ⊇wk

wk*-prov : ∀ {Γ n C} {ts : Vec 0 n} → Prov ∅ ts C →
               Prov Γ (wk*-vec ts) C
wk*-prov {Γ} rewrite sym (to-⌊⌋-to Γ) = ren-prov ⊇to

v₀[_] : ∀ {Γ} n {A} → Prov (Γ , A) (VARs[ n ] i₀) A
v₀[ n ] = var[ n ] x₀

v₁[_] : ∀ {Γ} n {A B} → Prov ((Γ , A) , B) (VARs[ n ] i₁) A
v₁[ n ] = var[ n ] x₁

v₂[_] : ∀ {Γ} n {A B C} → Prov (((Γ , A) , B) , C) (VARs[ n ] i₂) A
v₂[ n ] = var[ n ] x₂

I[_] : ∀ {Γ} n {A} → Prov Γ (LAMs[ n ] (VARs[ n ] i₀)) (A ⊃ A)
I[ n ] = lam[ n ] v₀[ n ]

K[_] : ∀ {Γ} n {A B} → Prov Γ (LAMs[ n ] (LAMs[ n ] (VARs[ n ] i₁))) (A ⊃ B ⊃ A)
K[ n ] = lam[ n ] (lam[ n ] v₁[ n ])

S[_] : ∀ {Γ} n {A B C} →
         Prov Γ (LAMs[ n ] (LAMs[ n ] (LAMs[ n ]
                    (APPs[ n ] (APPs[ n ] (VARs[ n ] i₂) (VARs[ n ] i₀))
                               (APPs[ n ] (VARs[ n ] i₁) (VARs[ n ] i₀))))))
                ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S[ n ] = lam[ n ] (lam[ n ] (lam[ n ]
           (app[ n ] (app[ n ] v₂[ n ] v₀[ n ])
                     (app[ n ] v₁[ n ] v₀[ n ]))))

I≡I[0] : ∀ {Γ A} → true⇒ (I {Γ} {A}) ≡ I[ 0 ]
I≡I[0] = refl

⇗I≡I[1] : ∀ {Γ A} → true⇗ (I {Γ} {A}) ≡ I[ 1 ]
⇗I≡I[1] = refl

⇗⇗I≡I[2] : ∀ {Γ A} → prov⇗ (true⇗ (I {Γ} {A})) ≡ I[ 2 ]
⇗⇗I≡I[2] = refl
