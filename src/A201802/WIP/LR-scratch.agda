module A201802.WIP.LR-scratch where

--------------------------------------------------------------------------------


{-
-- Value non-reduction.
vnr : ∀ {g} → {M : Val g} {M′ : Term g}
            → ¬ (Val.term M ↦ M′)
vnr {M = val (LAM M) {{iv-LAM}}}   M↦M′ = {!!}
vnr {M = val TRUE    {{iv-TRUE}}}  M↦M′ = {!!}
vnr {M = val FALSE   {{iv-FALSE}}} M↦M′ = {!!}


-- Determinism.
uniq↦ : ∀ {g} → {M M′₁ M′₂ : Term g}
               → M ↦ M′₁ → M ↦ M′₂
               → M′₁ ≡ M′₂
uniq↦ red-APP-LAM         M↦M′₂ = {!!}
uniq↦ red-IF-TRUE         M↦M′₂ = {!!}
uniq↦ red-IF-FALSE        M↦M′₂ = {!!}
uniq↦ (red-cong E M↦M′₁) M↦M′₂ = {!!}

uniq⤅ : ∀ {g} → {M M′₁ M′₂ : Term g}
               → M ⤅ M′₁ → M ⤅ M′₂
               → M′₁ ≡ M′₂
uniq⤅ done                   done                   = refl
uniq⤅ done                   (step M↦M″₂ M″₂⤅M′₂) = {!!}
uniq⤅ (step M↦M″₁ M″₁⤅M′₁) done                   = {!!}
uniq⤅ (step M↦M″₁ M″₁⤅M′₁) (step M↦M″₂ M″₂⤅M′₂) = {!!}
-}



-- foo : ∀ {g} → {M M′ : Term g}
--             → M ⤅ M′
--             → M ≡ M′ ⊎ Σ (Term g) (\ M″ → M ↦ M″ × M″ ⤅ M′)
-- foo done                = inj₁ refl
-- foo (step M↦M″ M″⤅M′) = inj₂ (_ , (M↦M″ , M″⤅M′))


-- inj-VAR : ∀ {g} → {I₁ I₂ : Fin g}
--                 → VAR I₁ ≡ VAR I₂
--                 → I₁ ≡ I₂
-- inj-VAR refl = refl

-- inj-LAM : ∀ {g} → {M₁ M₂ : Term (suc g)}
--                 → LAM M₁ ≡ LAM M₂
--                 → M₁ ≡ M₂
-- inj-LAM refl = refl

-- inj-APP₁ : ∀ {g} → {M₁ M₂ N : Term g}
--                  → APP M₁ N ≡ APP M₂ N
--                  → M₁ ≡ M₂
-- inj-APP₁ refl = refl

-- inj-APP₂ : ∀ {g} → {M N₁ N₂ : Term g}
--                  → APP M N₁ ≡ APP M N₂
--                  → N₁ ≡ N₂
-- inj-APP₂ refl = refl

-- inj-IF₁ : ∀ {g} → {M₁ M₂ N O : Term g}
--                 → IF M₁ N O ≡ IF M₂ N O
--                 → M₁ ≡ M₂
-- inj-IF₁ refl = refl

-- inj-IF₂ : ∀ {g} → {M N₁ N₂ O : Term g}
--                 → IF M N₁ O ≡ IF M N₂ O
--                 → N₁ ≡ N₂
-- inj-IF₂ refl = refl

-- inj-IF₃ : ∀ {g} → {M N O₁ O₂ : Term g}
--                 → IF M N O₁ ≡ IF M N O₂
--                 → O₁ ≡ O₂
-- inj-IF₃ refl = refl


-- inj[]₁ : ∀ {g} → {E₁ E₂ : EvCx g} {M : Term g}
--                → E₁ [ M ] ≡ E₂ [ M ]
--                → E₁ ≡ E₂
-- inj[]₁ {E₁ = E₁} {E₂} p = {!!}

-- inj[]₂ : ∀ {g} → {M₁ M₂ : Term g}
--                → (E : EvCx g) → E [ M₁ ] ≡ E [ M₂ ]
--                → M₁ ≡ M₂
-- inj[]₂ ec-[]            refl = refl
-- inj[]₂ (ec-fun-APP E N) p    = inj[]₂ E (inj-APP₁ p)
-- inj[]₂ (ec-APP-arg M E) p    = inj[]₂ E (inj-APP₂ p)
-- inj[]₂ (ec-IF E N O)    p    = inj[]₂ E (inj-IF₁ p)


-- uniq[] : ∀ {g} → {M M′₁ M′₂ : Term g}
--                → (E : EvCx g) → E [ M ] ≡ M′₁ → E [ M ] ≡ M′₂
--                → M′₁ ≡ M′₂
-- uniq[] E refl refl = refl


-- uniq↦ : ∀ {g} → {M M′₁ M′₂ : Term g}
--                → M ↦ M′₁ → M ↦ M′₂
--                → M′₁ ≡ M′₂
-- uniq↦ (red-APP-LAM {{refl}})               (red-APP-LAM {{refl}})               = refl
-- uniq↦ red-IF-TRUE                          red-IF-TRUE                          = refl
-- uniq↦ red-IF-FALSE                         red-IF-FALSE                         = refl
-- uniq↦ (red-cong E₁ M↦M′₁ {{p₁}} {{refl}}) (red-APP-LAM {{refl}})               = {!!}
-- uniq↦ (red-cong E₁ M↦M′₁ {{p₁}} {{refl}}) red-IF-TRUE                          = {!!}
-- uniq↦ (red-cong E₁ M↦M′₁ {{p₁}} {{refl}}) red-IF-FALSE                         = {!!}
-- uniq↦ (red-APP-LAM {{refl}})               (red-cong E₂ M↦M′₂ {{p₂}} {{refl}}) = {!!}
-- uniq↦ red-IF-TRUE                          (red-cong E₂ M↦M′₂ {{p₂}} {{refl}}) = {!!}
-- uniq↦ red-IF-FALSE                         (red-cong E₂ M↦M′₂ {{p₂}} {{refl}}) = {!!}
-- uniq↦ (red-cong E₁ M↦M′₁ {{p₁}} {{refl}}) (red-cong E₂ M↦M′₂ {{p₂}} {{refl}}) = {!uniq↦ M↦M′₁ M↦M′₂!}


-- bar : ∀ {g} → {M M′ M″ : Term g}
--             → M ↦ M′ → M ⤅ M″ → {{_ : ¬ (M ≡ M″)}}
--             → M′ ⤅ M″
-- bar M↦M′ done                {{p}} = refl ↯ p
-- bar M↦M′ (step M↦M° M°⤅M″) = {!!}


-- oops : ∀ {g} → {M M′ M″ : Term g}
--              → M ↦ M′ → M ⤅ M″
--              → M′ ⤅ M″
-- oops M↦M′ done                = {!!}
-- oops M↦M′ (step M↦M° M°⤅M″) = {!!}


-- --------------------------------------------------------------------------------


-- red-cong-APP-LAM : ∀ {g} → {M N N′ : Term g} {M′ : Term (suc g)}
--                          → M ⤅ LAM M′ → N ⤅ N′
--                          → APP (LAM M′) N ⤅ CUT N′ M′
-- red-cong-APP-LAM M⤅LAM-M′ N⤅N′ = {!!}


-- halt-APP : ∀ {g} → {M N : Term g} {M′ : Term (suc g)}
--                  → M ⤅ LAM M′ → M′ ⇓ → N ⇓
--                  → APP M N ⇓
-- halt-APP M⤅LAM-M′ M′⇓ N⇓ = {!!}




-- -- SNs : ∀ {g} → Vals 0 g → Types g → Set
-- -- SNs (vals ∙)                       ∙       = ⊤
-- -- SNs (vals (τ , M) {{av-τ , iv-M}}) (Γ , A) = SNs (vals τ {{av-τ}}) Γ × SN M A


-- -- derps : ∀ {g} → {τ : Vals 0 g} {Γ : Types g}
-- --               → SNs τ Γ
-- --               → ∙ ⊢ Vals.terms τ ⦂ Γ all
-- -- derps {τ = vals ∙}                       {∙}     ∙       = ∙
-- -- derps {τ = vals (τ , M) {{av-τ , iv-M}}} {Γ , A} (σ , s) = derps σ , derp s


-- -- tp-SUB : ∀ {g M A} → {τ : Vals 0 g} {Γ : Types g}
-- --                    → SNs τ Γ → Γ ⊢ M ⦂ A
-- --                    → ∙ ⊢ SUB (Vals.terms τ) M ⦂ A
-- -- tp-SUB σ 𝒟 = sub (derps σ) 𝒟


-- -- sn-lem₁ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M′ A
-- --                      → SN M A
-- -- sn-lem₁ {𝔹}     M↦M′ 𝒟 (𝒟′ , (M″ , M′⤅M″))     = 𝒟 , (M″ , step M↦M′ M′⤅M″)
-- -- sn-lem₁ {A ⊃ B} M↦M′ 𝒟 (𝒟′ , (M″ , M′⤅M″) , f) =
-- --   𝒟 , (M″ , step M↦M′ M′⤅M″) , (\ s → sn-lem₁ (red-cong (ec-fun-APP ec-[] _) M↦M′)
-- --                                                  (app 𝒟 (derp s)) (f s))


-- -- sn-lem₂ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M A
-- --                      → SN M′ A
-- -- sn-lem₂ {𝔹}     M↦M′ 𝒟 (_ , (M″ , M⤅M″))     = {!!}
-- -- sn-lem₂ {A ⊃ B} M↦M′ 𝒟 (_ , (M″ , M⤅M″) , f) = {!!}


-- -- sn-SUB : ∀ {g M A} → {τ : Vals 0 g} {Γ : Types g}
-- --                    → SNs τ Γ → Γ ⊢ M ⦂ A
-- --                    → SN (SUB (Vals.terms τ) M) A
-- -- sn-SUB σ (var i)    = {!!}
-- -- sn-SUB σ (lam 𝒟)    = {!!}
-- -- sn-SUB σ (app 𝒟 ℰ)  = {!!}
-- -- sn-SUB σ true       = true , (val TRUE , done)
-- -- sn-SUB σ false      = false , (val FALSE , done)
-- -- sn-SUB σ (if 𝒟 ℰ ℱ) = {!!}


-- -- --------------------------------------------------------------------------------
