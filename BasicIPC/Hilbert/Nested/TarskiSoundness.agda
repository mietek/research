module BasicIPC.Hilbert.Nested.TarskiSoundness where

open import BasicIPC.TarskiSemantics public
open import BasicIPC.Hilbert.Nested public


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = (eval t γ) (eval u γ)
eval ci        γ = id
eval ck        γ = const
eval cs        γ = ap
eval cpair     γ = _,_
eval cfst      γ = π₁
eval csnd      γ = π₂
eval tt        γ = ∙
