/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.IndSmooth.Prod
public import ReasLib.RingTheory.Regular.RingMap

@[expose] public section

universe u₁ v₁ u₂ v₂

/- Lemma 16.8.2: PT is preserved by binary products for two regular maps of
Noetherian rings as in Situation 16.8.1.  The shared closure theorem itself
does not require the ambient Noetherian or regularity assumptions. -/
@[stacks 07F3] #check
  fun {R₁ : Type u₁} {Λ₁ : Type v₁} {R₂ : Type u₂} {Λ₂ : Type v₂}
    [CommRing R₁] [CommRing Λ₁] [CommRing R₂] [CommRing Λ₂]
    [IsNoetherianRing R₁] [IsNoetherianRing Λ₁]
    [IsNoetherianRing R₂] [IsNoetherianRing Λ₂]
    (f₁ : R₁ →+* Λ₁) (f₂ : R₂ →+* Λ₂)
    (_ : f₁.Regular) (_ : f₂.Regular)
    (hf₁ : f₁.IndSmooth) (hf₂ : f₂.IndSmooth) ↦
      RingHom.IndSmooth.prodMap hf₁ hf₂

#check @RingHom.IndSmooth.prodMap
