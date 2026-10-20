/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.SubmoduleComplex

/-!
# Lemma 15.102.6

@stack 0G3N
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.IdealPower.SubmoduleComplex.Positive
open Opposite

universe u

/- Lemma 15.102.6 (0G3N): for a Noetherian ring `A`, an ideal `I`, and a bounded
complex `M` of finite `A`-modules, the canonical comparison from
`((I ^ (n + 1))[0] ⊗ᴸ M)ₙ` to `(I ^ (n + 1) M)ₙ` is an isomorphism of sequential
pro-objects.  The concrete complexes, tensor map, and comparison are owned by
`ReasLib`; this file is only the source-facing boundary.

The shared owner uses the two-variable derived tensor bifunctor, so no
chapter-local monoidal instance or fixed-right model is needed. -/
@[stacks 0G3N "Lemma 15.102.6"]
#check @comparison_isIso

/- Keep the source hypotheses visible at the chapter boundary. -/
#check fun {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) ↦
  comparison_isIso I M hboundedBelow hboundedAbove hfinite

/- The source-facing systems and concrete comparison are available independently. -/
#check @complex
#check @complexStep
#check @stage
#check @step
#check @system
#check @singleStage
#check @standardStage
#check @standardSystem
#check @tensorMap
#check @comparisonApp
#check @comparisonNatTrans
#check @comparison
#check @CategoryTheory.Pro.SequentialHom.ofNatTrans
#check @CategoryTheory.Pro.SequentialHom.toHom
