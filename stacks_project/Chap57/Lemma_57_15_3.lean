/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap57.Definition_57_15_1_Kernel
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.RelativeEquivalence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 57.15.3: if `K` is the Fourier--Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, and `g : S' ⟶ S` is a morphism of
schemes, then the derived pullback of `K` along the product comparison
`X₁ ×_{S'} Y₁ ⟶ X ×_S Y`, with `X₁ = S' ×_S X` and `Y₁ = S' ×_S Y`, is
the Fourier--Mukai kernel of a relative equivalence from `X₁` to `Y₁`
over `S'`. -/
@[stacks 0G0K] #check
  (FourierMukaiObject.instIsRelativeEquivalenceKernel_modulePullback :
    ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace),
    [FourierMukaiObject.IsRelativeEquivalenceKernel K] →
    FourierMukaiObject.IsRelativeEquivalenceKernel
      (FourierMukaiObject.modulePullbackKernel g K))
