/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion

/-!
# Flat finitely presented relative quasi-regular immersions

A relative quasi-regular immersion over a flat locally finitely presented morphism is regular,
and remains regular after arbitrary base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativeQuasiRegularImmersion

variable {X S Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

/-- A relative quasi-regular immersion over a flat locally finitely presented morphism is a
regular immersion. -/
theorem isRegularImmersion_of_flat_locallyOfFinitePresentation
    [Flat f] [LocallyOfFinitePresentation f] [RelativeQuasiRegularImmersion f i] :
    IsRegularImmersion i := sorry

/-- The immersion obtained from a relative quasi-regular immersion by arbitrary base change is
regular when the ambient morphism is flat and locally of finite presentation. -/
instance isRegularImmersion_pullback_snd_of_flat_locallyOfFinitePresentation
    {S' : Scheme.{u}} [Flat f] [LocallyOfFinitePresentation f]
    [RelativeQuasiRegularImmersion f i] (g : S' ⟶ S) :
    IsRegularImmersion (pullback.snd i (pullback.fst f g)) := sorry

end AlgebraicGeometry.RelativeQuasiRegularImmersion
