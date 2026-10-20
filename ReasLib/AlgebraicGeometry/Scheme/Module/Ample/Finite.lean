/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.SerreCriterion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-!
# Ampleness and finite morphisms

This file relates ampleness of an invertible scheme module to ampleness of its pullback along a
finite surjective morphism between schemes proper over a Noetherian affine base.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- An invertible module on a scheme proper over a Noetherian affine base is ample if and only if
its pullback along a finite surjective morphism from another proper scheme is ample. -/
@[stacks 0B5V]
theorem isAmple_iff_pullback_isAmple_of_isFinite_surjective_properOver
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
    [IsProper (X ↘ Spec (CommRingCat.of R))] [IsProper (Y ↘ Spec (CommRingCat.of R))]
    (f : Y ⟶ X) [IsFinite f] [Surjective f]
    (L : X.Modules) [Invertible L] :
    IsAmple L ↔ IsAmple ((Scheme.Modules.pullback f).obj L) := sorry

end AlgebraicGeometry.Scheme.Modules
