/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.DimensionOne

/-!
# Structure sheaf surjectivity under base change

This module records preservation of local surjectivity of the structure-sheaf
pushforward map under arbitrary base change in relative dimension at most one.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

variable {X Y X' Y' : Scheme.{u}}

/-- For a proper morphism with fibers of dimension at most one and vanishing first
cohomology of their structure sheaves, local surjectivity of the structure-sheaf
pushforward map is preserved by every base change. -/
theorem baseChange_structureSheafMap_isLocallySurjective
    (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hH1 : ∀ y : Y,
      IsZero (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))
    [Sheaf.IsLocallySurjective
      (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) :
    Sheaf.IsLocallySurjective
      (RingedSpace.Hom.commRingSheafPushforwardMap f'.toShHom) := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
