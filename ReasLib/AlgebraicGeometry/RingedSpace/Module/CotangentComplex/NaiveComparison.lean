/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.NaiveComparison

/-!
# Comparison with the naive cotangent complex of a morphism of ringed spaces

The canonical comparison identifies the naive cotangent complex with the good
truncation of the cotangent complex in degrees at least `-1`.
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- The canonical cochain map from the cotangent complex of a morphism of ringed spaces
to its naive cotangent complex. -/
noncomputable abbrev toNaive (f : X ⟶ Y) :
    cotangentComplex f ⟶ naiveCotangent f :=
  CotangentComplex.toNaive _ (inverseImageStructureSheafUnder f)

/-- The canonical comparison of cotangent complexes is a quasi-isomorphism after good
truncation in degrees at least `-1`. -/
instance toNaive_truncGE_quasiIso (f : X ⟶ Y) :
    QuasiIso (CochainComplex.truncGEMap (toNaive f) (-1)) :=
  CotangentComplex.toNaive_truncGE_quasiIso _ (inverseImageStructureSheafUnder f)

/-- The naive cotangent complex of a morphism of ringed spaces is concentrated in degrees
at least `-1`. -/
instance naiveCotangent_isGE_negOne (f : X ⟶ Y) :
    (naiveCotangent f).IsGE (-1) :=
  CotangentComplex.naiveObj_isGE_negOne _ (inverseImageStructureSheafUnder f)

end AlgebraicGeometry.RingedSpace
