/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.HomologyZero
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials

/-!
# Degree-zero homology of a ringed-space cotangent complex

The degree-zero homology of the cotangent complex of a morphism of ringed spaces
is canonically identified with its sheaf of relative differentials.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X S : RingedSpace.{u}}

/-- The canonical comparison morphism from degree-zero homology to relative differentials. -/
noncomputable abbrev homologyZeroMap (f : X ⟶ S) :
    (cotangentComplex f).homology 0 ⟶ Hom.differentials f :=
  SheafOfModules.RingedSite.CotangentComplex.homologyZeroMap
    (inverseImageStructureSheafHomComm f)

/-- The canonical isomorphism from degree-zero homology to relative differentials. -/
noncomputable abbrev homologyZeroIso (f : X ⟶ S) :
    (cotangentComplex f).homology 0 ≅ Hom.differentials f :=
  SheafOfModules.RingedSite.CotangentComplex.homologyZeroIso
    (inverseImageStructureSheafHomComm f)

/-- The degree-zero comparison morphism is an isomorphism. -/
instance homologyZeroMap_isIso (f : X ⟶ S) : IsIso (homologyZeroMap f) :=
  SheafOfModules.RingedSite.CotangentComplex.homologyZeroMap_isIso
    (inverseImageStructureSheafHomComm f)

end AlgebraicGeometry.RingedSpace
