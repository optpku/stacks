/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Cotangent complexes of morphisms of ringed spaces

This module specializes the sheaf-level cotangent complex to the canonical
inverse-image structure-sheaf morphism of a morphism of ringed spaces.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X S : RingedSpace.{u}}

/-- The cotangent complex of a morphism of ringed spaces, obtained by applying the
sheaf-level cotangent-complex construction to its inverse-image structure-sheaf map. -/
noncomputable abbrev cotangentComplex (f : X ⟶ S) :
    CochainComplex X.Modules ℤ :=
  SheafOfModules.RingedSite.CotangentComplex.obj _
    (CategoryTheory.Under.mk
      (AlgebraicGeometry.RingedSpace.Hom.inverseImageStructureSheafHomComm f))

/-- The notation `L[f]` for the cotangent complex of a morphism of ringed spaces. -/
scoped[AlgebraicGeometry] notation:max "L[" f "]" =>
  RingedSpace.cotangentComplex f

/-- The cotangent complex unfolds to the sheaf-level construction on the canonical
inverse-image structure-sheaf morphism. -/
theorem cotangentComplex_eq (f : X ⟶ S) :
    cotangentComplex f =
      SheafOfModules.RingedSite.CotangentComplex.obj _
        (CategoryTheory.Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.inverseImageStructureSheafHomComm f)) := sorry

end AlgebraicGeometry.RingedSpace
