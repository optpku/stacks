/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent.RingedSiteComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.ExtPresentation
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open SheafOfModules.RingedSite
open scoped DerivedExt
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Thickening
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) [Flat f]
-- Local instance justification (defeq pin): all Ext and presentation maps use the standard derived quotient at the independent coefficient universe.
attribute [local instance] HasDerivedCategory.standard

/-- Ext¹ of the ringed-site naive cotangent complex with pulled conormal coefficients. -/
abbrev ringedExtOne := Ext⁽(1 : ℤ)⁾(
  DerivedCategory.Q.obj (NaiveCotangent.obj (commInverseImageStructureSheaf f)
    (Under.mk (commInverseImageStructureSheafMap f))),
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor X.Modules 0).obj (pulledConormal t f)))

/-- Transport the source Ext¹ class by the explicit polynomial/sheafification comparison. -/
def toRingedExtOne (ξ : extOneNL t f) : ringedExtOne t f :=
  (DerivedCategory.Q.mapIso (GeometricNL.complexIso f)).inv ≫ ξ

/-- Transport back along the forward map of the same comparison. -/
def fromRingedExtOne (ξ : ringedExtOne t f) : extOneNL t f :=
  (DerivedCategory.Q.mapIso (GeometricNL.complexIso f)).hom ≫ ξ

/-- Transport to the ringed-site Ext¹ group and back is the identity. -/
@[simp] theorem from_toRingedExtOne (ξ : extOneNL t f) :
    fromRingedExtOne t f (toRingedExtOne t f ξ) = ξ := by
  exact (DerivedCategory.Q.mapIso (GeometricNL.complexIso f)).hom_inv_id_assoc ξ

/-- Transport to the geometric Ext¹ group and back is the identity. -/
@[simp] theorem to_fromRingedExtOne (ξ : ringedExtOne t f) :
    toRingedExtOne t f (fromRingedExtOne t f ξ) = ξ := by
  exact (DerivedCategory.Q.mapIso (GeometricNL.complexIso f)).inv_hom_id_assoc ξ

/-- Select a genuine locally surjective presentation of the transported geometric class. -/
def geometricExtOnePresentation (ξ : extOneNL t f) :=
  NaiveCotangent.extOnePresentation.{u + 1, u, u}
    (commInverseImageStructureSheafMap f) (pulledConormal t f) (toRingedExtOne t f ξ)

end AlgebraicGeometry.AlgebraicSpace.Thickening
