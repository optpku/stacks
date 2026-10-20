/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.PolynomialAugmentation
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Point

/-!
# Derived change of rings on the polynomial site

Derived extension of scalars from the polynomial structure sheaf to the constant
target ring preserves additive derived lower shriek to a point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite.Hom
open scoped CategoryTheory

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [hColimits : HasColimitsOfShape (Algebra.PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u + 1}]
variable [hDerived : Functor.HasLeftDerivedFunctor
    (categoryOverPointColimitToDerived (Algebra.PolynomialSite A B) AddCommGrpCat.{u + 1})
    (HomotopyCategory.quasiIso ((Algebra.PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))]

/-- Additive derived lower shriek of modules over the polynomial structure sheaf. -/
noncomputable abbrev lowerShriek :
    ModuleDerived.{u + 1} (ringedSite A B) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  @DerivedPoint.lowerShriek.{u + 1, u + 1, u, u + 1} (ringedSite A B)
    inferInstance inferInstance inferInstance
    sheafToPresheaf_bot_preservesFiniteColimits hColimits hDerived

/-- Additive derived lower shriek of modules over the constant target ring sheaf. -/
noncomputable abbrev lowerShriekConstant :
    ModuleDerived.{u + 1} (constantRingedSite A B) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  @DerivedPoint.lowerShriek.{u + 1, u + 1, u, u + 1} (constantRingedSite A B)
    inferInstance inferInstance inferInstance
    sheafToPresheaf_bot_preservesFiniteColimits hColimits hDerived

/-- Derived extension of scalars along the augmentation from the polynomial
structure sheaf to the constant target ring sheaf. -/
noncomputable abbrev changeOfRings :
    ModuleDerived.{u + 1} (ringedSite A B) ⥤
      ModuleDerived.{u + 1} (constantRingedSite A B) :=
  DerivedPoint.Chaotic.Comm.tensor.{u + 1, u + 1, u, u + 1} (structureSheafMapLift A B)

/-- The derived object with a polynomial structure-sheaf module in degree zero. -/
noncomputable abbrev single (F : RingedSite.ModuleCat.{u + 1} (ringedSite A B)) :
    ModuleDerived.{u + 1} (ringedSite A B) :=
  (@DerivedCategory.singleFunctor (RingedSite.ModuleCat.{u + 1} (ringedSite A B))
      inferInstance inferInstance
      (moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (ringedSite A B))
      (0 : ℤ)).obj F

/-- The augmentation-induced map from the derived lower shriek of the structure
sheaf to that of the constant target ring sheaf. -/
noncomputable abbrev unitComparison :=
  DerivedPoint.Chaotic.Comm.unitComparison (structureSheafMapLift A B)

/-- The augmentation induces an isomorphism on the derived lower shriek of the
unit module. -/
instance structureSheafMap_unitComparison_isIso : IsIso (unitComparison A B) :=
  sorry

/-- Derived extension of scalars along the polynomial augmentation preserves
additive derived lower shriek for every derived module. -/
theorem lowerShriek_changeOfRings (K : ModuleDerived.{u + 1} (ringedSite A B)) :
    IsIsomorphic ((lowerShriek A B).obj K)
      ((lowerShriekConstant A B).obj ((changeOfRings A B).obj K)) :=
  sorry

/-- Derived extension of scalars along the polynomial augmentation preserves
additive derived lower shriek for every module placed in degree zero. -/
theorem lowerShriek_changeOfRings_obj
    (F : RingedSite.ModuleCat.{u + 1} (ringedSite A B)) :
    IsIsomorphic ((lowerShriek A B).obj (single A B F))
      ((lowerShriekConstant A B).obj ((changeOfRings A B).obj (single A B F))) :=
  lowerShriek_changeOfRings A B (single A B F)

end CommAlgCat.Over.Polynomial.Site
