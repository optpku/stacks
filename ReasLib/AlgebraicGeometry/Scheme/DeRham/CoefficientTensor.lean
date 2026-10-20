/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DifferentialGradedAlgebra
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open RingedSite.Hom
-- Local instance justification (defeq pin): all tensor expressions use the canonical derived category of the coefficient sheaf presentation.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.DeRham.CanonicalTensor
variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The ordinary tensor bifunctor of coefficient-module complexes admits a total
left derived functor, computed by resolving both entries by K-flat module complexes. -/
theorem hasCoefficientDerivedTensor :
    DerivedCategory.DerivedTensor.Bifunctor.Has
      (C := RingedSpace.DeRham.Modules p.toLRSHom.toShHom) := sorry

-- Local instance justification (defeq pin): use the fixed total-left-derived tensor of this coefficient category, whose existence is the named K-flat resolution obligation above.
attribute [local instance] hasCoefficientDerivedTensor

/-- The coefficient-sheaf derived tensor is the total left derived functor of
ordinary totalized tensor, with its canonical derivation counit. -/
abbrev tensor :
    (ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ×
      ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) ⥤
      ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) :=
  DerivedCategory.DerivedTensor.Bifunctor.functor

/-- Derived de Rham multiplication is the derived-to-ordinary tensor counit,
followed by localization of the extended wedge multiplication. -/
def multiplication :
    (tensor p).obj (DerivedPushforward.derivedComplex p, DerivedPushforward.derivedComplex p) ⟶
      DerivedPushforward.derivedComplex p :=
  DerivedCategory.DerivedTensor.Bifunctor.counitAppOfComplex
      (extendedDeRhamComplex p) (extendedDeRhamComplex p) ≫
    DerivedCategory.Q.map (extendedWedge p) ≫
    (DerivedCategory.quotientCompQhIso
      (RingedSpace.DeRham.Modules p.toLRSHom.toShHom)).inv.app (extendedDeRhamComplex p)

/-- Fixed-factor coefficient tensor has pointwise left-derived values computed by K-flat resolutions. -/
theorem hasFixedRightDerivedTensor :
    DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.DeRham.Modules p.toLRSHom.toShHom) := sorry

/-- Fixing one argument of the two-variable tensor retains the specified one-variable
derived universal property and its counit. -/
theorem fixedRightCompatible
    (E : ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) :
    DerivedCategory.DerivedTensor.Bifunctor.Right.Compatible E := sorry

-- Local instance justification (defeq pin): compare the two canonical derivations using their specified counits, rather than choosing an unrelated tensor isomorphism.
attribute [local instance] hasFixedRightDerivedTensor fixedRightCompatible

/-- Shift of the first factor in derived tensor, constructed by comparison with the
canonical fixed-right total-derived functor and its derived shift structure. -/
def shiftFirst
    (K E : ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) (n : ℤ) :
    (tensor p).obj (K⟦n⟧, E) ≅ ((tensor p).obj (K, E))⟦n⟧ :=
  ((DerivedCategory.DerivedTensor.Bifunctor.Right.iso E).app (K⟦n⟧)).symm ≪≫
    ((DerivedCategory.DerivedTensor.Right.functor E).commShiftIso n).app K ≪≫
    (shiftFunctor _ n).mapIso ((DerivedCategory.DerivedTensor.Bifunctor.Right.iso E).app K)

end AlgebraicGeometry.Scheme.DeRham.CanonicalTensor
