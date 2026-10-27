/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.NaiveDifferentials
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import Mathlib.Algebra.Homology.Single

/-!
# Derived pullback of differential sheaves

The total left derived scalar-extension functor has its canonical cochain
counit. Flatness of polynomial differentials identifies that counit with the
underived scalar extension in degree zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

variable (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]

/-- Derived inverse image `Li^*` along `i♯ : O ⟶ underline{O}_X`, as the total left
derived functor of same-site extension of scalars. -/
def derivedInverseImage :
    DerivedCategory (SheafOfModules.{u + 1} (structureSheaf Λ X)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (inverseImageStructureSheaf Λ X)) :=
  @Functor.LeftDerived.Homotopy.functor.{u + 2, u + 1, u + 2, u + 2, u + 1, u + 2} _ _ _ _ _ _ _ _
    (SheafOfModules.RingedSite.extendAlong.{u + 1, u, u + 1}
      (J := topology Λ X) (structureSheafMapComm Λ X))
    (SheafOfModules.ChangeOfRings.extendScalars_additive.{u + 1, u, u + 1, u + 1}
      (SheafOfModules.RingedSite.ringSheafMap.{u + 1, u, u + 1} (structureSheafMapComm Λ X)))
    (RingedSite.Hom.modulePullback.DerivedCategory.hasLeftDerived.{u + 1, u + 1, u, u + 1, u, u + 1} (RingedSite.SameSite.hom (structureSheafMap Λ X)))

/-- The cochain counit compares derived scalar extension of differentials with
their sheaf-level scalar extension in degree zero. -/
def derivedPullbackToOmega :
    (derivedInverseImage Λ X).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u + 1} (structureSheaf Λ X)) (0 : ℤ)).obj
          (omegaSheaf Λ X)) ⟶
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u + 1} (inverseImageStructureSheaf Λ X)) (0 : ℤ)).obj
        (omegaPullback Λ X) :=
  (@Functor.LeftDerived.Homotopy.cochainCounit.{u + 2, u + 1, u + 2, u + 2, u + 1, u + 2} _ _ _ _ _ _ _ _
      (SheafOfModules.RingedSite.extendAlong.{u + 1, u, u + 1}
        (J := topology Λ X) (structureSheafMapComm Λ X))
      (SheafOfModules.ChangeOfRings.extendScalars_additive.{u + 1, u, u + 1, u + 1}
        (SheafOfModules.RingedSite.ringSheafMap.{u + 1, u, u + 1} (structureSheafMapComm Λ X)))
      (RingedSite.Hom.modulePullback.DerivedCategory.hasLeftDerived.{u + 1, u + 1, u, u + 1, u, u + 1} (RingedSite.SameSite.hom (structureSheafMap Λ X)))).app
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (omegaSheaf Λ X)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          (SheafOfModules.RingedSite.extendAlong.{u + 1, u, u + 1} (J := topology Λ X) (structureSheafMapComm Λ X))
          (ComplexShape.up ℤ) 0).hom.app (omegaSheaf Λ X))

/-- Because `Ω_{O / underline{Λ}}` is `O`-flat on polynomial algebras, the comparison
`Li^* omegaSheaf ⟶ omegaPullback` is an isomorphism in `D(underline{O}_X)`. -/
instance derivedPullbackToOmega_isIso : IsIso (derivedPullbackToOmega Λ X) :=
  sorry

/-- The canonical isomorphism from derived scalar extension of the flat
differential sheaf to its underived extension of scalars. -/
def derivedPullbackIso :
    (derivedInverseImage Λ X).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u + 1} (structureSheaf Λ X)) (0 : ℤ)).obj
          (omegaSheaf Λ X)) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u + 1} (inverseImageStructureSheaf Λ X)) (0 : ℤ)).obj
        (omegaPullback Λ X) :=
  asIso (derivedPullbackToOmega Λ X)

/-- The forward map of `derivedPullbackIso` is `derivedPullbackToOmega`. -/
theorem derivedPullbackIso_hom :
    (derivedPullbackIso Λ X).hom = derivedPullbackToOmega Λ X := rfl

end AlgebraicGeometry.Scheme.CotangentSite
