/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

/-!
# Affine Derived Quasicoherent Modules

This module records the derived equivalences and degree-zero cohomology comparison for
quasicoherent modules on an affine scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On an affine scheme, degree-zero cohomology after derived global sections is isomorphic to
the global sections of the degree-zero cohomology sheaf. -/
theorem affineGlobalSections_homologyZero (A : CommRingCat.{u})
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        ((affineGlobalSections A).obj E))
      ((AlgebraicGeometry.moduleSpecΓFunctor : (Spec A).Modules ⥤ ModuleCat A).obj
        (RingedSpace.ModuleDerived.cohomologySheaf E.obj 0)) := sorry

/-- Derived global sections on an affine scheme give an equivalence from derived modules with
quasicoherent homology to the derived category of modules over its coordinate ring. -/
instance affineGlobalSectionsIsEquivalence (A : CommRingCat.{u}) :
    Functor.IsEquivalence (affineGlobalSections A) := sorry

/-- Derived global sections on an affine scheme carry the canonical compatibility with shifts. -/
noncomputable instance affineGlobalSectionsCommShift (A : CommRingCat.{u}) :
    (affineGlobalSections A).CommShift ℤ := by
  change
    (((DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι ⋙
      RingedSpace.moduleDerivedGlobalSections (Spec A).toRingedSpace) ⋙
      ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso A).inv.hom).CommShift ℤ
  exact Functor.CommShift.comp _ _

/-- Derived global sections on an affine scheme preserve distinguished triangles. -/
instance affineGlobalSectionsIsTriangulated (A : CommRingCat.{u}) :
    (affineGlobalSections A).IsTriangulated := sorry

/-- For an affine scheme, the comparison from the ringed-space presentation of the derived
category of quasicoherent modules to derived modules with quasicoherent homology is an
equivalence. -/
instance affineRingedSpaceComparisonIsEquivalence (A : CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    Functor.IsEquivalence
      (DerivedCategory.CohomologyIn.Comparison.functor
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)) := sorry

/-- For an affine scheme, the canonical comparison from the derived category of quasicoherent
modules to derived modules with quasicoherent homology is an equivalence. -/
instance affineComparisonIsEquivalence (A : CommRingCat.{u}) :
    Functor.IsEquivalence (comparison (Spec A)) := sorry

/-- The affine comparison functor carries the canonical compatibility with shifts. -/
noncomputable instance affineComparisonCommShift (A : CommRingCat.{u}) :
    (comparison (Spec A)).CommShift ℤ := by
  change
    (((Equivalence.MapDerivedCategory.forwardExact
        (QCoh.ringedSpaceEquivalence (Spec A))).mapDerivedCategory) ⋙
      DerivedCategory.CohomologyIn.Comparison.functor
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).CommShift ℤ
  exact Functor.CommShift.comp _ _

/-- For an affine scheme, the canonical comparison from the derived category of quasicoherent
modules to derived modules with quasicoherent homology preserves distinguished triangles. -/
instance affineComparisonIsTriangulated (A : CommRingCat.{u}) :
    (comparison (Spec A)).IsTriangulated := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

namespace AlgebraicGeometry.Scheme.QCoh.Derived

/-- On an affine scheme, the derived coherator is naturally isomorphic to derived global
sections followed by restriction of scalars and the derived associated-module functor. -/
theorem affineCoherator_isomorphic (A : CommRingCat.{u}) :
    IsIsomorphic (coherator (Spec A))
      ((Scheme.Modules.ringedSpaceEquivalence (Spec A)).mapDerivedCategory.functor ⋙
        RingedSpace.moduleDerivedGlobalSections (Spec A).toRingedSpace ⋙
        ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso A).inv.hom ⋙
        (AlgebraicGeometry.tildeEquiv :
          ModuleCat A ≌ QCoh (Spec A)).mapDerivedCategory.functor) := sorry

end AlgebraicGeometry.Scheme.QCoh.Derived

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On an affine scheme, the derived coherator restricted to complexes with quasicoherent
cohomology is a quasi-inverse to the canonical comparison functor. -/
theorem affineCoherator_isQuasiInverse (A : CommRingCat.{u}) :
    (comparison (Spec A)).IsQuasiInverse
      ((DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι ⋙
        (Scheme.Modules.ringedSpaceEquivalence (Spec A)).mapDerivedCategory.inverse ⋙
        QCoh.Derived.coherator (Spec A)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
