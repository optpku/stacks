/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Support

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open AlgebraicGeometry
open CategoryTheory.DerivedCategory.LocalCohomology

noncomputable section

universe u

#check (AlgebraicGeometry.Scheme.affineZeroLocus :
  ∀ {A : CommRingCat.{u}} (_ : Ideal A), TopologicalSpace.Closeds (Spec A))
#check (AlgebraicGeometry.Scheme.coe_affineZeroLocus :
  ∀ {A : CommRingCat.{u}} (I : Ideal A),
    (AlgebraicGeometry.Scheme.affineZeroLocus I : Set (Spec A)) =
      PrimeSpectrum.zeroLocus (I : Set A))
#check (AlgebraicGeometry.Scheme.DerivedQCoh.affineTilde :
  ∀ (A : CommRingCat.{u}),
    DerivedCategory (ModuleCat A) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace))
#check (AlgebraicGeometry.Scheme.DerivedQCoh.affineTildeIsEquivalence :
  ∀ (A : CommRingCat.{u}),
    Functor.IsEquivalence (AlgebraicGeometry.Scheme.DerivedQCoh.affineTilde A))
#check (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSectionsWithSupport :
  ∀ {A : CommRingCat.{u}} (_ : Ideal A),
    DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat A))
#check (CategoryTheory.DerivedCategory.LocalCohomology.affineComparison_isomorphic :
  ∀ {A : CommRingCat.{u}} (I : Ideal A) (_ : I.FG)
    (RΓ : (DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)),
    (IdealPowerTorsion.inclusion I ⊣ RΓ) →
      IsIsomorphic (RΓ ⋙ IdealPowerTorsion.inclusion I)
        (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSectionsWithSupport I))
#check (CategoryTheory.DerivedCategory.LocalCohomology.affineComparison_obj_isomorphic :
  ∀ {A : CommRingCat.{u}} (I : Ideal A) (_ : I.FG)
    (RΓ : (DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)),
    (IdealPowerTorsion.inclusion I ⊣ RΓ) →
      ∀ (K : DerivedCategory (ModuleCat A)),
        IsIsomorphic ((IdealPowerTorsion.inclusion I).obj (RΓ.obj K))
          ((AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSectionsWithSupport I).obj K))
