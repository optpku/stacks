/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

universe u

/- Compatibility: proper pushforward to Spec of a field is left adjoint. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.properPushforwardIsLeftAdjoint :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
      (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).IsLeftAdjoint)

/- Compatibility: chosen proper dualizing complex over a field. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
      AlgebraicGeometry.Scheme.DerivedQCoh X)

/- Compatibility: unfolding of the chosen proper dualizing complex. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex_obj :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
      AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex f =
        (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).rightAdjoint.obj
          (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf
            (Spec (CommRingCat.of k))))

/- Compatibility: comparison of the chosen right adjoint with a supplied adjunction. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.isoOfAdjunction :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh (Spec (CommRingCat.of k)) ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X)
      (ha : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a),
      AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex f ≅
        a.obj (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf
          (Spec (CommRingCat.of k))))

/- Compatibility: Krull-dimension index of a proper scheme over a field. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dimensionIndex :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)), ℕ)

/- Compatibility: unfolding of the dimension index. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dimensionIndex_def :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dimensionIndex f =
        ((topologicalKrullDim X).unbotD 0).toNat)

/- Compatibility: dualizing module of a proper scheme over a field. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f], X.Modules)

/- Compatibility: unfolding of the dualizing module. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule_eq :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
      AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule f =
        AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf
          (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex f).obj
          (-(AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dimensionIndex f : ℤ)))
