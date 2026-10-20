/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.GradedObject.Duality
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open DerivedCategory.Bounded
open DerivedCategory.TStructure
open scoped DerivedExt DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- A quasicoherent derived object on a proper scheme over a field is bounded coherent exactly when
its total Ext from every perfect object is finite-dimensional over the base field. -/
theorem boundedCoherent_iff_finiteTotalExt
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (K : Scheme.DerivedQCoh X) :
    (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K.obj ∧
      (t.bounded : ObjectProperty
        (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj) ↔
      ∀ E : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          GradedObject.FiniteTotalDimension
            (fun i : ℤ ↦ DerivedExt.value f E K.obj i) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
