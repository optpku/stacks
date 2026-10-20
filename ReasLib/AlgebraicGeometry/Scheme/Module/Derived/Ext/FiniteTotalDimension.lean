/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Ext.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.CohomologyDetection
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.GradedObject.Duality

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded
open scoped DerivedExt DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace DerivedExt

/-- A perfect complex has finite total-dimensional derived Ext to a bounded coherent complex on a
proper scheme over a field. -/
theorem finiteTotalDimension_of_isPerfect {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (K : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    GradedObject.FiniteTotalDimension
      (fun i : ℤ ↦ value f E (ι.obj K.obj) i) := sorry

end DerivedExt
end Hom
end Scheme
end AlgebraicGeometry
