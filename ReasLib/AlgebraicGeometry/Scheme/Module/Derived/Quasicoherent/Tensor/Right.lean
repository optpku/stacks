/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

/-!
# Fixed-right derived tensor with quasicoherent cohomology

This module restricts fixed-right derived tensor to derived module sheaves whose cohomology is
quasicoherent.
-/

@[expose] public section

open CategoryTheory DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

namespace tensorRight

/-- Fixed-right derived tensor preserves derived module sheaves with quasicoherent cohomology. -/
theorem mapsTo {X : Scheme.{u}}
    (L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).inverseImage
          (DerivedTensor.Right.functor L.obj) := sorry

end tensorRight

/-- Fixed-right derived tensor, restricted to derived module sheaves with quasicoherent
cohomology. -/
noncomputable def tensorRight {X : Scheme.{u}}
    (L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :=
  (DerivedCategory.cohomologyIn
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).lift
      ((DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          DerivedTensor.Right.functor L.obj)
      (fun K ↦ tensorRight.mapsTo L K.obj K.property)

/-- Forgetting the quasicoherent-cohomology lift of fixed-right derived tensor recovers the
ambient derived tensor functor. -/
noncomputable def tensorRight.inclusionIso {X : Scheme.{u}}
    (L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    tensorRight L ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ≅
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          DerivedTensor.Right.functor L.obj :=
  (DerivedCategory.cohomologyIn
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).liftCompιIso
      ((DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          DerivedTensor.Right.functor L.obj)
      (fun K ↦ tensorRight.mapsTo L K.obj K.property)

/-- The derived tensor product of two derived module sheaves with quasicoherent cohomology. -/
noncomputable abbrev tensorObj {X : Scheme.{u}}
    (K L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :=
  (tensorRight L).obj K

/-- The underlying derived module of the restricted tensor object is the ambient derived
tensor product. -/
@[simp]
theorem tensorObj_obj {X : Scheme.{u}}
    (K L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    (tensorObj K L).obj =
      (DerivedTensor.Right.functor L.obj).obj K.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
