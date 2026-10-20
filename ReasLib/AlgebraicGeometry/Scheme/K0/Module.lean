/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Ring
public import ReasLib.AlgebraicGeometry.Scheme.K0.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Coherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0
public import Mathlib.Algebra.Module.MinimalAxioms

/-!
# The action of perfect-complex K-theory on coherent K-theory

On a Noetherian scheme, derived tensor product gives coherent `K₀'` its canonical module
structure over perfect-complex `K₀`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'

section Action

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The bounded coherent-derived tensor of a perfect complex with a bounded coherent object. -/
noncomputable def tensorObj
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (M : DerivedCategory.Bounded.CohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)) :
    DerivedCategory.Bounded.CohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) :=
  ⟨⟨(DerivedCategory.DerivedTensor.Right.functor M.obj.obj).obj K.obj,
      (RingedSpace.ModuleDerived.IsPerfect.tensorBoundedCoherentCohomology
        K.property M.property M.obj.property).2⟩,
    (RingedSpace.ModuleDerived.IsPerfect.tensorBoundedCoherentCohomology
      K.property M.property M.obj.property).1⟩

/-- The underlying derived object of `K0'.tensorObj` is the derived tensor product. -/
theorem tensorObj_obj
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (M : DerivedCategory.Bounded.CohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)) :
    (tensorObj X K M).obj.obj =
      (DerivedCategory.DerivedTensor.Right.functor M.obj.obj).obj K.obj := sorry

/-- Tensoring by a fixed perfect object kills the bounded coherent-derived triangle relations. -/
theorem relations_le_ker_smulOfDerived
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    TriangulatedK0.relations
        (DerivedCategory.Bounded.CohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)) ≤
      (FreeAbelianGroup.lift fun M : DerivedCategory.Bounded.CohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ↦
        (derivedK0Equiv X).symm (TriangulatedK0.of (tensorObj X K M))).ker := sorry

/-- Tensoring by a fixed perfect object on bounded coherent-derived classes. -/
noncomputable def smulOfDerived
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    TriangulatedK0
        (DerivedCategory.Bounded.CohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)) →+ K0' X :=
  TriangulatedK0.lift
    (fun M ↦ (derivedK0Equiv X).symm (TriangulatedK0.of (tensorObj X K M)))
    (relations_le_ker_smulOfDerived X K)

/-- `smulOfDerived` sends a derived generator to its tensor-product class. -/
theorem smulOfDerived_of
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (M : DerivedCategory.Bounded.CohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)) :
    smulOfDerived X K (TriangulatedK0.of M) =
      (derivedK0Equiv X).symm (TriangulatedK0.of (tensorObj X K M)) := sorry

/-- Tensoring by a fixed perfect object as an additive endomorphism of `K0' X`. -/
noncomputable def smulOf
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) : K0' X →+ K0' X :=
  (smulOfDerived X K).comp (derivedK0Equiv X).toAddMonoidHom

/-- `smulOf` agrees with derived tensoring through the inverse derived comparison. -/
theorem smulOf_derivedK0Equiv_symm_of
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (M : DerivedCategory.Bounded.CohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)) :
    smulOf X K ((derivedK0Equiv X).symm (TriangulatedK0.of M)) =
      (derivedK0Equiv X).symm (TriangulatedK0.of (tensorObj X K M)) := sorry

/-- Perfect-object classes defining `smulOf` kill the triangulated relations. -/
theorem relations_le_ker_smul :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) ≤
      (FreeAbelianGroup.lift fun K :
          RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ↦ smulOf X K).ker := sorry

/-- The biadditive action of perfect-complex `K₀` on coherent `K₀'`. -/
noncomputable def smul : K0 X →+ K0' X →+ K0' X :=
  TriangulatedK0.lift (smulOf X) (relations_le_ker_smul X)

/-- The action of a perfect generator on an inverse derived generator is derived tensor product. -/
theorem smul_derivedK0Equiv_symm_of
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (M : DerivedCategory.Bounded.CohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)) :
    smul X (TriangulatedK0.of K)
        ((derivedK0Equiv X).symm (TriangulatedK0.of M)) =
      (derivedK0Equiv X).symm (TriangulatedK0.of (tensorObj X K M)) := sorry

/-- Scalar multiplication of `K0 X` on `K0' X` is induced by derived tensor product. -/
noncomputable instance instSMul : SMul (K0 X) (K0' X) :=
  ⟨fun a m ↦ smul X a m⟩

/-- The tensor action distributes over addition in `K0' X`. -/
theorem smul_add_axiom (a : K0 X) (m n : K0' X) :
    a • (m + n) = a • m + a • n := sorry

/-- Addition in `K0 X` distributes through the tensor action. -/
theorem add_smul_axiom (a b : K0 X) (m : K0' X) :
    (a + b) • m = a • m + b • m := sorry

/-- Multiplication in `K0 X` is compatible with the tensor action. -/
theorem mul_smul_axiom (a b : K0 X) (m : K0' X) :
    (a * b) • m = a • b • m := sorry

/-- The structure-sheaf class acts identically on `K0' X`. -/
theorem one_smul_axiom (m : K0' X) : (1 : K0 X) • m = m := sorry

/-- The canonical `K0 X`-module structure on coherent `K0' X`. -/
noncomputable instance instModule : Module (K0 X) (K0' X) :=
  Module.ofMinimalAxioms (smul_add_axiom X) (add_smul_axiom X)
    (mul_smul_axiom X) (one_smul_axiom X)

end Action

end AlgebraicGeometry.Scheme.K0'
