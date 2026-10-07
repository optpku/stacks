module

public import ReasLib.AlgebraicGeometry.Scheme.K0
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# The ring structure on the Grothendieck group of perfect complexes

Derived tensor product gives the Grothendieck group of perfect complexes on a scheme its
canonical commutative-ring structure.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0

/-- The derived tensor product of two perfect complexes, with its perfectness retained. -/
noncomputable def tensorObj (X : Scheme.{u})
    (K L : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) :=
  ⟨(DerivedCategory.DerivedTensor.Right.functor L.obj).obj K.obj,
    RingedSpace.ModuleDerived.IsPerfect.tensor K.property L.property⟩

/-- The underlying derived object of `K0.tensorObj` is the derived tensor product. -/
theorem tensorObj_obj (X : Scheme.{u})
    (K L : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    (tensorObj X K L).obj =
      (DerivedCategory.DerivedTensor.Right.functor L.obj).obj K.obj := sorry

/-- The perfect object represented by the structure sheaf in degree zero. -/
noncomputable def unitObject (X : Scheme.{u}) :
    RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) :=
  ⟨(DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj
      (SheafOfModules.unit X.toRingedSpace.ringCatSheaf : X.Modules),
    SheafOfModules.IsFiniteLocallyFree.isPerfect _⟩

/-- The underlying derived object of `K0.unitObject` is the structure sheaf in degree zero. -/
theorem unitObject_obj (X : Scheme.{u}) :
    (unitObject X).obj =
      (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf : X.Modules) := sorry

/-- Tensoring with a fixed perfect object kills the triangle relations in the other variable. -/
theorem relations_le_ker_mulOf (X : Scheme.{u})
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) ≤
      (FreeAbelianGroup.lift fun L :
          RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ↦
        TriangulatedK0.of (tensorObj X K L)).ker := sorry

/-- Multiplication by the class of a fixed perfect complex. -/
noncomputable def mulOf (X : Scheme.{u})
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) : K0 X →+ K0 X :=
  TriangulatedK0.lift (fun L ↦ TriangulatedK0.of (tensorObj X K L))
    (relations_le_ker_mulOf X K)

/-- `K0.mulOf` sends an object class to the class of its derived tensor product. -/
theorem mulOf_of (X : Scheme.{u})
    (K L : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    mulOf X K (TriangulatedK0.of L) = TriangulatedK0.of (tensorObj X K L) := sorry

/-- The perfect-complex classes defining `K0.mulOf` kill the triangle relations. -/
theorem relations_le_ker_mul (X : Scheme.{u}) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) ≤
      (FreeAbelianGroup.lift fun K :
          RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ↦ mulOf X K).ker := sorry

/-- The biadditive multiplication on perfect-complex `K₀`, induced by derived tensor product. -/
noncomputable def mul (X : Scheme.{u}) : K0 X →+ K0 X →+ K0 X :=
  TriangulatedK0.lift (mulOf X) (relations_le_ker_mul X)

/-- Multiplication of perfect-complex generators is represented by derived tensor product. -/
theorem mul_of (X : Scheme.{u})
    (K L : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    mul X (TriangulatedK0.of K) (TriangulatedK0.of L) =
      TriangulatedK0.of (tensorObj X K L) := sorry

/-- Multiplication on `K0 X` is the tensor-induced biadditive operation. -/
noncomputable instance instMul (X : Scheme.{u}) : Mul (K0 X) :=
  ⟨fun x y ↦ mul X x y⟩

/-- The unit on `K0 X` is the class of the structure sheaf in degree zero. -/
noncomputable instance instOne (X : Scheme.{u}) : One (K0 X) :=
  ⟨TriangulatedK0.of (unitObject X)⟩

/-- Derived tensor multiplication on `K0 X` is associative. -/
theorem mul_assoc_axiom (X : Scheme.{u}) (a b c : K0 X) :
    a * b * c = a * (b * c) := sorry

/-- Derived tensor multiplication on `K0 X` is commutative. -/
theorem mul_comm_axiom (X : Scheme.{u}) (a b : K0 X) : a * b = b * a := sorry

/-- The structure-sheaf class is a left unit for derived tensor multiplication. -/
theorem one_mul_axiom (X : Scheme.{u}) (a : K0 X) : 1 * a = a := sorry

/-- Derived tensor multiplication distributes over addition. -/
theorem mul_add_axiom (X : Scheme.{u}) (a b c : K0 X) :
    a * (b + c) = a * b + a * c := sorry

/-- The canonical commutative-ring structure on perfect-complex `K₀`. -/
noncomputable instance instCommRing (X : Scheme.{u}) : CommRing (K0 X) :=
  CommRing.ofMinimalAxioms add_assoc zero_add neg_add_cancel
    (mul_assoc_axiom X) (mul_comm_axiom X) (one_mul_axiom X) (mul_add_axiom X)

/-- The multiplicative unit in `K0 X` is the class of the structure sheaf. -/
theorem one_eq (X : Scheme.{u}) :
    (1 : K0 X) = TriangulatedK0.of (unitObject X) := sorry

end AlgebraicGeometry.Scheme.K0
