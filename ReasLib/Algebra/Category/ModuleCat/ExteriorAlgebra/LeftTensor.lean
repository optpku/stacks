module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-one multiplication on exterior algebras

This file bundles left multiplication by a degree-one generator as a morphism
`M ⊗ Λ(M) ⟶ Λ(M)`.  The construction belongs to `ModuleCat`: presheaves and sheaves only
transport this concrete linear-algebra datum.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace ModuleCat.exteriorAlgebra

variable {R : Type u} [CommRing R]

/-- Left multiplication in the exterior algebra by the degree-one generator associated to a
module element. -/
def leftMulFn (M : ModuleCat.{u} R) (x : M) (a : ExteriorAlgebra R M) :
    ExteriorAlgebra R M :=
  ExteriorAlgebra.ι R x * a

/-- Degree-one left multiplication is additive in the module argument. -/
theorem leftMulFn_add_left (M : ModuleCat.{u} R) (x y : M) (a : ExteriorAlgebra R M) :
    leftMulFn M (x + y) a = leftMulFn M x a + leftMulFn M y a := sorry

/-- Degree-one left multiplication is linear in the module argument. -/
theorem leftMulFn_smul_left (M : ModuleCat.{u} R) (r : R) (x : M)
    (a : ExteriorAlgebra R M) :
    leftMulFn M (r • x) a = r • leftMulFn M x a := sorry

/-- Degree-one left multiplication is additive in the exterior-algebra argument. -/
theorem leftMulFn_add_right (M : ModuleCat.{u} R) (x : M)
    (a b : ExteriorAlgebra R M) :
    leftMulFn M x (a + b) = leftMulFn M x a + leftMulFn M x b := sorry

/-- Degree-one left multiplication is linear in the exterior-algebra argument. -/
theorem leftMulFn_smul_right (M : ModuleCat.{u} R) (r : R) (x : M)
    (a : ExteriorAlgebra R M) :
    leftMulFn M x (r • a) = r • leftMulFn M x a := sorry

/-- The canonical morphism `M ⊗ Λ(M) ⟶ Λ(M)` given by multiplication by degree-one
generators on the left. -/
@[stacks 0FJN "degree-one exterior multiplication"]
noncomputable def leftTensorMap (M : ModuleCat.{u} R) :
    tensorObj M M.exteriorAlgebra ⟶ M.exteriorAlgebra :=
  ModuleCat.MonoidalCategory.tensorLift
    (leftMulFn M) (leftMulFn_add_left M) (leftMulFn_smul_left M)
    (leftMulFn_add_right M) (leftMulFn_smul_right M)

/-- The degree-one left-tensor morphism evaluates on a pure tensor by multiplication in the
exterior algebra. -/
@[simp]
theorem leftTensorMap_tmul (M : ModuleCat.{u} R) (x : M) (a : ExteriorAlgebra R M) :
    leftTensorMap M (x ⊗ₜ a) = ExteriorAlgebra.ι R x * a := sorry

/-- Degree-one left multiplication is natural in the module. -/
theorem leftTensorMap_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    tensorHom f (map f) ≫ leftTensorMap N = leftTensorMap M ≫ map f := sorry

end ModuleCat.exteriorAlgebra
