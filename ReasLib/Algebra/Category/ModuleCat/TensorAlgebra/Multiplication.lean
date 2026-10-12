/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import ReasLib.Algebra.Category.ModuleCat.TensorAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication on tensor algebras in `ModuleCat`

Tensor-algebra multiplication is bundled as a morphism from the tensor square of the
underlying module.  Presheaf and sheaf constructions can transport this concrete datum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace ModuleCat.tensorAlgebra

variable {R : Type u} [CommRing R]

/-- Multiplication in a tensor algebra, bundled as a morphism of modules. -/
@[stacks 01CF "multiplication in a tensor algebra"]
noncomputable def mul (M : ModuleCat.{u} R) :
    tensorObj M.tensorAlgebra M.tensorAlgebra ⟶ M.tensorAlgebra :=
  ModuleCat.ofHom (LinearMap.mul' R (TensorAlgebra R M))

/-- The multiplicative unit of a tensor algebra, bundled as a morphism of modules. -/
@[stacks 01CF "unit of a tensor algebra"]
noncomputable def one (M : ModuleCat.{u} R) :
    𝟙_ (ModuleCat.{u} R) ⟶ M.tensorAlgebra :=
  ModuleCat.ofHom (Algebra.linearMap R (TensorAlgebra R M))

/-- The tensor-algebra unit sends the scalar-ring unit to the algebra unit. -/
@[simp]
theorem one_apply_one (M : ModuleCat.{u} R) :
    one M (1 : R) = (1 : TensorAlgebra R M) := sorry

/-- The tensor-algebra unit is natural in the underlying module. -/
@[reassoc]
theorem one_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    one M ≫ map f = one N := sorry

/-- Tensor-algebra multiplication evaluates on a pure tensor by algebra multiplication. -/
@[simp]
theorem mul_tmul (M : ModuleCat.{u} R) (a b : TensorAlgebra R M) :
    mul M (a ⊗ₜ b) = a * b := sorry

/-- Tensor-algebra multiplication is natural in the underlying module. -/
@[reassoc]
theorem mul_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    tensorHom (map f) (map f) ≫ mul N = mul M ≫ map f := sorry

end ModuleCat.tensorAlgebra
