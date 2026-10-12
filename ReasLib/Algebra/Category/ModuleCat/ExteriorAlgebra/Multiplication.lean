/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication on exterior algebras in `ModuleCat`

The algebra multiplication is bundled as a morphism from the tensor square of the underlying
module.  Presheaf and sheaf constructions can transport this explicit linear-algebra datum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace ModuleCat.exteriorAlgebra

variable {R : Type u} [CommRing R]

/-- Multiplication in an exterior algebra, as a morphism from its tensor square. -/
@[stacks 01CF "multiplication in an exterior algebra"]
noncomputable def mul (M : ModuleCat.{u} R) :
    tensorObj M.exteriorAlgebra M.exteriorAlgebra ⟶ M.exteriorAlgebra :=
  ModuleCat.ofHom (LinearMap.mul' R (ExteriorAlgebra R M))

/-- The multiplicative unit of an exterior algebra, bundled as a morphism of modules. -/
@[stacks 01CF "unit of an exterior algebra"]
noncomputable def one (M : ModuleCat.{u} R) :
    𝟙_ (ModuleCat.{u} R) ⟶ M.exteriorAlgebra :=
  ModuleCat.ofHom (Algebra.linearMap R (ExteriorAlgebra R M))

/-- The exterior-algebra unit sends the scalar-ring unit to the algebra unit. -/
@[simp]
theorem one_apply_one (M : ModuleCat.{u} R) :
    one M (1 : R) = (1 : ExteriorAlgebra R M) := sorry

/-- The exterior-algebra unit is natural in the underlying module. -/
@[reassoc]
theorem one_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    one M ≫ map f = one N := sorry

/-- Exterior-algebra multiplication evaluates on a pure tensor by algebra multiplication. -/
@[simp]
theorem mul_tmul (M : ModuleCat.{u} R) (a b : ExteriorAlgebra R M) :
    mul M (a ⊗ₜ b) = a * b := sorry

/-- Exterior-algebra multiplication is natural in the underlying module. -/
@[reassoc]
theorem mul_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    tensorHom (map f) (map f) ≫ mul N = mul M ≫ map f := sorry

end ModuleCat.exteriorAlgebra
