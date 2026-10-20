/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import ReasLib.Algebra.Category.ModuleCat.SymmetricAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication on symmetric algebras in `ModuleCat`

Symmetric-algebra multiplication is bundled as a morphism from the tensor square of the
underlying module.  Presheaf and sheaf constructions can transport this concrete datum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace ModuleCat.symmetricAlgebra

variable {R : Type u} [CommRing R]

/-- Multiplication in a symmetric algebra, bundled as a morphism of modules. -/
@[stacks 01CF "multiplication in a symmetric algebra"]
noncomputable def mul (M : ModuleCat.{u} R) :
    tensorObj M.symmetricAlgebra M.symmetricAlgebra ⟶ M.symmetricAlgebra :=
  ModuleCat.ofHom (LinearMap.mul' R (_root_.SymmetricAlgebra R M))

/-- The multiplicative unit of a symmetric algebra, bundled as a morphism of modules. -/
@[stacks 01CF "unit of a symmetric algebra"]
noncomputable def one (M : ModuleCat.{u} R) :
    𝟙_ (ModuleCat.{u} R) ⟶ M.symmetricAlgebra :=
  ModuleCat.ofHom (Algebra.linearMap R (_root_.SymmetricAlgebra R M))

/-- The symmetric-algebra unit sends the scalar-ring unit to the algebra unit. -/
@[simp]
theorem one_apply_one (M : ModuleCat.{u} R) :
    one M (1 : R) = (1 : _root_.SymmetricAlgebra R M) := sorry

/-- The symmetric-algebra unit is natural in the underlying module. -/
@[reassoc]
theorem one_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    one M ≫ map f = one N := sorry

/-- Symmetric-algebra multiplication evaluates on a pure tensor by algebra multiplication. -/
@[simp]
theorem mul_tmul (M : ModuleCat.{u} R) (a b : _root_.SymmetricAlgebra R M) :
    mul M (a ⊗ₜ b) = a * b := sorry

/-- Symmetric-algebra multiplication is natural in the underlying module. -/
@[reassoc]
theorem mul_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    tensorHom (map f) (map f) ≫ mul N = mul M ≫ map f := sorry

end ModuleCat.symmetricAlgebra
