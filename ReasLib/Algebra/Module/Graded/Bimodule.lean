/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Category
public import ReasLib.Algebra.Module.Graded.Left

/-!
# Graded bimodules

This leaf packages a graded bimodule as a right graded module together with a compatible left
action.  Thus the carrier, base module, right action, grading, and direct-sum decomposition have a
single owner, while the additional fields are exactly the left-module and bimodule compatibility
data.
-/

@[expose] public section

noncomputable section

universe x y w v u

namespace GradedModule

variable {ι : Type x} [DecidableEq ι] [AddCommMonoid ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]

/-- Definition 22.28.1 (2): a graded `(A, B)`-bimodule is a right graded `B`-module
equipped with a commuting left `A`-module structure whose action respects the grading. -/
@[stacks 0FQH "graded bimodules over internally graded algebras"]
structure Bimodule (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (𝒝 : ι → Submodule R B) [GradedAlgebra 𝒝] where
  /-- The underlying right graded `B`-module. -/
  toRight : Right.{x, y, w, u} 𝒝
  /-- The left `A`-module structure. -/
  [moduleLeft : Module A toRight.carrier]
  /-- Restriction of the left action along `R → A` agrees with the base `R`-module structure. -/
  [isScalarTowerLeft : IsScalarTower R A toRight.carrier]
  /-- The left `A`-action commutes with the right `B`-action. -/
  [smulCommClass : SMulCommClass A Bᵐᵒᵖ toRight.carrier]
  /-- The left action adds the degrees of homogeneous elements. -/
  [gradedSMulLeft : SetLike.GradedSMul 𝒜 toRight.grading]

namespace Bimodule

variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ι → Submodule R B} [GradedAlgebra 𝒝]

attribute [instance] Bimodule.moduleLeft Bimodule.isScalarTowerLeft
  Bimodule.smulCommClass Bimodule.gradedSMulLeft

/-- A graded bimodule coerces to its underlying carrier. -/
instance instCoeSort : CoeSort (Bimodule.{x, y, w, v, u} 𝒜 𝒝) (Type y) where
  coe M := M.toRight.carrier

/-- The homogeneous pieces of a graded bimodule. -/
abbrev grading (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) : ι → Submodule R M :=
  M.toRight.grading

/-- The stored left action of a graded bimodule. -/
def leftAction (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (a : A) (x : M) : M :=
  a • x

/-- The stored right action of a graded bimodule, expressed through the opposite algebra. -/
def rightAction (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (x : M) (b : B) : M :=
  M.toRight.action x b

/-- Forget the right action of a graded bimodule. -/
def toLeft (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) : Left.{x, y, v, u} 𝒜 where
  carrier := M.toRight.carrier
  addCommMonoid := M.toRight.addCommGroup.toAddCommMonoid
  moduleBase := M.toRight.moduleBase
  moduleAlgebra := M.moduleLeft
  isScalarTower := M.isScalarTowerLeft
  grading := M.grading
  decomposition := M.toRight.decomposition
  gradedSMul := M.gradedSMulLeft

/-- Forgetting the right action preserves every homogeneous piece. -/
@[simp] theorem toLeft_grading (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (i : ι) :
    M.toLeft.grading i = M.grading i := sorry

/-- Left multiplication by homogeneous elements adds their degrees. -/
theorem left_smul_mem (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) {i j : ι} {a : A} {x : M}
    (ha : a ∈ 𝒜 i) (hx : x ∈ M.grading j) : M.leftAction a x ∈ M.grading (i + j) := sorry

/-- Right multiplication by homogeneous elements adds their degrees. -/
theorem right_smul_mem (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) {i j : ι} {x : M} {b : B}
    (hx : x ∈ M.grading i) (hb : b ∈ 𝒝 j) :
    M.rightAction x b ∈ M.grading (i + j) := sorry

end Bimodule

end GradedModule
