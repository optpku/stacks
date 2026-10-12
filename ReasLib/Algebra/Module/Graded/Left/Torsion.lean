/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.Finite.Abelian
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.RingTheory.GradedAlgebra.PositiveGenerators
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Torsion finitely generated graded modules

This file records eventual vanishing in high degree as the torsion Serre class.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace GradedModule.Left

variable {A : Type u} [CommRing A]
variable {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]

/-- 0BXD: An integer-graded left module is torsion when its homogeneous pieces vanish in all
sufficiently large degrees. -/
@[stacks 0BXD]
def IsTorsion (M : Left 𝒜 ℤ) : Prop :=
  ∀ᶠ n : ℤ in Filter.atTop, M.grading n = ⊥

/-- 0BXD: The torsion object property on finitely generated integer-graded modules. -/
@[stacks 0BXD]
def torsion (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :
    ObjectProperty (FG 𝒜 ℤ) :=
  fun M ↦ IsTorsion M.obj

/-- 0BXD: Under Noetherianity, eventual high-degree vanishing is a Serre class of finite graded
modules. -/
@[stacks 0BXD]
instance instTorsionIsSerreClass [IsNoetherianRing A] : (torsion 𝒜).IsSerreClass := sorry

end GradedModule.Left
