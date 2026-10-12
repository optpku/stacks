/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Left graded modules

This leaf bundles the standard mathlib presentation of a left module over an internally graded
algebra: a module carrier, a direct-sum grading, and a `SetLike.GradedSMul` instance.
-/

@[expose] public section

noncomputable section

universe x w v u

namespace GradedModule

variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {R : Type u} [CommSemiring R]
variable {A : Type v} [Semiring A] [Algebra R A]

/-- A left graded module over the internally graded algebra `𝒜`, graded by a degree type `κ`
with an additive `ι`-action. -/
@[stacks 052N "left graded module bundle"]
structure Left (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (κ : Type x := ι) [DecidableEq κ] [AddAction ι κ] where
  /-- The underlying type. -/
  carrier : Type w
  /-- The additive commutative monoid of the underlying module. -/
  [addCommMonoid : AddCommMonoid carrier]
  /-- The underlying `R`-module. -/
  [moduleBase : Module R carrier]
  /-- The left `A`-module structure. -/
  [moduleAlgebra : Module A carrier]
  /-- Restriction of the `A`-action along `R → A` agrees with the base `R`-module structure. -/
  [isScalarTower : IsScalarTower R A carrier]
  /-- The homogeneous pieces of the module. -/
  grading : κ → Submodule R carrier
  /-- The homogeneous pieces form an internal direct-sum decomposition. -/
  [decomposition : DirectSum.Decomposition grading]
  /-- The left action adds the degrees of homogeneous elements. -/
  [gradedSMul : SetLike.GradedSMul 𝒜 grading]

namespace Left

variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
variable {κ : Type x} [DecidableEq κ] [AddAction ι κ]

attribute [instance] Left.addCommMonoid Left.moduleBase Left.moduleAlgebra
  Left.isScalarTower Left.decomposition Left.gradedSMul

/-- A left graded module coerces to its underlying carrier. -/
@[stacks 052N "left graded module coercion"]
instance instCoeSort : CoeSort (Left (R := R) (A := A) 𝒜 κ) (Type w) where
  coe M := M.carrier

end Left

end GradedModule
