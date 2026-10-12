/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicCycle.Dimension
import stacks_project.Chap42.Situation_42_7_1
import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

open AlgebraicGeometry

universe u

section

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable [UniversallyCatenary S] [LocallyOfFiniteType f]
variable (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

#check (AlgebraicCycle X ℤ : Type u)

/- Definition 42.8.1: The group of `k`-cycles on `X` consists of cycles supported at points
where the relative dimension function induced by `f` and `δ` equals `k`. -/
@[stacks 02QR] #check
  (AlgebraicGeometry.AlgebraicCycle.dimensionSubgroup (f.relativeDimensionFunction δ) k :
    AddSubgroup (AlgebraicCycle X ℤ))

#check (AlgebraicGeometry.AlgebraicCycle.mem_dimensionSubgroup
    (f.relativeDimensionFunction δ) k :
  ∀ α : AlgebraicCycle X ℤ,
    α ∈ AlgebraicGeometry.AlgebraicCycle.dimensionSubgroup
      (f.relativeDimensionFunction δ) k ↔
      ∀ x, α x ≠ 0 → f.relativeDimensionFunction δ x = k)

end
