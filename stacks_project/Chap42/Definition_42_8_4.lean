module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicCycle.Effective
import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
import ReasLib.Topology.Specialization.Dimension
import stacks_project.Chap42.Situation_42_7_1

open AlgebraicGeometry

universe u

section

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable [UniversallyCatenary S] [LocallyOfFiniteType f]
variable (δ : S → ℤ) [IsDimensionFunction δ]

/- Definition 42.8.4: An effective cycle on `X` is an integer-valued algebraic cycle whose
coefficient at every integral closed subscheme is nonnegative. -/
@[stacks 0H47] #check
  (AlgebraicGeometry.AlgebraicCycle.effective X : AddSubmonoid (AlgebraicCycle X ℤ))

end
