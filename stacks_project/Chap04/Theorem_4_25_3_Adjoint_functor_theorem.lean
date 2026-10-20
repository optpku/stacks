module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v v₁ u u₁

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]
variable (G : D ⥤ C) [Limits.HasLimits D]
variable [Limits.PreservesLimitsOfSize.{v₁, v₁} G]

/-
The source writes `G : 𝒞 ⥤ 𝒟`, whereas the canonical theorem names the same domain and
codomain metavariables `D` and `C`, respectively. Its assumptions `[HasLimits D]`,
`[PreservesLimitsOfSize.{v₁, v₁} G]`, and `SolutionSetCondition.{v₁} G` are exactly the
source's completeness, limit-preservation, and small solution-family hypotheses. The conclusion
`G.IsRightAdjoint` is the standard reusable form of saying that `G` has a left adjoint.

In particular, the solution-family index lives in the domain morphism universe `v₁`, while the
object universes of both categories remain independent. Recalling the theorem itself therefore
retains the useful universe generality without introducing a second statement or a local wrapper.
-/

/- Theorem 4.25.3 (Adjoint functor theorem): if `G : D ⥤ C` preserves limits, `D` has limits, and
`G` satisfies the solution set condition, then `G` is a right adjoint. This is exactly the
canonical mathlib theorem `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`. -/
@[stacks 0AHQ "limit-preserving functors satisfying the solution set condition are right adjoints"]
#check (isRightAdjoint_of_preservesLimits_of_solutionSetCondition G :
  SolutionSetCondition G → G.IsRightAdjoint)

end CategoryTheory
