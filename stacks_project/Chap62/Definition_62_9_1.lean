module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Proper
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

section

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsLocallyNoetherian S] [LocallyOfFiniteType f]
variable (r : ℕ)

/- Definition 62.9.1: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` is
locally Noetherian and `f` is locally of finite type. Let `r ≥ 0` be an integer.
We say a relative `r`-cycle `α` on `X / S` is a proper relative cycle if the
support of `α` (Remark 62.5.6) is contained in a closed subset `W ⊆ X` proper
over `S` (Cohomology of Schemes, Definition 30.26.2). The group of all proper
relative `r`-cycles on `X / S` is denoted `c(X/S, r)`. -/
@[stacks 0H61] #check
  (AlgebraicGeometry.RelativeCycle.proper f r : AddSubgroup (f.FiberCycleFamily r))

#check (AlgebraicGeometry.RelativeCycle.mem_proper_iff f r :
  ∀ α : f.FiberCycleFamily r,
    α ∈ AlgebraicGeometry.RelativeCycle.proper f r ↔
      RelativeCycle.IsRelative α ∧
        ∃ W : TopologicalSpace.Closeds X,
          Scheme.Hom.CyclesOnFibers.support α ⊆ W ∧ ClosedSubset.IsProperOver f W)

end
