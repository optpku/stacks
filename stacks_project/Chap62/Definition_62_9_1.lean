module

public import stacks_project.Chap62.Definition_62_9_1_Proper
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
  (RelativeCycle.proper f r : AddSubgroup (RelativeCycle.Family f r))

#check RelativeCycle.mem_proper

end
