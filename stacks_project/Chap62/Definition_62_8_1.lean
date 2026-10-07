module

public import stacks_project.Chap62.Definition_62_8_1_Effective
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

section

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsLocallyNoetherian S] [LocallyOfFiniteType f]
variable (r : ℕ)

/- Definition 62.8.1: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` is
locally Noetherian and `f` is locally of finite type. Let `r ≥ 0` be an integer.
We say a relative `r`-cycle `α` on `X / S` is effective if `α_s` is an effective
cycle (Chow Homology, Definition 42.8.4) for all `s ∈ S`. The monoid of all
effective relative `r`-cycles on `X / S` is denoted `z^{eff}(X/S, r)`. -/
@[stacks 0H5R] #check
  (RelativeCycle.effective f r : AddSubmonoid (RelativeCycle.Family f r))

#check RelativeCycle.mem_effective

end
