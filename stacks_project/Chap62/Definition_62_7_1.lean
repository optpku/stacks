module

public import stacks_project.Chap62.Definition_62_7_1_Equidimensional
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

section

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsLocallyNoetherian S] [LocallyOfFiniteType f]
variable (r : ℕ)

/- Definition 62.7.1: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` is
locally Noetherian and `f` is locally of finite type. Let `r ≥ 0` be an integer.
A relative `r`-cycle `α` on `X / S` is equidimensional if `support α` is
contained in a closed subscheme `W ⊆ X` with
`RelativeDimensionLE (W.subschemeι ≫ f) r`. The group of all equidimensional
relative `r`-cycles on `X / S` is `RelativeCycle.equidimensional f r`, denoted
`z_equi(X/S, r)`. -/
@[stacks 0H5I] #check
  (RelativeCycle.equidimensional f r : AddSubgroup (RelativeCycle.Family f r))

#check RelativeCycle.mem_equidimensional

end
