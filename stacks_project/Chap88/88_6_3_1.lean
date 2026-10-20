module

public import Mathlib.Algebra.Module.Presentation.Basic
import ReasLib.Algebra.Module.Presentation.Relations
import StacksCheckRecall

@[expose] public section

universe u v w₀ w₁

/- 88.6.3.1: after choosing generators `g j` of `J` and generators `k i` of the
syzygy module of those generators, the composition-zero identity is
`∑ j, k i j * g j = 0` in `P` for each relation index `i`. This is the
linear-relation law of a module presentation: each relation coefficient vector
evaluates to zero on the generator family. -/
@[stacks 0AKB] #check
  (@Module.Relations.Solution.sum_var_relation :
    ∀ {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
      {relations : Module.Relations.{w₀, w₁} R} [Fintype relations.G]
      (solution : relations.Solution M) (r : relations.R),
      ∑ g, (relations.relation r) g • solution.var g = 0)
