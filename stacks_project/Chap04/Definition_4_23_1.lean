module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe vC uC vD uD

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (F : C ⥤ D)

/- The verified candidates `leftExactFunctor`, `rightExactFunctor`, and `exactFunctor` are the
canonical `ObjectProperty` owners; their `_iff` lemmas expose `PreservesFiniteLimits` and
`PreservesFiniteColimits`. They omit only the source's ambient assumptions that the relevant
finite (co)limits exist in `C`: specializing under `[HasFiniteLimits C]` and
`[HasFiniteColimits C]` recovers the textbook setting exactly. Tagged recalls therefore avoid
parallel local predicates and retain the bundled-functor and composition APIs for downstream use. -/

/- Definition 4.23.1 (1): the left-exact functors `C ⥤ D` form the canonical object property
`leftExactFunctor C D`, whose value on `F : C ⥤ D` is definitionally `PreservesFiniteLimits F`. -/
@[stacks 0034 "left exact functors preserve all finite limits"]
#check (leftExactFunctor C D F : Prop)

/- Definition 4.23.1 (2): the right-exact functors `C ⥤ D` form the canonical object property
`rightExactFunctor C D`, whose value on `F : C ⥤ D` is definitionally
`PreservesFiniteColimits F`. -/
@[stacks 0034 "right exact functors preserve all finite colimits"]
#check (rightExactFunctor C D F : Prop)

/- Definition 4.23.1 (3): the exact functors `C ⥤ D` form the canonical object property
`exactFunctor C D`, whose value on `F : C ⥤ D` says that `F` is both left exact and right exact. -/
@[stacks 0034 "exact functors are both left and right exact"]
#check (exactFunctor C D F : Prop)

/- Companion recall: exactness is definitionally preservation of finite limits together with
preservation of finite colimits. -/
#check exactFunctor_iff

end CategoryTheory
