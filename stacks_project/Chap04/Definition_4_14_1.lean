/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.IsLimit
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe vJ uJ vC uC

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable {F : J ⥤ C} (c : Cone F)

/- `Cone M` packages the source object, projections, and their compatibility. The exact canonical
owner for the remaining universal property is `IsLimit`: its `lift`, `fac`, and `uniq` fields give
the mediating morphism, factorization equations, and uniqueness. `LimitCone` only bundles a cone
with this witness, while `HasLimit` discards the chosen data, so neither should replace `IsLimit`
on the source-facing surface. This recall exposes the standard limit-cone API directly. -/

/- Definition 4.14.1: a limit of a diagram is a cone whose projections admit a unique compatible
factorization from every other cone; this is the canonical predicate `IsLimit`. -/
@[stacks 002E "limit cone with compatible projections and unique factorization"]
#check (IsLimit c : Type (max (max uJ uC) vC))

end CategoryTheory.Limits
