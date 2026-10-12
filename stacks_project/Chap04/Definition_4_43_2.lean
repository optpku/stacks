/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
import StacksCheckRecall

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D)

/- The source needs a functor with an invertible tensorator, its associativity coherence, and
preservation of the tensor unit. The verified `Functor.Monoidal` class is the canonical owner:
`Monoidal.μNatIso` packages the functorial tensorator with components `Monoidal.μIso`, while
`LaxMonoidal.associativity` and `Monoidal.εIso` expose the coherence and unit clauses.
`Functor.CoreMonoidal` is only a construction helper for the same owner, so recalling it would
create a competing public presentation. This choice adds no variables or assumptions beyond the
source, and downstream files can use the standard monoidal-functor typeclass and comparison API. -/

/- Definition 4.43.2: a functor of monoidal categories is the canonical mathlib owner
`Functor.Monoidal`. For a functor `F : C ⥤ D`, the typeclass `F.Monoidal` is the primitive
structure; the unit and tensor comparison isomorphisms belong to its derived API, so no parallel
local wrapper is needed here. -/
@[stacks 0FFL "monoidal functor with invertible tensorator, associativity coherence, and unit preservation"]
#check (Monoidal F : Type (max u₁ v₂))

end Functor
end CategoryTheory
