/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Opposites
import StacksCheckRecall

@[expose] public section


universe vC uC vA uA

namespace CategoryTheory

section

variable (C : Type uC) [Category.{vC} C]
variable (A : Type uA) [Category.{vA} A]

/- Domain-style sampling for Definition 4.3.2:
- primary domain: opposite-category presentations of contravariant functors
- sampled canonical declarations:
  `CategoryTheory.Functor`,
  `Category.opposite`,
  the functor-category notation `(· ⥤ ·)`
- best owner abstraction: the functor category `Cᵒᵖ ⥤ A`, i.e. `CategoryTheory.Functor`
  specialized to source `Cᵒᵖ` and target `A`
- primitive data: only the ordinary functor data and axioms for a functor out of the opposite
  category
- derived API: natural transformations and the inherited category structure on the functor
  category; set-valued presheaves are the direct specialization `Cᵒᵖ ⥤ Type _`
-/
/- Source/core/bridge triage for Definition 4.3.2:
- `source-facing`: a contravariant functor from `C` to `A`
- `core/canonical`: the functor category `Cᵒᵖ ⥤ A`
- primitive data: only an ordinary functor out of the opposite category
- derived API: natural transformations and the ambient category structure inherited from the
  functor category
- `bridge/view`: no alias is needed when `A = Type _`; use `Cᵒᵖ ⥤ Type _` directly
-/

/- Definition 4.3.2: a contravariant functor from `C` to `A` is canonically an object of the
functor category `Cᵒᵖ ⥤ A`, so the refined item is a direct recall of that owner type expression
rather than a parallel local alias. -/
@[stacks 001N "contravariant functors as functors from an opposite category"]
#check (Cᵒᵖ ⥤ A)

/- Companion recall: the primitive data of a contravariant functor are exactly the standard
object map, morphism map, and functoriality axioms of `CategoryTheory.Functor`, specialized to
source `Cᵒᵖ` and target `A`. -/
#check Functor

end

end CategoryTheory
