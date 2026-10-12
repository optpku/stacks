/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory

open BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/- 4.34.2.2 (1): identity automorphisms define the neutral section
`X ⥤ᵇ relativeInertia F`. -/
@[stacks 04Z3 "(1)"]
#check (RelativeInertia.identitySection :
  (F : X ⥤ᵇ Y) → X ⥤ᵇ relativeInertia F)

/- 4.34.2.2 (2): identity automorphisms define the neutral section
`X ⥤ᵇ inertia X`. -/
@[stacks 04Z3 "(2)"]
#check (Inertia.identitySection :
  (X : BasedCategory.{vX, uX} C) → X ⥤ᵇ inertia X)

end BasedCategory
end CategoryTheory
