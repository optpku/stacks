/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import StacksCheckRecall

/-!
# Set-valued stalk functors at a point of a site

This directly reuses the canonical Mathlib point-fiber API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (p : GrothendieckTopology.Point.{max u v} J)

section Sheafification

variable [HasWeakSheafify J (Type (max u v))]

/- Lemma 18.36.1 (1): taking the stalk of a set-valued presheaf agrees with taking the stalk
after sheafification. -/
@[stacks 04EN "(1)"]
#check
  (p.presheafToSheafCompSheafFiberIso (Type (max u v)) :
    presheafToSheaf J (Type (max u v)) ⋙ p.sheafFiber ≅ p.presheafFiber)

end Sheafification

/- Lemma 18.36.1 (2), exactness: the stalk functor on set-valued sheaves is exact. -/
@[stacks 04EN "(2), exact"]
#check
  (ExactFunctor.of p.sheafFiber :
    Sheaf J (Type (max u v)) ⥤ₑ Type (max u v))

/- Lemma 18.36.1 (2), colimits: the stalk functor on sheaves preserves all colimits. -/
@[stacks 04EN "(2), colimits"]
#check
  (inferInstance :
    PreservesColimits (p.sheafFiber : Sheaf J (Type (max u v)) ⥤ Type (max u v)))

/- Lemma 18.36.1 (3), exactness: the stalk functor on set-valued presheaves is exact. -/
@[stacks 04EN "(3), exact"]
#check
  (ExactFunctor.of p.presheafFiber :
    (Cᵒᵖ ⥤ Type (max u v)) ⥤ₑ Type (max u v))

/- Lemma 18.36.1 (3), colimits: the stalk functor on presheaves preserves all colimits. -/
@[stacks 04EN "(3), colimits"]
#check
  (inferInstance :
    PreservesColimits (p.presheafFiber : (Cᵒᵖ ⥤ Type (max u v)) ⥤ Type (max u v)))

end CategoryTheory
