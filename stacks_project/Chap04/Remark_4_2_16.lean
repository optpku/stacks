/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Size.Endofunctor
import StacksCheckRecall

@[expose] public section


universe u

namespace CategoryTheory

/- Remark 4.2.16 (Stacks tag `02C2`): when the category of sets is modeled by the big category
`Type u`, the type of endofunctors `Type u ⥤ Type u` is not `u`-small. The reusable
universe-size statement is `CategoryTheory.not_small_type_endofunctor`. -/
@[stacks 02C2]
#check (not_small_type_endofunctor : ¬ Small.{u} (Type u ⥤ Type u))

end CategoryTheory
