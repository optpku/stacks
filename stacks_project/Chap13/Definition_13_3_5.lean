/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Homological
import StacksCheckRecall

@[expose] public section

/-!
# Source-facing bridge for Definition 13.3.5

The source's contravariant cohomological functor is modeled without a duplicate
predicate: `H : Dᵒᵖ ⥤ A` is homological on the opposite category, while
`H.rightOp : D ⥤ Aᵒᵖ` is its covariant opposite-valued homological form.
-/

namespace CategoryTheory

@[stacks 0147] #check @Functor.IsHomological
#check @Functor.map_distinguished_exact
#check @Functor.rightOp
#check @Functor.rightOp_isHomological

end CategoryTheory
