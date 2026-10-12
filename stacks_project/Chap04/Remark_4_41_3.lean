/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoYoneda.Comparison.Equivalence
import StacksCheckRecall

@[expose] public section

universe v u vAux uAux

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {S : Type (max uAux (max vAux (max u v)))}
  [Category.{max vAux (max u v)} S]
variable (p : S ⥤ C) [Functor.IsFibered.InGroupoids p]

/- Remark 4.41.3: the split `2`-Yoneda co-Grothendieck model is equivalent over the base to the
original category fibred in groupoids. -/
@[stacks 076J]
#check (TwoYoneda.splitToOriginal.equivalence.{v, u, vAux, uAux} p :
  TwoYoneda.splitModel p ≌ BasedCategory.ofFunctor p)

end CategoryTheory
