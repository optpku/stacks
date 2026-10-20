module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.LeftLegDiagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {U : Type (max u v)} [Category.{v} U]
variable {X : Type (max u v)} [Category.{v} X]
variable {V : Type (max u v)} [Category.{v} V]
variable {Y : Type (max u v)} [Category.{v} Y]
variable {F : X ⥤ Y} {G : V ⥤ Y}
variable (P : CategoricalPullback.CatCommSqOver F G U)
variable [P.IsBilimit]

/- Lemma 4.31.14: if `P` is a `2`-fibre-product square, then the square induced by its left leg
and the two diagonal functors is again a `2`-fibre-product square. -/
@[stacks 04YR]
#check (CategoricalPullback.CatCommSqOver.LeftLegDiagonal.square.isBilimit P :
  (CategoricalPullback.CatCommSqOver.LeftLegDiagonal.square P).IsBilimit)
