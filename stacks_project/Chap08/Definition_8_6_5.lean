/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.6.5 -- Stacks in setoids

The canonical owner is `CategoryTheory.StackOver.Setoids`.  It is the full sub-bicategory of
stacks in groupoids selected by the fiberwise setoid condition; its object and hom views live in
the same ReasLib module so later constructions need not rebuild induced-bicategory coercions.
-/

namespace CategoryTheory

/- Definition 8.6.5: stacks in setoids over `(C, J)` form the full induced 2-category of
`StackOver.Groupoids J` selected by `Functor.IsFibered.InSetoids` on the projection. -/
@[stacks 0433 "stacks in setoids over a site"]
#check @StackOver.Setoids

#check @StackOver.Setoids.forget
#check @StackOver.Setoids.toGroupoids
#check @StackOver.Setoids.toSetoids
#check @StackOver.Setoids.toStackOver
#check @StackOver.Setoids.toFiberedCategoryOver
#check @StackOver.Setoids.mk
#check @StackOver.Setoids.mk.toSetoidsIso
#check @StackOver.Setoids.ofProjection
#check @StackOver.Setoids.Hom.toGroupoidsMor
#check @StackOver.Setoids.Hom.toSetoidsMor
#check @StackOver.Setoids.Hom.ofSetoidsMor
#check @StackOver.Setoids.Hom.lift
#check @StackOver.Setoids.Hom.isoMk
#check @StackOver.Setoids.Hom₂.toSetoidsNatTrans
#check @StackOver.Setoids.Hom₂.toBasedNatTrans
#check @StackOver.Setoids.Hom₂.toNatTrans
#check @StackOver.Setoids.homIsThin

end CategoryTheory
