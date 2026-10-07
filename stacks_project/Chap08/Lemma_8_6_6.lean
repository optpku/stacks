module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Two-fibre products of stacks in setoids

The explicit carrier, projections, comparison cone, and bilimit are owned by
`StackOver.Setoids.TwoFibreProduct`.
-/

namespace CategoryTheory

/- Lemma 8.6.6 (0434): the canonical two-fibre product in stacks in setoids. -/
#check @StackOver.Setoids.TwoFibreProduct.apex
#check @StackOver.Setoids.TwoFibreProduct.apex.toGroupoids
#check @StackOver.Setoids.TwoFibreProduct.apex.toSetoids
#check @StackOver.Setoids.TwoFibreProduct.fst
#check @StackOver.Setoids.TwoFibreProduct.fst.hom
#check @StackOver.Setoids.TwoFibreProduct.fst.toSetoidsMor
#check @StackOver.Setoids.TwoFibreProduct.snd
#check @StackOver.Setoids.TwoFibreProduct.snd.hom
#check @StackOver.Setoids.TwoFibreProduct.snd.toSetoidsMor
#check @StackOver.Setoids.TwoFibreProduct.comparisonIso
#check @StackOver.Setoids.TwoFibreProduct.comparisonIso.hom
#check @StackOver.Setoids.TwoFibreProduct.comparisonIso.inv
#check @StackOver.Setoids.TwoFibreProduct.cone
#check @StackOver.Setoids.TwoFibreProduct.cone.pt
#check @StackOver.Setoids.TwoFibreProduct.cone.fst
#check @StackOver.Setoids.TwoFibreProduct.cone.snd
#check @StackOver.Setoids.TwoFibreProduct.cone.iso

/- The explicit cone is the standard pseudo-pullback described in Categories, Lemma 4.32.3. -/
@[stacks 0434 "standard pseudo-pullback description"]
#check @StackOver.Setoids.TwoFibreProduct.cone.isBilimit

@[stacks 0434 "two-fibre products of stacks in setoids"]
#check @StackOver.Setoids.hasPseudoPullbacks

end CategoryTheory
