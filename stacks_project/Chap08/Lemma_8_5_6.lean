/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.5.6: the canonical two-fibre product in stacks in groupoids. -/
#check @StackOver.Groupoids.TwoFibreProduct.apex
#check @StackOver.Groupoids.TwoFibreProduct.apex.toGroupoids
#check @StackOver.Groupoids.TwoFibreProduct.fst
#check @StackOver.Groupoids.TwoFibreProduct.fst.hom
#check @StackOver.Groupoids.TwoFibreProduct.snd
#check @StackOver.Groupoids.TwoFibreProduct.snd.hom
#check @StackOver.Groupoids.TwoFibreProduct.comparisonIso
#check @StackOver.Groupoids.TwoFibreProduct.comparisonIso.hom
#check @StackOver.Groupoids.TwoFibreProduct.comparisonIso.inv
#check @StackOver.Groupoids.TwoFibreProduct.cone
#check @StackOver.Groupoids.TwoFibreProduct.cone.pt
#check @StackOver.Groupoids.TwoFibreProduct.cone.fst
#check @StackOver.Groupoids.TwoFibreProduct.cone.snd
#check @StackOver.Groupoids.TwoFibreProduct.cone.iso
#check @StackOver.Groupoids.TwoFibreProduct.cone.isBilimit

@[stacks 02ZL "two-fibre products of stacks in groupoids"]
#check @StackOver.Groupoids.hasPseudoPullbacks

end CategoryTheory
