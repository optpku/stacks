module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.4.6 (026G): the `(2, 1)`-category of stacks over a site has two-fibre products, and
the chosen explicit cone has the standard pseudo-pullback universal property. -/
#check @BasedCategory.PseudoPullback.isStackOnSite
#check @StackOver.TwoFibreProduct.apex
#check @StackOver.TwoFibreProduct.fst
#check @StackOver.TwoFibreProduct.snd
#check @StackOver.TwoFibreProduct.comparisonIso
#check @StackOver.TwoFibreProduct.cone
/- The explicit cone is the standard pseudo-pullback described in Categories, Lemma 4.32.3. -/
@[stacks 026G "standard pseudo-pullback description"]
#check @StackOver.TwoFibreProduct.cone.isBilimit

@[stacks 026G "two-fibre products of stacks"]
#check @StackOver.hasPseudoPullbacks

end CategoryTheory
