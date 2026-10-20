module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Closure
import StacksCheckRecall

@[expose] public section

/-!
# Setoid closure of the stack two-fibre product

Faithfulness of a morphism with setoid source is supplied by the general based-functor instance;
the source-facing closure corollary is owned by `StackOver.Groupoids.TwoFibreProduct`, matching
the ambient groupoid two-fibre-product construction in its conclusion.
-/

namespace CategoryTheory

#check @BasedFunctor.faithfulOfSource

/- Lemma 8.6.8: the ambient two-fibre product of setoid sources is a stack in setoids. -/
@[stacks 05UJ]
#check @StackOver.Groupoids.TwoFibreProduct.isStackInSetoids_of_sources

end CategoryTheory
