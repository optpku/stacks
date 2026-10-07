module

public import ReasLib.Algebra.Category.ModuleCat.Filtration.Counterexample
import StacksCheckRecall

@[expose] public section

/-!
# Example 12.3.13

Compatibility facade for the filtered-module counterexample to abelianness.
-/

/- Example 12.3.13 [0108]: filtered vector spaces over a field are not an abelian category;
the reusable result holds for filtered modules over every nontrivial ring. -/
@[stacks 0108]
#check @ModuleCat.FilteredObject.not_nonempty_abelian
