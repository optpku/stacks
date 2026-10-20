module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Exact
import StacksCheckRecall

@[expose] public section

/- Lemma 17.17.10 (05NL): tensoring a flat right-augmented resolution on the right preserves its
exactness. -/
@[stacks 05NL]
#check @SheafOfModules.RingedSite.rightAugmentedExact_tensor_right_of_flat
