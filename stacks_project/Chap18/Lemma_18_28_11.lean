module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Exact
import StacksCheckRecall

/-!
# Lemma 18.28.11

Tensoring an exact right-augmented resolution by flat objects preserves exactness.  The sequence
predicate and theorem live at the neutral monoidal-abelian layer; this file recalls its module
presheaf and module sheaf interfaces.
-/

@[expose] public section

/- Lemma 18.28.11 (1) (03EZ): the module-presheaf specialization. -/
@[stacks 03EZ "(1)"]
#check @PresheafOfModules.rightAugmentedExact_tensor_right_of_flat

/- Lemma 18.28.11 (2) (03EZ): the module-sheaf specialization. -/
@[stacks 03EZ "(2)"]
#check @SheafOfModules.RingedSite.rightAugmentedExact_tensor_right_of_flat

/- The reusable predicate for a right-augmented exact sequence. -/
#check @CategoryTheory.RightAugmentedExact

/- The category-level tensor exactness theorem. -/
#check @CategoryTheory.RightAugmentedExact.map_tensorRight
