module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Sheafification
import StacksCheckRecall

/-!
# Lemma 18.28.4

The coverwise section criterion is stated directly at the presheaf-to-sheafification boundary;
no chapter-local aliases or monoidal instances are needed.
-/

@[expose] public section

/- Lemma 18.28.4 (0GN1): coverwise flat section modules imply flat sheafification. -/
@[stacks 0GN1]
#check @PresheafOfModules.sheafification_isFlat_of_locally_flat
