module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Injective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.12.1 support

The functorial preservation statement is owned by
`SheafOfModules.forgetPreservesInjectiveObjects` in ReasLib.
-/

/- Lemma 21.12.1 (03FB): the forgetful functor from module sheaves to module presheaves
preserves injective objects. -/
#check @SheafOfModules.forgetPreservesInjectiveObjects
