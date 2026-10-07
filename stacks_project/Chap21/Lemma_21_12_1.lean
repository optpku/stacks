module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Injective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.12.1

The reusable owner is the functorial preservation instance in ReasLib. Its standard
`Functor.injective_obj_of_injective` projection is exactly the objectwise textbook statement.
-/

/- Lemma 21.12.1 (03FB): forgetting a sheaf of modules to its underlying presheaf of modules
preserves injective objects. -/
@[stacks 03FB] #check @SheafOfModules.forgetPreservesInjectiveObjects

end
