module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cohomology
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.4 (06YK): after forgetting its module structure, the module-valued cohomology
presheaf is the cohomology presheaf of the underlying additive sheaf. -/
@[stacks 06YK]
#check @SheafOfModules.cohomologyPresheaf_toPresheaf_isomorphic

#check @SheafOfModules.cohomologyPresheafFunctor_toPresheaf_isomorphic
#check @SheafOfModules.cohomologyAtObject_isomorphic
