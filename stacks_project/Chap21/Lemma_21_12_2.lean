module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.12.2

The module-valued cohomology presheaf and its comparison with the underlying additive
cohomology presheaf are provided by the reusable ringed-site cohomology API.
-/

open SheafOfModules

@[stacks 06YK "module-valued cohomology presheaf functor"]
#check @cohomologyPresheafFunctor

@[stacks 06YK "module-valued cohomology presheaf"]
#check @cohomologyPresheaf

@[stacks 06YK "cohomology evaluated at an object of the site"]
#check @cohomologyAtObjectFunctor

@[stacks 06YK "underlying additive cohomology presheaf comparison"]
#check @cohomologyPresheafFunctor_toPresheaf_isomorphic

@[stacks 06YK "objectwise underlying additive cohomology presheaf comparison"]
#check @cohomologyPresheaf_toPresheaf_isomorphic

@[stacks 06YK "cohomology comparison after evaluation at a site object"]
#check @cohomologyAtObject_isomorphic
