module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Basis.Refinement
import StacksCheckRecall

@[expose] public section

/- The categorical output of the refinement is a commutative square inducing an isomorphism on
cokernels. -/
#check @CategoryTheory.Limits.CokernelRefinement

/- The right side of the refinement square is the canonical map induced by the selected finite
subfamilies. -/
#check @SheafOfModules.Localization.Basis.SelectedCover.map

/- Lemma 18.30.9: a map between finite coproducts of basis structure modules admits a finite
basis refinement inducing an isomorphism on cokernels. -/
@[stacks 093F]
#check @SheafOfModules.Localization.Basis.existsFiniteCokernelRefinement

/- Sieve-saturated specialization. -/
#check @SheafOfModules.Localization.Basis.exists_finiteCokernelRefinement
