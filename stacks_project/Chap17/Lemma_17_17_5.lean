module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Colimits
import StacksCheckRecall

@[expose] public section

/- Lemma 17.17.5 (05NG) (1): filtered colimits of flat module sheaves are flat. -/
@[stacks 05NG "(1)"]
#check @SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered

/- Lemma 17.17.5 (05NG) (2): arbitrary coproducts of flat module sheaves are flat. -/
@[stacks 05NG "(2)"]
#check @SheafOfModules.RingedSite.isFlat_coproduct
