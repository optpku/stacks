module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
import StacksCheckRecall

@[expose] public section

/- Lemma 17.16.2: for presheaves of `𝒪_X`-modules `ℱ'` and `𝒢'`, the tensor product of
their sheafifications is canonically identified with the sheafification of their presheaf tensor
product. -/
@[stacks 05NA]
#check @SheafOfModules.RingedSite.ModuleSheafification.tensorIso
