module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator.Coherent
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import StacksCheckRecall

@[expose] public section

/- Lemma 17.23.4 (0H2L): if the structure module and `F` are coherent, then `Ann(F)` is
coherent. -/
@[stacks 0H2L]
#check @SheafOfModules.Annihilator.isCoherent

/- The two reusable closure steps used by the statement live outside the chapter. -/
#check @AlgebraicGeometry.RingedSpace.InternalHom.isCoherent
#check @SheafOfModules.IsCoherent.kernel
