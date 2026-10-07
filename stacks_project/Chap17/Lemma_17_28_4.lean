module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials
import StacksCheckRecall

@[expose] public section

/- Lemma 17.28.4 (08TD): relative differentials are obtained by sheafifying the objectwise
presheaf of Kähler differentials. -/
@[stacks 08TD]
#check @SheafOfModules.RingedSite.relativeDifferentials_def

#check @TopCat.Sheaf.relativeDifferentials_def
