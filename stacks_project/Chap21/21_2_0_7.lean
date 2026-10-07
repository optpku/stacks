module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- 21.2.0.7 (071I): the higher direct image of a module sheaf is computed by applying module
pushforward to a chosen injective resolution and taking homology. -/
@[stacks 071I "module higher direct image from an injective resolution"]
#check @RingedSite.Hom.HigherDirectImage.isoHomologyPushforward

/- The functor and object owners used by the comparison. -/
#check @RingedSite.Hom.higherDirectImageModuleFunctor
#check @RingedSite.Hom.higherDirectImageModule
