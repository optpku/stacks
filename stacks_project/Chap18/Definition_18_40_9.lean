module

public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 18.40.9 (04HA): locality is a property of the bundled ringed-site morphism and its
canonical inverse-image structure-sheaf map. -/
@[stacks 04HA]
#check @RingedSite.Hom.IsLocal

#check @RingedSite.Hom.isLocal_iff
#check @RingedSite.Hom.isLocal_iff_unitsSquare
