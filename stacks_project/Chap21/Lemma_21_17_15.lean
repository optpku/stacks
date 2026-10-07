module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tor.Flat
import StacksCheckRecall

@[expose] public section

/- Lemma 21.17.15 (08FG): a module sheaf is flat if and only if its first Tor with every module
sheaf vanishes. -/

@[stacks 08FG]
#check @RingedSite.Hom.ModuleDerived.Tor.isFlat_iff_isZero_tor_one

#check @RingedSite.Hom.ModuleDerived.Tor.isZero_tor_one_of_isFlat
#check @RingedSite.Hom.ModuleDerived.Tor.isFlat_of_isZero_tor_one

end
