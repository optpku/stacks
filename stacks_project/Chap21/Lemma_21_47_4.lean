module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Characterization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.47.4

The intrinsic ringed-site characterization lives in `RingedSite.Hom.ModuleDerived`; this file is
only its tagged Chapter 21 source entry.
-/

/- Lemma 21.47.4 (08G8): a derived `𝒪_X`-module is perfect if and only if it is
pseudo-coherent and locally has finite Tor dimension. -/
@[stacks 08G8] #check
  @RingedSite.Hom.ModuleDerived.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension

#check @RingedSite.Hom.ModuleDerived.isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect
#check @RingedSite.Hom.ModuleDerived.isPseudoCoherent_of_isPerfect
#check @RingedSite.Hom.ModuleDerived.locallyHasFiniteTorDimension_of_isPerfect
#check @RingedSite.Hom.ModuleDerived.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension

end
