module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Characterization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.47.3

The reusable ringed-site criterion is owned by
`RingedSite.Hom.ModuleDerived.isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent`.
This item is a direct canonical recall.
-/

/- Lemma 21.47.3 (08G7): if `E` has Tor-amplitude in `[a, b]` and is
`(a - 1)`-pseudo-coherent, then
`E` is perfect. -/
@[stacks 08G7]
#check @RingedSite.Hom.ModuleDerived.isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent
