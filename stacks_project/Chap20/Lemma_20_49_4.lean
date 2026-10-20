module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Characterization
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.4: Tor-amplitude in `[a, b]`, with `a ≤ b`, and
`(a - 1)`-pseudo-coherence imply perfectness. -/
@[stacks 08CP]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent

#check @AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
