module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pushforward.Injective
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.11 (02N5): pushforward along a flat morphism of ringed spaces preserves
injective module sheaves. -/
@[stacks 02N5]
#check @AlgebraicGeometry.RingedSpace.Hom.IsFlat.injective_pushforward

#check @AlgebraicGeometry.RingedSpace.Hom.IsFlat.pushforwardPreservesInjectives
