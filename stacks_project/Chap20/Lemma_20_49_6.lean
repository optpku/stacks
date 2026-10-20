module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.6: derived pullback along a morphism of ringed spaces preserves perfect
derived module sheaves. -/
@[stacks 09UA]
#check @AlgebraicGeometry.RingedSpace.modulePullbackDerived_isPerfect
