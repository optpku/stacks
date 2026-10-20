module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 26.4.1: the locally ringed-space closed-immersion predicate is the
ringed-space predicate on the underlying morphism. -/
@[stacks 01HK] #check LocallyRingedSpace.IsClosedImmersion
#check LocallyRingedSpace.IsClosedImmersion.iff
#check LocallyRingedSpace.Hom.kernelIdealSheaf
#check LocallyRingedSpace.Hom.kernelIdealSubobject
