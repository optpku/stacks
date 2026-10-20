module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 26.3.1: open immersions of locally ringed spaces are the
canonical predicate, characterized by an open embedding and stalkwise
isomorphisms. -/
@[stacks 01HE] #check LocallyRingedSpace.IsOpenImmersion
#check LocallyRingedSpace.IsOpenImmersion.iff_isIso_stalkMap
