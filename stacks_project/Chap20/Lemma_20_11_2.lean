module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Comparison
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.2 (01EQ): an indexed open cover has a coefficient-natural comparison from its
Cech complex to bounded-below derived sections; taking homology gives all degreewise comparison
maps from the same derived datum. -/
@[stacks 01EQ]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.Comparison.exists_normalized
#check @AlgebraicGeometry.RingedSpace.ModuleCech.Comparison.exists_normalized_of_iSup_eq

#check @AlgebraicGeometry.RingedSpace.ModuleCech.derivedSourceHomologyIso
#check @AlgebraicGeometry.RingedSpace.ModuleCech.Comparison.degree
#check @AlgebraicGeometry.RingedSpace.ModuleCech.Comparison.app
