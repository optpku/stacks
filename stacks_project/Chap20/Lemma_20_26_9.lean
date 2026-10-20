module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.KFlat.BoundedAbove

@[expose] public section

/- @stack 06YD -/

open AlgebraicGeometry CategoryTheory
open SheafOfModules.RingedSite

/- Lemma 20.26.9 (06YD): bounded-above complexes with flat terms are K-flat. -/
@[stacks 06YD "bounded-above flat complexes are K-flat"]
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsTermwiseFlat.isKFlat_of_boundedAbove_of_flat

#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsTermwiseFlat.isKFlat_of_boundedAbove
#check @HomologicalComplex.IsTermwiseFlat.isKFlat_of_boundedAbove

end
