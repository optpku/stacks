module

public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.42.5 (0A8V): composition of derived internal Homs on a ringed space is the
source-order composition map in any braided closed monoidal category. -/
@[stacks 0A8V]
#check @CategoryTheory.MonoidalClosed.Source.comp

#check @CategoryTheory.MonoidalClosed.Source.comp_spec

end AlgebraicGeometry.RingedSpace
