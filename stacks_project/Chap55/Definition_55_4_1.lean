module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Picard

/- Definition 55.4.1: the Picard group of a numerical type is the cokernel of the
integral matrix whose `(i, j)` entry is the intersection number divided by the
weight of row `i`; equivalently, the `i`th standard basis vector maps to the
vector with `j`th coordinate `T.intersection i j / T.weight j`. -/
@[stacks 0C7H] #check (NumericalType.PicardGroup : (T : NumericalType) → Type)
