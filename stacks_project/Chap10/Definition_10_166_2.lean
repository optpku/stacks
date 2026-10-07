module

public import ReasLib.FieldTheory.GeometricRegularity
import StacksCheckRecall

/-!
# Definition 10.166.2

@stack 0382
-/

@[expose] public section

/- Definition 10.166.2: a Noetherian algebra over a field `k` is geometrically regular over `k`
when `Algebra.IsGeometricallyRegular` holds, i.e. when the equivalent conditions of
Lemma 10.166.1 hold. -/
@[stacks 0382]
#check @Algebra.IsGeometricallyRegular
@[stacks 0382]
#check @Algebra.IsGeometricallyRegular.isRegularRing_baseChange
@[stacks 0382]
#check @Algebra.IsGeometricallyRegular.iff_tensorRegular
