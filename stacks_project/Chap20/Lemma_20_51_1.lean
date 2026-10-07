module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.HomotopyColimit
import StacksCheckRecall

@[expose] public section

/- Lemma 20.51.1 (0DJI): if `K` is a sequential diagram of perfect objects of
`D(𝒪_X)` and `Khocolim` is its homotopy colimit, then `(ihom Khocolim).obj E` is the
homotopy limit of the inverse system `n ↦ E ⊗ MonoidalClosed.dual (K.obj n)`. -/
@[stacks 0DJI]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.internalHom_homotopyLimit_of_isPerfect

#check @CategoryTheory.MonoidalClosed.InternalHom.tower
#check @CategoryTheory.MonoidalClosed.Dual.tensorTower
#check @CategoryTheory.MonoidalClosed.Dual.tensorComparisonHom
