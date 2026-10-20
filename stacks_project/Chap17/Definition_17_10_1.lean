module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
import StacksCheckRecall

/-!
# Quasicoherent modules

The defining predicate is the canonical Mathlib class `SheafOfModules.IsQuasicoherent`; ReasLib
names its full subcategory `RingedSpace.QCoh`.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Definition 17.10.1 (1) (01BE): a module sheaf on a ringed space is quasicoherent when it has
the canonical local free presentation property. -/
@[stacks 01BE "(1)"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) ↦ F.IsQuasicoherent

/- Definition 17.10.1 (2) (01BE): `X.QCoh` is the category of quasicoherent module sheaves on
`X`. -/
@[stacks 01BE "(2)"]
#check fun (X : RingedSpace.{u}) ↦ X.QCoh

end AlgebraicGeometry
