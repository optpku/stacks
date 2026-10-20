module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
import StacksCheckRecall

/-!
# Remark 18.16.5

A left adjoint to extension of scalars can exist only along a flat ring map.
-/

@[expose] public section

open CategoryTheory
open ModuleCat

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) [(extendScalars.{u, u, u} f).IsRightAdjoint]

/- Remark 18.16.5 (04BI): if extension of scalars is a right adjoint, then the ring map is flat. -/
@[stacks 04BI]
#check (ExtendScalars.flat_of_isRightAdjoint f : f.Flat)
