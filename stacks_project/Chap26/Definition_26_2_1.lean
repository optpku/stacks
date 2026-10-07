module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 26.2.1: locally ringed spaces, their local rings and residue
fields, and the induced maps on stalks and residue fields use the canonical
mathlib owners. -/
@[stacks 01HB] #check LocallyRingedSpace
@[stacks 01HB] #check LocallyRingedSpace.Hom
#check LocallyRingedSpace.Hom.stalkMap
@[stacks 01HB] #check LocallyRingedSpace.residueField
#check LocallyRingedSpace.residueFieldMap

variable {X Y : LocallyRingedSpace.{u}} (x : X) (f : X ⟶ Y)

#check (inferInstance : IsLocalRing (X.presheaf.stalk x))
#check (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
#check f.stalkMap x
@[stacks 01HB] #check LocallyRingedSpace.isLocalHomStalkMap f x
#check LocallyRingedSpace.residueFieldMap f x
