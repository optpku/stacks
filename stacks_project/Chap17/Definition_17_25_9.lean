module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Picard
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped RingedSpacePicard

/- Definition 17.25.9 (01CX): `Pic(X)` is the group of isomorphism classes of invertible
`𝒪_X`-modules under tensor product. -/
@[stacks 01CX]
#check @AlgebraicGeometry.RingedSpace.PicardGroup

#check @AlgebraicGeometry.RingedSpace.Modules.picardClass
#check @AlgebraicGeometry.RingedSpace.PicardGroup.repr
#check @AlgebraicGeometry.RingedSpace.PicardGroup.reprPicardClassIso
#check @AlgebraicGeometry.RingedSpace.PicardGroup.picardClass_eq_iff
#check @AlgebraicGeometry.RingedSpace.PicardGroup.picardClass_unit
#check @AlgebraicGeometry.RingedSpace.PicardGroup.picardClass_eq_zero_iff
#check @AlgebraicGeometry.RingedSpace.PicardGroup.picardClass_tensor
#check @AlgebraicGeometry.RingedSpace.PicardGroup.reprZeroIso
#check @AlgebraicGeometry.RingedSpace.PicardGroup.reprAddIso
#check @AlgebraicGeometry.RingedSpace.PicardGroup.reprNegIso
