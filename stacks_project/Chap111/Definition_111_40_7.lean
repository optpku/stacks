module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped SpecOfNotation RingedSpacePicard

universe u

section

variable (X : LocallyRingedSpace.{u})

/- Definition 111.40.7 (1): the Picard group of a locally ringed space is the group of
isomorphism classes of invertible `𝒪_X`-modules under tensor product. -/
@[stacks 02AM]
#check (AlgebraicGeometry.RingedSpace.PicardGroup X.toRingedSpace : Type (u + 1))

#check (inferInstance : AddCommGroup X.toRingedSpace.PicardGroup)
#check (Pic(X.toRingedSpace) : Type _)

end

section

variable (R : Type u) [CommRing R]

/- Definition 111.40.7 (2): for a ring `R`, `Pic(R)` is defined to be `Pic(Spec(R))`. -/
@[stacks 02AM]
#check (AlgebraicGeometry.Scheme.PicardGroup (Spec(R)) : Type (u + 1))

#check (Scheme.PicardGroup (Spec(R)) : Type _)
#check (inferInstance : AddCommGroup (Spec(R)).toRingedSpace.PicardGroup)

end

#check @AlgebraicGeometry.RingedSpace.PicardGroup
#check @AlgebraicGeometry.RingedSpace.Modules.picardClass
#check @AlgebraicGeometry.RingedSpace.PicardGroup.picardClass_tensor
#check @AlgebraicGeometry.RingedSpace.PicardGroup.picardClass_eq_iff
#check @AlgebraicGeometry.Scheme.PicardGroup
