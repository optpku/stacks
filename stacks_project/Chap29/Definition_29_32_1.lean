module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import Mathlib.AlgebraicGeometry.Scheme
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

universe u

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/- Definition 29.32.1: for a morphism of schemes `f : X ⟶ S`, the sheaf of differentials
`Ω_{X/S}` is the sheaf of relative differentials of the underlying morphism of ringed spaces.
It is equipped with its universal `S`-derivation. -/
@[stacks 01UQ] #check
  (AlgebraicGeometry.RingedSpace.Hom.differentials f.toShHom :
    AlgebraicGeometry.RingedSpace.Modules X.toSheafedSpace)

/- The universal `S`-derivation of `Ω_{X/S}`. -/
#check
  (AlgebraicGeometry.RingedSpace.Hom.universalDerivation f.toShHom :
    AlgebraicGeometry.RingedSpace.Hom.derivations f.toShHom
      (AlgebraicGeometry.RingedSpace.Hom.differentials f.toShHom))

end AlgebraicGeometry
