/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
import StacksCheckRecall

@[expose] public section

/-!
Definition 17.28.10 (08RT): for a morphism `f : X ⟶ S` of ringed spaces and an
`𝒪_X`-module `F`, an `S`-derivation into `F` is a derivation relative to the inverse-image
structure map `f⁻¹𝒪_S ⟶ 𝒪_X`.  The representing object is `Ω_{X/S}`, equipped with its
universal derivation `d_{X/S}`.
-/

/- Definition 17.28.10 (08RT) (1): the type of `S`-derivations into `F`. -/
@[stacks 08RT "(1)"]
#check @AlgebraicGeometry.RingedSpace.Hom.derivations

/- Definition 17.28.10 (08RT) (2): the sheaf `Ω_{X/S}` of relative differentials. -/
@[stacks 08RT "(2)"]
#check @AlgebraicGeometry.RingedSpace.Hom.differentials

/- Definition 17.28.10 (08RT) (3): the universal derivation `d_{X/S}`. -/
@[stacks 08RT "(3)"]
#check @AlgebraicGeometry.RingedSpace.Hom.universalDerivation

#check @AlgebraicGeometry.RingedSpace.Hom.differentialDesc
#check @AlgebraicGeometry.RingedSpace.Hom.differentialDesc_fac
#check @AlgebraicGeometry.RingedSpace.Hom.derivationsFunctor
#check @AlgebraicGeometry.RingedSpace.Hom.homEquiv
#check @AlgebraicGeometry.RingedSpace.Hom.corepresentableBy
#check @AlgebraicGeometry.RingedSpace.Hom.representingIso
#check @AlgebraicGeometry.RingedSpace.Hom.differentials_representsDerivations
