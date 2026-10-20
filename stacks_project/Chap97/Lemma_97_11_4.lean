module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.Cartesian
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 97.11.4: for morphisms `X ⟶ Z ⟶ B` of algebraic spaces over an arbitrary
scheme `S`, restriction of scalars is the fibre of postcomposition along the identity
section, as a cartesian square of fppf sheaves on schemes over `S`. -/
@[stacks 05YE] #check
  (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.isPullback :
    ∀ {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B),
      IsPullback (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.toRelativeHom f g)
        (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.toBase f g)
        (AlgebraicGeometry.AlgebraicSpace.RelativeHom.postcomp f g)
        (AlgebraicGeometry.AlgebraicSpace.RelativeHom.idSection g))
