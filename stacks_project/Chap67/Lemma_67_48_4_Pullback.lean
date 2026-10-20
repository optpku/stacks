module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.pullbackToNormalization :
  ∀ {S : Scheme.{u}} {X Y W : AlgebraicSpace S} (f : X ⟶ Y) (g : W ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [HasPullback f g] [HasPullback (Hom.fromNormalization f) g],
    pullback f g ⟶ pullback (Hom.fromNormalization f) g)

end AlgebraicGeometry.AlgebraicSpace
