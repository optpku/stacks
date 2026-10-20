module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing

/-!
# Dimension of local rings of algebraic spaces

The dimension of the local ring of an algebraic space at a point is the common Krull dimension
of the stalks of étale scheme charts through that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt : Points X → WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_eq_ringKrullDim_stalk :
  ∀ {U : Over S} (f : ofOver U ⟶ X),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f →
    ∀ (u : U.left) {x : Points X}, Points.mapOfOver f u = x →
      localRingDimAt x = ringKrullDim (U.left.presheaf.stalk u))

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_ofOver :
  ∀ (T : Over S) (t : T.left),
    localRingDimAt (ofOver.pointsEquiv T t) = ringKrullDim (T.left.presheaf.stalk t))

end AlgebraicGeometry.AlgebraicSpace
