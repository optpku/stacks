module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints.Etale
import StacksCheckRecall

/-!
# Identification of finite-type points of an algebraic space

The finite-type points of an algebraic space are the images of closed points of
schemes under étale morphisms, and the same description holds if those schemes
are required to be affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.25.3 (1): The finite-type points are the union of the images of
closed points under all étale morphisms from schemes. -/
@[stacks 06EH] #check (AlgebraicGeometry.AlgebraicSpace.finiteTypePoints_eq_iUnion_image_closedPoints_etale :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    finiteTypePoints X =
      ⋃ (U : Over S) (φ : ofOver U ⟶ X) (_ : Etale φ),
        Points.mapOfOver φ '' closedPoints U.left)

/- Lemma 67.25.3 (2): The same equality holds when the source schemes are
required to be affine. -/
@[stacks 06EH] #check (AlgebraicGeometry.AlgebraicSpace.finiteTypePoints_eq_iUnion_image_closedPoints_affine_etale :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    finiteTypePoints X =
      ⋃ (U : Over S) (_ : AlgebraicGeometry.IsAffine U.left)
        (φ : ofOver U ⟶ X) (_ : Etale φ),
        Points.mapOfOver φ '' closedPoints U.left)

end AlgebraicGeometry.AlgebraicSpace
