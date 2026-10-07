module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point

universe u

/- Lemma 29.16.4 (1): the finite type points of a scheme are exactly the union of the closed
points of its open subschemes, viewed in the ambient scheme. -/
@[stacks 02J2] #check
  (AlgebraicGeometry.finiteTypePoints_eq_iUnion_image_closedPoints_open :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.finiteTypePoints S =
        ⋃ U : S.Opens, (Subtype.val '' closedPoints U : Set S))

/- Lemma 29.16.4 (2): the same description of finite type points holds if the union is taken only
over the affine open subschemes of the scheme. -/
@[stacks 02J2] #check
  (AlgebraicGeometry.finiteTypePoints_eq_iUnion_image_closedPoints_affineOpen :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.finiteTypePoints S =
        ⋃ U : S.affineOpens, (Subtype.val '' closedPoints U.1 : Set S))
