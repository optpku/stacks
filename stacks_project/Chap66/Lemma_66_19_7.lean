module

public import stacks_project.Chap66.Lemma_66_19_7_Point
import StacksCheckRecall

open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/- Lemma 66.19.7 (1): let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`xbar` be a geometric point of `X`. The functor `u : X_étale ⥤ Type` sending `U` to `|U_xbar|`,
equivalently the Hom-lifts of `xbar` through `U`, is the fiber of a point `p` of the site
`X_étale` (Sites, Definition 7.32.2). -/
@[stacks 04K0] #check toSmallEtalePoint

/- Lemma 66.19.7 (2): the associated stalk functor `F ↦ F_p` (Sites, Equation 7.32.1.1) is
the geometric stalk functor `F ↦ F_xbar` of Definition 66.19.6. -/
@[stacks 04K0] #check toSmallEtalePoint_stalkIso
