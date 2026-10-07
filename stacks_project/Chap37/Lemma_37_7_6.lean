module

public import stacks_project.Chap37.Lemma_37_7_6_BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (T : Thickening.Over X) (U : Thickening.Over Y)
  (k : (Thickening.Over.map g).obj T ⟶ U)
  (leftSq : IsPullback k.left.left T.left.hom U.left.hom g)
  (rightSq : IsPullback k.right.left T.right.hom U.right.hom g)
  [h_unramified : FormallyUnramified U.left.hom]
  [h_universal : IsUniversalFirstOrder U]

/- Lemma 37.7.6 (1): a cartesian base change of a formally unramified morphism is formally
unramified. -/
@[stacks 04F8] #check
  (AlgebraicGeometry.FormallyUnramified.isStableUnderBaseChange.of_isPullback leftSq
    (inferInstance : FormallyUnramified U.left.hom) :
      FormallyUnramified T.left.hom)

/- Lemma 37.7.6 (2): the cartesian base change of a universal first-order thickening is
universal to first order. -/
@[stacks 04F8] #check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.of_isPullback
    g T U k leftSq rightSq : IsUniversalFirstOrder T)

/- Lemma 37.7.6 (3): for the cartesian base change of a universal first-order thickening
along a formally unramified closed part, the canonical conormal comparison is an epimorphism. -/
@[stacks 04F8] #check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.conormalMap_epi
    g T U k leftSq rightSq :
      Epi (Scheme.Hom.Conormal.map leftSq.toCommSq))

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
