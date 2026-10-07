module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.BaseChange

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (T : Thickening.Over X) (U : Thickening.Over Y)
  (k : (Thickening.Over.map g).obj T ⟶ U)
  (leftSq : IsPullback k.left.left T.left.hom U.left.hom g)
  (rightSq : IsPullback k.right.left T.right.hom U.right.hom g)
  [IsUniversalFirstOrder U]

/- The universal-first-order base-change API remains available through this source-facing
compatibility module. -/
#check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.of_isPullback
    g T U k leftSq rightSq : IsUniversalFirstOrder T)

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
