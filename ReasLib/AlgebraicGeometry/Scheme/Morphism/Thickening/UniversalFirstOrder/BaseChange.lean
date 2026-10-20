module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.BaseChange

/-!
# Universal first-order thickenings and base change

Universality to first order is preserved by cartesian base change. For a formally unramified
closed part, the canonical comparison between universal first-order thickenings is flat under
flat base change, and the associated conormal comparison is an epimorphism.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

/-- Universality to first order is preserved by a cartesian base change of both the closed
and ambient schemes of a thickening. -/
theorem of_isPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (T : Thickening.Over X) (U : Thickening.Over Y)
    (k : (Thickening.Over.map g).obj T ⟶ U)
    (leftSq : IsPullback k.left.left T.left.hom U.left.hom g)
    (rightSq : IsPullback k.right.left T.right.hom U.right.hom g)
    [IsUniversalFirstOrder U] : IsUniversalFirstOrder T := sorry

/-- If the target closed part is formally unramified, the ambient component of the canonical
comparison between universal first-order thickenings is flat when the base morphism is flat. -/
instance comparison_flat {X Y : Scheme.{u}} (g : X ⟶ Y)
    (T : Thickening.Over X) (U : Thickening.Over Y)
    [FormallyUnramified U.left.hom]
    [IsUniversalFirstOrder T] [IsUniversalFirstOrder U]
    (f : T.left.left ⟶ U.left.left)
    (sq : IsPullback f T.left.hom U.left.hom g) [Flat g] :
    Flat (comparison g T U f sq.toCommSq).right.left := sorry

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (T : Thickening.Over X) (U : Thickening.Over Y)
  (k : (Thickening.Over.map g).obj T ⟶ U)
  (leftSq : IsPullback k.left.left T.left.hom U.left.hom g)
  (rightSq : IsPullback k.right.left T.right.hom U.right.hom g)
  [h_unramified : FormallyUnramified U.left.hom]
  [h_universal : IsUniversalFirstOrder U]

include rightSq h_unramified h_universal

/-- For a cartesian base change of a universal first-order thickening along a formally
unramified closed part, the canonical conormal comparison is an epimorphism. -/
theorem conormalMap_epi : Epi (Scheme.Hom.Conormal.map leftSq.toCommSq) := sorry

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
