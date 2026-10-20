module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Squishing.TangentVector

@[expose] public section

open CategoryTheory TopCat
open scoped AlgebraicGeometry DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A tangent-vector squishing induces an exact, surjective sequence on Picard groups. -/
theorem exists_picardSquishingExact
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (U : X.left.Opens)
    (tangentEvaluation :
      additiveSheaf
        ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
      additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
    (maps : SquishingTangentMaps X X' f vartheta x)
    (squishing : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) :
    ∃ δ : k →+ X.left.PicardGroup,
      ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
        Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
          Function.Surjective (Scheme.Hom.picardPullback f.left) := sorry

/-- A proper, reduced target of a tangent-vector squishing makes the first Picard map injective. -/
theorem exists_picardSquishingExactWithInjective
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    [IsProper X'.hom] [IsReduced X'.left]
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (U : X.left.Opens)
    (tangentEvaluation :
      additiveSheaf
        ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
      additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
    (maps : SquishingTangentMaps X X' f vartheta x)
    (squishing : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) :
    ∃ δ : k →+ X.left.PicardGroup,
      ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
        Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
          Function.Surjective (Scheme.Hom.picardPullback f.left) ∧
            Function.Injective δ := sorry

end AlgebraicGeometry
