/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Squishing.Picard

@[expose] public section

open CategoryTheory TopCat
open scoped AlgebraicGeometry DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 53.15.6 (1): a squishing of a tangent vector yields an exact and
surjective sequence `k →+ X.left.PicardGroup →+ X'.left.PicardGroup`. -/
@[stacks 0C1N]
#check (AlgebraicGeometry.exists_picardSquishingExact :
    {k : Type u} → [Field k] → [IsAlgClosed k] →
    (X X' : SchemeOverField k) → [Algebraic X] → [Algebraic X'] →
    (f : X' ⟶ X) →
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left) →
    (x : SchemeOverField.point k ⟶ X) →
    (U : X.left.Opens) →
    (tangentEvaluation :
      additiveSheaf
        ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
      additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)) →
    (maps : SquishingTangentMaps X X' f vartheta x) →
    (squishing : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) →
    ∃ δ : k →+ X.left.PicardGroup,
      ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
        Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
          Function.Surjective (Scheme.Hom.picardPullback f.left))

/- Lemma 53.15.6 (2): if `X'` is proper and reduced, the first map in the
exact Picard sequence supplied by a tangent-vector squishing is injective. -/
@[stacks 0C1N]
#check (AlgebraicGeometry.exists_picardSquishingExactWithInjective :
    {k : Type u} → [Field k] → [IsAlgClosed k] →
    (X X' : SchemeOverField k) → [Algebraic X] → [Algebraic X'] →
    [IsProper X'.hom] → [IsReduced X'.left] →
    (f : X' ⟶ X) →
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left) →
    (x : SchemeOverField.point k ⟶ X) →
    (U : X.left.Opens) →
    (tangentEvaluation :
      additiveSheaf
        ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
      additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)) →
    (maps : SquishingTangentMaps X X' f vartheta x) →
    (squishing : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) →
    ∃ δ : k →+ X.left.PicardGroup,
      ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
        Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
          Function.Surjective (Scheme.Hom.picardPullback f.left) ∧
            Function.Injective δ)

end AlgebraicGeometry
