/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Squishing.TangentVector

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf
open TopCat.Sheaf.Skyscraper
open scoped AlgebraicGeometry DualNumber

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

/- Example 53.15.3 (Squishing a tangent vector) -/
@[stacks 0C1K]
#check (AlgebraicGeometry.SquishesTangentVector :
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
    (maps : SquishingTangentMaps X X' f vartheta x) → Prop)

#check (AlgebraicGeometry.unitsShortExact_of_squishesTangentVector :
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
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) →
    (ShortComplex.mk (unitsStructureMap f.left)
      (dlogEvaluationOf X X' f vartheta x maps)
      (dlogEvaluationOf_zero X X' f vartheta x U tangentEvaluation maps h)).ShortExact)

end AlgebraicGeometry

end
