/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap53.Example_53_15_2_Glueing_points_Evaluation

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Example 53.15.2 (Glueing points) -/
@[stacks 0C1J] #check (AlgebraicGeometry.unitsShortExact_of_glueingPoints :
    {k : Type u} → [Field k] → [IsAlgClosed k] →
    (X X' : SchemeOverField k) → [Algebraic X] → [Algebraic X'] →
    (f : X' ⟶ X) → [IsFinite f.left] →
    (a b : SchemeOverField.point k ⟶ X') →
    (x : SchemeOverField.point k ⟶ X) →
    (h_distinct : a ≠ b) →
    (ha : a ≫ f = x) → (hb : b ≫ f = x) →
    (U : X.left.Opens) →
    (hU : (U : Set X.left) =
      {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ) →
    [IsIso (f.left ∣_ U)] →
    (evalA evalB :
      (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf ⟶
        pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k) →
    (h_evalA : IsEvaluationAt f.left (SchemeOverField.rationalPoint a)
      (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalA) →
    (h_evalB : IsEvaluationAt f.left (SchemeOverField.rationalPoint b)
      (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalB) →
    (h_add_zero : additiveStructureMap f.left ≫
      additiveEvaluationDifference evalA evalB = 0) →
    (h_add_exact : (ShortComplex.mk (additiveStructureMap f.left)
      (additiveEvaluationDifference evalA evalB) h_add_zero).ShortExact) →
      (ShortComplex.mk (unitsStructureMap f.left)
      (unitsEvaluationDifference evalA evalB)
      (unitsStructureMap_comp_evaluationDifference f.left
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
        evalA evalB h_add_zero)).ShortExact)

end AlgebraicGeometry
