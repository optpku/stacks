/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Points
public import ReasLib.AlgebraicGeometry.Scheme.Squishing.TangentVector

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open TopCat.Sheaf
open scoped AlgebraicGeometry DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The geometric and additive sheaf data for gluing two distinct rational points of `Y`
over a point of `X`. -/
structure GlueingPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X : SchemeOverField k) (hY : Algebraic Y) (hX : Algebraic X)
    (g : Y ⟶ X)
    (a b : SchemeOverField.point k ⟶ Y)
    (x : SchemeOverField.point k ⟶ X)
    (U : X.left.Opens)
    (evalA evalB :
      (TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Y.left.sheaf ⟶
        pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k) : Prop where
  /-- The two source points are distinct. -/
  distinct : a ≠ b
  /-- The first source point maps to the chosen target point. -/
  first_maps_to : a ≫ g = x
  /-- The second source point maps to the chosen target point. -/
  second_maps_to : b ≫ g = x
  /-- The morphism is finite. -/
  finite : IsFinite g.left
  /-- `U` is the complement of the rational point represented by `x`. -/
  complement :
    (U : Set X.left) =
      {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ
  /-- The restriction of `g` over the complement of `x` is an isomorphism. -/
  restriction_isIso : IsIso (g.left ∣_ U)
  /-- The first evaluation map is evaluation at the first source point. -/
  evaluationA : IsEvaluationAt g.left (SchemeOverField.rationalPoint a)
    (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalA
  /-- The second evaluation map is evaluation at the second source point. -/
  evaluationB : IsEvaluationAt g.left (SchemeOverField.rationalPoint b)
    (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalB
  /-- The additive structure map is killed by the evaluation difference. -/
  additive_zero : additiveStructureMap g.left ≫
    additiveEvaluationDifference evalA evalB = 0
  /-- The additive evaluation sequence is short exact. -/
  additive_exact : (ShortComplex.mk (additiveStructureMap g.left)
    (additiveEvaluationDifference evalA evalB) additive_zero).ShortExact

/-- Construct gluing-point data from its defining geometric conditions. -/
def GlueingPoints.ofConditions
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X : SchemeOverField k) (hY : Algebraic Y) (hX : Algebraic X)
    (g : Y ⟶ X)
    (a b : SchemeOverField.point k ⟶ Y)
    (x : SchemeOverField.point k ⟶ X)
    (U : X.left.Opens)
    (evalA evalB :
      (TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Y.left.sheaf ⟶
        pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)
    (distinct : a ≠ b)
    (first_maps_to : a ≫ g = x)
    (second_maps_to : b ≫ g = x)
    (finite : IsFinite g.left)
    (complement :
      (U : Set X.left) =
        {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ)
    (restriction_isIso : IsIso (g.left ∣_ U))
    (evaluationA : IsEvaluationAt g.left (SchemeOverField.rationalPoint a)
      (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalA)
    (evaluationB : IsEvaluationAt g.left (SchemeOverField.rationalPoint b)
      (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalB)
    (additive_zero : additiveStructureMap g.left ≫
      additiveEvaluationDifference evalA evalB = 0)
    (additive_exact : (ShortComplex.mk (additiveStructureMap g.left)
      (additiveEvaluationDifference evalA evalB) additive_zero).ShortExact) :
    GlueingPoints Y X hY hX g a b x U evalA evalB :=
  { distinct := distinct
    first_maps_to := first_maps_to
    second_maps_to := second_maps_to
    finite := finite
    complement := complement
    restriction_isIso := restriction_isIso
    evaluationA := evaluationA
    evaluationB := evaluationB
    additive_zero := additive_zero
    additive_exact := additive_exact }

/-- The point-identification clauses of gluing-point data. -/
theorem GlueingPoints.point_spec
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y X : SchemeOverField k} {hY : Algebraic Y} {hX : Algebraic X}
    {g : Y ⟶ X} {a b : SchemeOverField.point k ⟶ Y}
    {x : SchemeOverField.point k ⟶ X} {U : X.left.Opens}
    {evalA evalB :
      (TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Y.left.sheaf ⟶
        pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k}
    (h : GlueingPoints Y X hY hX g a b x U evalA evalB) :
    a ≠ b ∧ a ≫ g = x ∧ b ≫ g = x := sorry

/-- The exceptional-open and punctured-isomorphism clauses of gluing-point data. -/
theorem GlueingPoints.open_spec
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y X : SchemeOverField k} {hY : Algebraic Y} {hX : Algebraic X}
    {g : Y ⟶ X} {a b : SchemeOverField.point k ⟶ Y}
    {x : SchemeOverField.point k ⟶ X} {U : X.left.Opens}
    {evalA evalB :
      (TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Y.left.sheaf ⟶
        pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k}
    (h : GlueingPoints Y X hY hX g a b x U evalA evalB) :
    (U : Set X.left) =
        {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ ∧
      IsIso (g.left ∣_ U) := sorry

/-- The evaluation and additive-exactness clauses of gluing-point data. -/
theorem GlueingPoints.evaluation_spec
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y X : SchemeOverField k} {hY : Algebraic Y} {hX : Algebraic X}
    {g : Y ⟶ X} {a b : SchemeOverField.point k ⟶ Y}
    {x : SchemeOverField.point k ⟶ X} {U : X.left.Opens}
    {evalA evalB :
      (TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Y.left.sheaf ⟶
        pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k}
    (h : GlueingPoints Y X hY hX g a b x U evalA evalB) :
    IsEvaluationAt g.left (SchemeOverField.rationalPoint a)
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalA ∧
      IsEvaluationAt g.left (SchemeOverField.rationalPoint b)
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalB ∧
      additiveStructureMap g.left ≫ additiveEvaluationDifference evalA evalB = 0 ∧
      (ShortComplex.mk (additiveStructureMap g.left)
        (additiveEvaluationDifference evalA evalB) h.additive_zero).ShortExact := sorry

/-- An elementary finite modification is either a gluing of two points or a tangent-vector
squishing, with algebraicity of the source and target supplied explicitly. -/
inductive ElementaryModification
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X : SchemeOverField k) (hY : Algebraic Y) (hX : Algebraic X)
    (g : Y ⟶ X) : Prop where
  /-- The gluing-of-two-points branch. -/
  | glueing
      (a b : SchemeOverField.point k ⟶ Y)
      (x : SchemeOverField.point k ⟶ X)
      (U : X.left.Opens)
      (evalA evalB :
        (TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Y.left.sheaf ⟶
          pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)
      (data : GlueingPoints Y X hY hX g a b x U evalA evalB) :
      ElementaryModification Y X hY hX g
  /-- The squishing-of-a-tangent-vector branch. -/
  | squishing
      (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ Y.left)
      (x : SchemeOverField.point k ⟶ X)
      (U : X.left.Opens)
      (tangentEvaluation :
        additiveSheaf
          ((TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Y.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
      (maps : @SquishingTangentMaps k _ _ X Y hX hY g vartheta x)
      (data : @SquishesTangentVector k _ _ X Y hX hY g vartheta x U
        tangentEvaluation maps) :
      ElementaryModification Y X hY hX g

/-- Every elementary modification is a finite morphism. -/
theorem ElementaryModification.isFinite
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y X : SchemeOverField k} {hY : Algebraic Y} {hX : Algebraic X}
    {g : Y ⟶ X} (h : ElementaryModification Y X hY hX g) :
    IsFinite g.left := sorry

/-- The two source-semantic branches of an elementary modification. -/
theorem elementaryModification_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y X : SchemeOverField k} {hY : Algebraic Y} {hX : Algebraic X}
    {g : Y ⟶ X} :
    ElementaryModification Y X hY hX g ↔
      (∃ (a b : SchemeOverField.point k ⟶ Y)
          (x : SchemeOverField.point k ⟶ X) (U : X.left.Opens)
          (evalA evalB :
            (TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Y.left.sheaf ⟶
              pointRingSheaf X.left
                (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k),
        GlueingPoints Y X hY hX g a b x U evalA evalB) ∨
      (∃ (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ Y.left)
          (x : SchemeOverField.point k ⟶ X) (U : X.left.Opens)
          (tangentEvaluation :
            additiveSheaf
              ((TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Y.left.sheaf) ⟶
            additiveSheaf
              (pointRingSheaf X.left
                (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
          (maps : @SquishingTangentMaps k _ _ X Y hX hY g vartheta x),
        @SquishesTangentVector k _ _ X Y hX hY g vartheta x U tangentEvaluation maps) := sorry

end AlgebraicGeometry

end
