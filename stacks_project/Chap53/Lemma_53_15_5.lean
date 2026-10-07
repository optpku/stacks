module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Gluing.Picard

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 53.15.5 (1): glueing two points gives an exact sequence
`Additive kˣ ⟶ X.left.PicardGroup ⟶ X'.left.PicardGroup ⟶ 0`. -/
@[stacks 0C1M] #check
  (AlgebraicGeometry.exists_picardGlueingExact :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
      (f : X' ⟶ X) [IsFinite f.left]
      (a b : SchemeOverField.point k ⟶ X')
      (x : SchemeOverField.point k ⟶ X)
      (h_distinct : a ≠ b) (ha : a ≫ f = x) (hb : b ≫ f = x)
      (U : X.left.Opens)
      (hU : (U : Set X.left) =
        {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ)
      [IsIso (f.left ∣_ U)]
      (evalA evalB :
        (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf ⟶
          TopCat.Sheaf.Skyscraper.atPoint
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
            (CommRingCat.of k))
      (h_evalA : IsEvaluationAt f.left (SchemeOverField.rationalPoint a)
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalA)
      (h_evalB : IsEvaluationAt f.left (SchemeOverField.rationalPoint b)
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalB)
      (h_add_zero : additiveStructureMap f.left ≫
        additiveEvaluationDifference evalA evalB = 0)
      (h_add_exact : (ShortComplex.mk (additiveStructureMap f.left)
        (additiveEvaluationDifference evalA evalB) h_add_zero).ShortExact),
      ∃ δ : Additive kˣ →+ X.left.PicardGroup,
        ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
          Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
            Function.Surjective (Scheme.Hom.picardPullback f.left))

/- Lemma 53.15.5 (2): when the glued points lie in different connected components,
the exact Picard sequence can be chosen with zero first map. -/
@[stacks 0C1M] #check
  (AlgebraicGeometry.exists_picardGlueingExactWithZero_of_differentComponents :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
      (f : X' ⟶ X) [IsFinite f.left]
      (a b : SchemeOverField.point k ⟶ X')
      (x : SchemeOverField.point k ⟶ X)
      (h_distinct : a ≠ b) (ha : a ≫ f = x) (hb : b ≫ f = x)
      (U : X.left.Opens)
      (hU : (U : Set X.left) =
        {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ)
      [IsIso (f.left ∣_ U)]
      (evalA evalB :
        (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf ⟶
          TopCat.Sheaf.Skyscraper.atPoint
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
            (CommRingCat.of k))
      (h_evalA : IsEvaluationAt f.left (SchemeOverField.rationalPoint a)
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalA)
      (h_evalB : IsEvaluationAt f.left (SchemeOverField.rationalPoint b)
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalB)
      (h_add_zero : additiveStructureMap f.left ≫
        additiveEvaluationDifference evalA evalB = 0)
      (h_add_exact : (ShortComplex.mk (additiveStructureMap f.left)
        (additiveEvaluationDifference evalA evalB) h_add_zero).ShortExact)
      (h_components :
        ConnectedComponents.mk
            ((SchemeOverField.rationalPoint a) (IsLocalRing.closedPoint k)) ≠
          ConnectedComponents.mk
            ((SchemeOverField.rationalPoint b) (IsLocalRing.closedPoint k))),
      ∃ δ : Additive kˣ →+ X.left.PicardGroup,
        ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
          Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
            Function.Surjective (Scheme.Hom.picardPullback f.left) ∧ δ = 0)

/- Lemma 53.15.5 (3): when `X'` is proper and the glued points lie in the same
connected component, the exact Picard sequence can be chosen with injective first map. -/
@[stacks 0C1M] #check
  (AlgebraicGeometry.exists_picardGlueingExactWithInjective_of_sameComponent :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X X' : SchemeOverField k) [Algebraic X] [Algebraic X'] [IsProper X'.hom]
      (f : X' ⟶ X) [IsFinite f.left]
      (a b : SchemeOverField.point k ⟶ X')
      (x : SchemeOverField.point k ⟶ X)
      (h_distinct : a ≠ b) (ha : a ≫ f = x) (hb : b ≫ f = x)
      (U : X.left.Opens)
      (hU : (U : Set X.left) =
        {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ)
      [IsIso (f.left ∣_ U)]
      (evalA evalB :
        (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf ⟶
          TopCat.Sheaf.Skyscraper.atPoint
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
            (CommRingCat.of k))
      (h_evalA : IsEvaluationAt f.left (SchemeOverField.rationalPoint a)
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalA)
      (h_evalB : IsEvaluationAt f.left (SchemeOverField.rationalPoint b)
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalB)
      (h_add_zero : additiveStructureMap f.left ≫
        additiveEvaluationDifference evalA evalB = 0)
      (h_add_exact : (ShortComplex.mk (additiveStructureMap f.left)
        (additiveEvaluationDifference evalA evalB) h_add_zero).ShortExact)
      (h_components :
        ConnectedComponents.mk
            ((SchemeOverField.rationalPoint a) (IsLocalRing.closedPoint k)) =
          ConnectedComponents.mk
            ((SchemeOverField.rationalPoint b) (IsLocalRing.closedPoint k))),
      ∃ δ : Additive kˣ →+ X.left.PicardGroup,
        ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
          Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
            Function.Surjective (Scheme.Hom.picardPullback f.left) ∧
              Function.Injective δ)
