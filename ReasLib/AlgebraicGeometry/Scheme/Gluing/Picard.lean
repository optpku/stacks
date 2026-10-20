/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Connected.Clopen
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Points
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Two-point gluing gives a Picard-group exact sequence whose pullback is surjective. -/
theorem exists_picardGlueingExact
    {k : Type u} [Field k] [IsAlgClosed k]
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
      (additiveEvaluationDifference evalA evalB) h_add_zero).ShortExact) :
    ∃ δ : Additive kˣ →+ X.left.PicardGroup,
      ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
        Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
          Function.Surjective (Scheme.Hom.picardPullback f.left) := sorry

/-- If the glued points lie in different connected components, the first map in the
    Picard-group exact sequence can be chosen to be zero. -/
theorem exists_picardGlueingExactWithZero_of_differentComponents
    {k : Type u} [Field k] [IsAlgClosed k]
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
          ((SchemeOverField.rationalPoint b) (IsLocalRing.closedPoint k))) :
    ∃ δ : Additive kˣ →+ X.left.PicardGroup,
      ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
        Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
          Function.Surjective (Scheme.Hom.picardPullback f.left) ∧ δ = 0 := sorry

/-- If the source of a two-point gluing is proper and the points lie in the same
    connected component, the first map in the Picard-group exact sequence is injective. -/
theorem exists_picardGlueingExactWithInjective_of_sameComponent
    {k : Type u} [Field k] [IsAlgClosed k]
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
          ((SchemeOverField.rationalPoint b) (IsLocalRing.closedPoint k))) :
    ∃ δ : Additive kˣ →+ X.left.PicardGroup,
      ∃ h_zero : ∀ z, Scheme.Hom.picardPullback f.left (δ z) = 0,
        Function.Exact δ (Scheme.Hom.picardPullback f.left) ∧
          Function.Surjective (Scheme.Hom.picardPullback f.left) ∧
            Function.Injective δ := sorry

end AlgebraicGeometry
