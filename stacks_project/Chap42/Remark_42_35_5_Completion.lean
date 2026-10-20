/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.OpenRestriction.Completion
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w

#check (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)), Type (max (u + 1) v))

#check (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.globalEquiv :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)),
    AlgebraicGeometry.BivariantClass.OpenRestriction.Completion delta f U V a h ≃+
      AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.Global delta f U V a h)

#check (AlgebraicGeometry.ChowCohomology.completedRing :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] {I : Type v} (U : I → X.left.Opens)
    (hU_cover : iSup U = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hId : ∀ i, U i ≤ (𝟙 X : X ⟶ X).left ⁻¹ᵁ U i), Type (max (u + 1) v))
