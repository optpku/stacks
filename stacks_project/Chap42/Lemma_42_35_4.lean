/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_35_4_Additive
public import stacks_project.Chap42.Lemma_42_35_4_OpenRestriction

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u v w

namespace AlgebraicGeometry.BivariantClass.OpenRestriction

/-- Lemma 42.35.4: Restriction to compatible disjoint clopen decompositions identifies
degree-`p` bivariant classes of `f : X ⟶ Y` with the product of the componentwise
bivariant-class groups. -/
@[stacks 0FDZ]
theorem components_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h_component : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Function.Bijective (components delta f p U V a h_component) := sorry

end AlgebraicGeometry.BivariantClass.OpenRestriction
