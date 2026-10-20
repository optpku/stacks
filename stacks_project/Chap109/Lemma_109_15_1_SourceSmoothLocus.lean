/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import stacks_project.Chap99.Lemma_99_15_2
public import stacks_project.Chap108.Lemma_108_4_5_OpenImmersion
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic

/-!
# Smooth source locus of the stack of curves

The object property of families of curves whose classifying morphism factors
through an open substack of `𝒞urves` on which the structure morphism
`𝒞urves ⟶ Spec(Z)` is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of families of curves whose classifying morphism
factors through an open substack of `𝒞urves` on which the structure morphism
`toIdentitySlice (toGroupoids S)` is smooth. This is membership in the
smooth source locus of `𝒞urves ⟶ Spec(Z)`, not smoothness of the family. -/
def sourceSmoothLocus (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    ∃ (U : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
      (ι : U ⟶ toGroupoids S),
      CohStack.Hom.OpenImmersion ι ∧
        CohStack.Hom.Smooth (ι ≫ CohStack.toIdentitySlice (toGroupoids S)) ∧
          ∃ (u : U.total), Nonempty (P ≅ (Groupoids.toFunctor ι).obj u)

/-- Membership in `sourceSmoothLocus` means there is an open immersion into
`toGroupoids S` along which the structure morphism is smooth, and the family
is in the essential image of that open. -/
theorem sourceSmoothLocus_iff {S : Scheme.{u}} (P : Obj S) :
    sourceSmoothLocus S P ↔
      ∃ (U : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
        (ι : U ⟶ toGroupoids S),
        CohStack.Hom.OpenImmersion ι ∧
          CohStack.Hom.Smooth
              (ι ≫ CohStack.toIdentitySlice (toGroupoids S)) ∧
            ∃ (u : U.total),
              Nonempty (P ≅ (Groupoids.toFunctor ι).obj u) :=
  sorry

/-- The smooth source locus of `𝒞urves` is closed under isomorphisms of
families. -/
instance instIsClosedUnderIsomorphisms_sourceSmoothLocus (S : Scheme.{u}) :
    (sourceSmoothLocus S).IsClosedUnderIsomorphisms :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
