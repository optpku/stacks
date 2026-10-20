/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Comparing Distinguished Triangle Completions

This leaf provides the specialization of Mathlib's arrow-isomorphism
comparison theorem that is most often needed after completing one fixed
morphism to distinguished triangles.
-/

namespace CategoryTheory.Pretriangulated.Triangle

universe v u

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- Stacks 014B, Lemma 13.4.7: two distinguished completions of the same first morphism are
isomorphic by a triangle isomorphism whose first two components are identities. -/
@[stacks 014B, stacks 09QV]
theorem existsIsoOfSameMor₁ {X Y Z Z' : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}
    {g' : Y ⟶ Z'} {h' : Z' ⟶ X⟦(1 : ℤ)⟧}
    (hT : CategoryTheory.Pretriangulated.Triangle.mk f g h ∈ distTriang C)
    (hT' : CategoryTheory.Pretriangulated.Triangle.mk f g' h' ∈ distTriang C) :
    ∃ e : CategoryTheory.Pretriangulated.Triangle.mk f g h ≅
      CategoryTheory.Pretriangulated.Triangle.mk f g' h',
      e.hom.hom₁ = 𝟙 X ∧ e.hom.hom₂ = 𝟙 Y := sorry

end CategoryTheory.Pretriangulated.Triangle
