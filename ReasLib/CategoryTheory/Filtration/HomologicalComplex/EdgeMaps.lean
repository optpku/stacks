/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.TwoStep
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Homology

/-!
# Edge maps for filtered homological complexes

This module provides the canonical projection from a filtration stage to its associated graded
piece and predicates characterizing the two directions of a homological edge map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace CategoryTheory
namespace HomologicalComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

namespace Stage

/-- The canonical projection of a filtration stage onto its associated graded piece. -/
noncomputable def toGradedPiece
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    Stage.complex K p ⟶ gradedPiece K p :=
  Limits.cokernel.π (Stage.comparison K (lt_add_one p).le) ≫
    (TwoStep.GradedPiece.cokernelIso K p).inv

end Stage

namespace Homology

variable [CategoryWithHomology C]

/-- The homology morphism induced by the canonical stage-to-graded projection. -/
noncomputable def toGradedPiece
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) (i : ι) :
    (Stage.complex K p).homology i ⟶ (gradedPiece K p).homology i :=
  HomologicalComplex.homologyMap (Stage.toGradedPiece K p) i

/-- A morphism from the underlying homology to a graded-piece homology is an edge map when it
  agrees with the stage map after restriction to the filtration stage. -/
def IsEdgeToGradedPiece
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) (i : ι)
    (e : (underlying K).homology i ⟶ (gradedPiece K p).homology i) : Prop :=
  map K p i ≫ e = toGradedPiece K p i

/-- A morphism from a graded-piece homology to the underlying homology is an edge map when its
  composite with the canonical projection is the stage map. -/
def IsEdgeFromGradedPiece
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) (i : ι)
    (e : (gradedPiece K p).homology i ⟶ (underlying K).homology i) : Prop :=
  toGradedPiece K p i ≫ e = map K p i

namespace IsEdgeToGradedPiece

/-- The edge map to a graded piece is unique when the stage inclusion induces an epimorphism
on homology. -/
theorem unique
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) (i : ι)
    [Epi (map K p i)]
    {e₁ e₂ : (underlying K).homology i ⟶ (gradedPiece K p).homology i}
    (h₁ : IsEdgeToGradedPiece K p i e₁)
    (h₂ : IsEdgeToGradedPiece K p i e₂) :
    e₁ = e₂ := by
  apply (cancel_epi (map K p i)).1
  exact h₁.trans h₂.symm

end IsEdgeToGradedPiece

namespace IsEdgeFromGradedPiece

/-- The edge map from a graded piece is unique when the stage projection induces an
epimorphism on homology. -/
theorem unique
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) (i : ι)
    [Epi (toGradedPiece K p i)]
    {e₁ e₂ : (gradedPiece K p).homology i ⟶ (underlying K).homology i}
    (h₁ : IsEdgeFromGradedPiece K p i e₁)
    (h₂ : IsEdgeFromGradedPiece K p i e₂) :
    e₁ = e₂ := by
  apply (cancel_epi (toGradedPiece K p i)).1
  exact h₁.trans h₂.symm

end IsEdgeFromGradedPiece

end Homology
end HomologicalComplex.Filtered
end CategoryTheory
