/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage

/-!
# Small CFG sections from a supplied pointwise right Kan extension

A caller which already supplies right Kan extensions of all Type-valued presheaves
also supplies the required size bound for genuine sheaf sections. The implication
uses the native equivalence between existence of a Type-valued limit and smallness
of its compatible sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open FiberedCategoryOver.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- The stronger presheaf extension premise supplies the exact sheaf-section size condition. -/
instance hasSmallCFGTypeSections_of_pointwiseRightKanExtension (h : X ⟶ Y)
    [∀ P : X.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    HasSmallCFGTypeSections (S := S) h where
  small F Z := (Types.hasLimit_iff_small_sections
    (StructuredArrow.proj Z (toCartesianBasedFunctor h).toFunctor.op ⋙ F.obj)).mp
      inferInstance

end AlgebraicGeometry.GroupoidsOver
