/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Lift

/-!
# Identity comparison for universal maps induced by diagram transformations

The universal map induced by the identity transformation of a diagram is canonically
isomorphic to the identity map of a bilimit apex. This file isolates that comparison from
composition and higher coherence.

The presentation reuses the generic identity comparison for a bilimit lift and adds only
the right-unitor correction introduced by postcomposition with the identity strong
transformation.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {E : Pseudofunctor J B}

/-- The identity apex map presents the pseudocone obtained by postcomposing with the
identity diagram transformation.

This specializes the generic `lift.id.comparisonIso` and then applies the inverse right
unitor in the strong-transformation bicategory. -/
noncomputable def mapDiagram.id.comparisonIso (S : PseudoCone E) :
    (S.comparison S.pt).obj (𝟙 S.pt) ≅
      (postcomposeObj (𝟙 E) S).π :=
  PseudoCone.lift.id.comparisonIso S ≪≫ (ρ_ S.π).symm

/-- The forward cell of the identity-diagram presentation is the generic identity
presentation followed by the inverse right unitor. -/
@[simp]
theorem mapDiagram.id.comparisonIso.hom (S : PseudoCone E) :
    (mapDiagram.id.comparisonIso S).hom =
      (PseudoCone.lift.id.comparisonIso S).hom ≫
        (ρ_ S.π).inv := sorry

/-- The inverse cell of the identity-diagram presentation is the right unitor followed by
the inverse generic identity presentation. -/
@[simp]
theorem mapDiagram.id.comparisonIso.inv (S : PseudoCone E) :
    (mapDiagram.id.comparisonIso S).inv =
      (ρ_ S.π).hom ≫
        (PseudoCone.lift.id.comparisonIso S).inv := sorry

/-- The universal map induced by the identity diagram transformation is canonically
isomorphic to the identity map of the bilimit apex. -/
noncomputable abbrev mapDiagram.id.iso
    (S : PseudoCone E) [S.IsBilimit] :
    𝟙 S.pt ≅ mapDiagram S S (𝟙 E) :=
  PseudoCone.lift.uniqueIso (postcomposeObj (𝟙 E) S) S
    (𝟙 S.pt) (mapDiagram.id.comparisonIso S)

/-- Under the represented comparison, the forward identity coherence is the explicit
identity-diagram presentation followed by the inverse universal comparison. -/
@[simp]
theorem mapDiagram.id.iso.map_hom
    (S : PseudoCone E) [S.IsBilimit] :
    (S.comparison S.pt).map (mapDiagram.id.iso S).hom =
      (mapDiagram.id.comparisonIso S ≪≫
        (mapDiagram.comparisonIso S S (𝟙 E)).symm).hom := sorry

/-- Under the represented comparison, the inverse identity coherence is the inverse of
the explicit identity-diagram presentation composite. -/
@[simp]
theorem mapDiagram.id.iso.map_inv
    (S : PseudoCone E) [S.IsBilimit] :
    (S.comparison S.pt).map (mapDiagram.id.iso S).inv =
      (mapDiagram.id.comparisonIso S ≪≫
        (mapDiagram.comparisonIso S S (𝟙 E)).symm).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`mapDiagram.id.comparisonIso` reuses `PseudoCone.lift.id.comparisonIso` and only appends a
right unitor. `mapDiagram.id.iso` is obtained from the generic uniqueness API for bilimit
lifts. Thus this layer introduces no new choice beyond the already encapsulated universal
lift. -/

end Bicategory.PseudoCone

end CategoryTheory
