/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Functoriality.Identity

/-!
# Identity comparison for universal pseudopullback maps

The universal map induced by the identity cospan transformation is canonically
isomorphic to the identity map of a bilimit pseudopullback apex.

Both the presentation of the identity map and the resulting apex-map isomorphism reuse
the shape-independent identity API for pseudocones. The only additional cells pass
between the readable changed-cospan presentation and neutral pseudocone postcomposition.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B}
variable {f : x ⟶ z} {g : y ⟶ z}

/-- The identity apex map presents the readable cone obtained by changing cospan along
the identity transformation.

The neutral identity presentation is followed by the inverse readable/neutral
presentation comparison. -/
noncomputable def mapCospan.id.comparisonIso
    (S : PseudoPullbackCone f g) :
    (S.toPseudoCone.comparison S.pt).obj (𝟙 S.pt) ≅
      (S.changeCospan (CospanTransform.id f g)).toPseudoCone.π :=
  PseudoCone.mapDiagram.id.comparisonIso S.toPseudoCone ≪≫
    (changeCospan.presentation.modification.iso S
      (CospanTransform.id f g)).symm

/-- The forward identity presentation is the neutral identity presentation followed by
the inverse readable/neutral comparison. -/
@[simp]
theorem mapCospan.id.comparisonIso.hom
    (S : PseudoPullbackCone f g) :
    (mapCospan.id.comparisonIso S).hom =
      (PseudoCone.mapDiagram.id.comparisonIso S.toPseudoCone).hom ≫
        (changeCospan.presentation.modification.iso S
          (CospanTransform.id f g)).inv := sorry

/-- The inverse identity presentation is the readable/neutral comparison followed by
the inverse neutral identity presentation. -/
@[simp]
theorem mapCospan.id.comparisonIso.inv
    (S : PseudoPullbackCone f g) :
    (mapCospan.id.comparisonIso S).inv =
      (changeCospan.presentation.modification.iso S
          (CospanTransform.id f g)).hom ≫
        (PseudoCone.mapDiagram.id.comparisonIso S.toPseudoCone).inv := sorry

/-- The universal map induced by the identity cospan transformation is canonically
isomorphic to the identity map of the bilimit pseudopullback apex.

This is the neutral identity coherence transported across the canonical
readable/neutral universal-map comparison. -/
noncomputable def mapCospan.id.iso
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    𝟙 S.pt ≅ mapCospan S S (CospanTransform.id f g) :=
  PseudoCone.mapDiagram.id.iso S.toPseudoCone ≪≫
    (mapCospan.mapDiagramIso S S
      (CospanTransform.id f g)).symm

/-- The forward cell of readable identity coherence is the neutral identity cell
followed by the inverse readable/neutral map comparison. -/
@[simp]
theorem mapCospan.id.iso.hom
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (mapCospan.id.iso S).hom =
      (PseudoCone.mapDiagram.id.iso S.toPseudoCone).hom ≫
        (mapCospan.mapDiagramIso S S
          (CospanTransform.id f g)).inv := sorry

/-- The inverse cell of readable identity coherence is the readable/neutral map
comparison followed by the inverse neutral identity cell. -/
@[simp]
theorem mapCospan.id.iso.inv
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (mapCospan.id.iso S).inv =
      (mapCospan.mapDiagramIso S S
          (CospanTransform.id f g)).hom ≫
        (PseudoCone.mapDiagram.id.iso S.toPseudoCone).inv := sorry

/-- Under the represented comparison, the forward readable identity coherence is the
explicit readable identity presentation followed by the inverse universal comparison. -/
@[simp]
theorem mapCospan.id.iso.map_hom
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (S.toPseudoCone.comparison S.pt).map (mapCospan.id.iso S).hom =
      (mapCospan.id.comparisonIso S ≪≫
        (mapCospan.comparisonIso S S
          (CospanTransform.id f g)).symm).hom := sorry

/-- Under the represented comparison, the inverse readable identity coherence is the
inverse of the explicit identity-presentation composite. -/
@[simp]
theorem mapCospan.id.iso.map_inv
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (S.toPseudoCone.comparison S.pt).map (mapCospan.id.iso S).inv =
      (mapCospan.id.comparisonIso S ≪≫
        (mapCospan.comparisonIso S S
          (CospanTransform.id f g)).symm).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`mapCospan.id.comparisonIso` appends only the existing readable presentation comparison
to `PseudoCone.mapDiagram.id.comparisonIso`. `mapCospan.id.iso` transports the existing
neutral identity coherence through `mapCospan.mapDiagramIso`. No new apex map,
modification, inverse, or universal preimage is chosen in this module. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
