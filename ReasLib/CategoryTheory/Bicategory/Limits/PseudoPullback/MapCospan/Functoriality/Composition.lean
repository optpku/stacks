/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Functoriality.Composition

/-!
# Composition comparison for universal pseudopullback maps

Universal maps induced by successive cospan transformations compose canonically to the
universal map induced by their composite. This file transports the shape-independent
`PseudoCone.mapDiagram.comp.iso` across the readable/neutral presentation comparisons.

An intermediate isomorphism compares the composite of two readable universal maps with
the composite of the two neutral universal maps. It is shared by the complete cone
presentation and the final apex-map coherence. Detailed projection formulas can therefore
be added independently without duplicating this whiskering data.
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
variable {x y z x' y' z' x'' y'' z'' : B}
variable {f : x ⟶ z} {g : y ⟶ z}
variable {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {f'' : x'' ⟶ z''} {g'' : y'' ⟶ z''}

/-- The composite of two readable universal cospan maps is canonically isomorphic to
the composite of the corresponding neutral universal diagram maps.

The comparison changes the first factor and then the second factor, using ordinary
bicategorical whiskering of isomorphisms. -/
noncomputable def mapCospan.comp.mapDiagramIso
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    mapCospan S T ψ ≫ mapCospan T U φ ≅
      PseudoCone.mapDiagram S.toPseudoCone T.toPseudoCone ψ ≫
        PseudoCone.mapDiagram T.toPseudoCone U.toPseudoCone φ :=
  Bicategory.whiskerRightIso
      (mapCospan.mapDiagramIso S T ψ)
      (mapCospan T U φ) ≪≫
    Bicategory.whiskerLeftIso
      (PseudoCone.mapDiagram S.toPseudoCone T.toPseudoCone ψ)
      (mapCospan.mapDiagramIso T U φ)

/-- The composite of two readable universal cospan maps presents the readable cone
obtained from the composite cospan transformation.

The neutral composite presentation is conjugated only by the shared apex-map comparison
and the final readable/neutral cone comparison. -/
noncomputable def mapCospan.comp.comparisonIso
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (U.toPseudoCone.comparison S.pt).obj
        (mapCospan S T ψ ≫ mapCospan T U φ) ≅
      (S.changeCospan (CospanTransform.comp ψ φ)).toPseudoCone.π :=
  (U.toPseudoCone.comparison S.pt).mapIso
      (mapCospan.comp.mapDiagramIso S T U ψ φ) ≪≫
    PseudoCone.mapDiagram.comp.comparisonIso
      S.toPseudoCone T.toPseudoCone U.toPseudoCone ψ φ ≪≫
    (changeCospan.presentation.modification.iso S
      (CospanTransform.comp ψ φ)).symm

/-- Universal maps along successive cospan transformations compose canonically to the
universal map along their composite.

All nontrivial composition coherence is inherited from
`PseudoCone.mapDiagram.comp.iso`; the outer isomorphisms only change presentations. -/
noncomputable def mapCospan.comp.iso
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    mapCospan S T ψ ≫ mapCospan T U φ ≅
      mapCospan S U (CospanTransform.comp ψ φ) :=
  mapCospan.comp.mapDiagramIso S T U ψ φ ≪≫
    PseudoCone.mapDiagram.comp.iso
      S.toPseudoCone T.toPseudoCone U.toPseudoCone ψ φ ≪≫
    (mapCospan.mapDiagramIso S U
      (CospanTransform.comp ψ φ)).symm

/-- Under the represented comparison, the forward readable composition coherence is
the explicit composite presentation followed by the inverse universal comparison. -/
@[simp]
theorem mapCospan.comp.iso.map_hom
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (U.toPseudoCone.comparison S.pt).map
        (mapCospan.comp.iso S T U ψ φ).hom =
      (mapCospan.comp.comparisonIso S T U ψ φ ≪≫
        (mapCospan.comparisonIso S U
          (CospanTransform.comp ψ φ)).symm).hom := sorry

/-- Under the represented comparison, the inverse readable composition coherence is
the inverse of the explicit composite-presentation comparison. -/
@[simp]
theorem mapCospan.comp.iso.map_inv
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (U.toPseudoCone.comparison S.pt).map
        (mapCospan.comp.iso S T U ψ φ).inv =
      (mapCospan.comp.comparisonIso S T U ψ φ ≪≫
        (mapCospan.comparisonIso S U
          (CospanTransform.comp ψ φ)).symm).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`mapCospan.comp.mapDiagramIso` contains only the two canonical whiskered
readable/neutral map comparisons. `mapCospan.comp.comparisonIso` and
`mapCospan.comp.iso` reuse the neutral composition presentation and coherence,
respectively. No additional apex map, modification, inverse, or universal preimage is
chosen in this module. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
