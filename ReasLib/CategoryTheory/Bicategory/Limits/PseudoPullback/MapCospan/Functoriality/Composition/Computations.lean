/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality.Composition

/-!
# Computations for composition coherence of universal pseudopullback maps

This file exposes the forward and inverse cells of the three composition isomorphisms
used by the readable `mapCospan` API. The formulas stop at existing named whiskering,
neutral composition, and presentation-comparison isomorphisms.

Consequently downstream simplification can inspect the readable layer without duplicating
the associator pasting already owned by `PseudoCone.mapDiagram.comp.comparisonIso`.
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

/-- The forward composite-map comparison first changes the first universal map and then
changes the second universal map. -/
@[simp]
theorem mapCospan.comp.mapDiagramIso.hom
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.mapDiagramIso S T U ψ φ).hom =
      (Bicategory.whiskerRightIso
        (mapCospan.mapDiagramIso S T ψ)
        (mapCospan T U φ)).hom ≫
      (Bicategory.whiskerLeftIso
        (PseudoCone.mapDiagram S.toPseudoCone T.toPseudoCone ψ)
        (mapCospan.mapDiagramIso T U φ)).hom := sorry

/-- The inverse composite-map comparison changes the second neutral map back first and
then changes the first one. -/
@[simp]
theorem mapCospan.comp.mapDiagramIso.inv
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.mapDiagramIso S T U ψ φ).inv =
      (Bicategory.whiskerLeftIso
        (PseudoCone.mapDiagram S.toPseudoCone T.toPseudoCone ψ)
        (mapCospan.mapDiagramIso T U φ)).inv ≫
      (Bicategory.whiskerRightIso
        (mapCospan.mapDiagramIso S T ψ)
        (mapCospan T U φ)).inv := sorry

/-- The forward readable composite presentation is the mapped composite-map comparison,
the neutral composite presentation, and the inverse final presentation comparison. -/
@[simp]
theorem mapCospan.comp.comparisonIso.hom
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.comparisonIso S T U ψ φ).hom =
      (U.toPseudoCone.comparison S.pt).map
          (mapCospan.comp.mapDiagramIso S T U ψ φ).hom ≫
        (PseudoCone.mapDiagram.comp.comparisonIso
          S.toPseudoCone T.toPseudoCone U.toPseudoCone ψ φ).hom ≫
        (changeCospan.presentation.modification.iso S
          (CospanTransform.comp ψ φ)).inv := sorry

/-- The inverse readable composite presentation reverses the final presentation
comparison, neutral composite presentation, and mapped composite-map comparison. -/
@[simp]
theorem mapCospan.comp.comparisonIso.inv
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.comparisonIso S T U ψ φ).inv =
      (changeCospan.presentation.modification.iso S
          (CospanTransform.comp ψ φ)).hom ≫
        (PseudoCone.mapDiagram.comp.comparisonIso
          S.toPseudoCone T.toPseudoCone U.toPseudoCone ψ φ).inv ≫
        (U.toPseudoCone.comparison S.pt).map
          (mapCospan.comp.mapDiagramIso S T U ψ φ).inv := sorry

/-- The forward readable composition coherence is the composite-map comparison,
neutral composition coherence, and inverse final map comparison. -/
@[simp]
theorem mapCospan.comp.iso.hom
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.iso S T U ψ φ).hom =
      (mapCospan.comp.mapDiagramIso S T U ψ φ).hom ≫
        (PseudoCone.mapDiagram.comp.iso
          S.toPseudoCone T.toPseudoCone U.toPseudoCone ψ φ).hom ≫
        (mapCospan.mapDiagramIso S U
          (CospanTransform.comp ψ φ)).inv := sorry

/-- The inverse readable composition coherence reverses the final map comparison,
neutral composition coherence, and composite-map comparison. -/
@[simp]
theorem mapCospan.comp.iso.inv
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.iso S T U ψ φ).inv =
      (mapCospan.mapDiagramIso S U
          (CospanTransform.comp ψ φ)).hom ≫
        (PseudoCone.mapDiagram.comp.iso
          S.toPseudoCone T.toPseudoCone U.toPseudoCone ψ φ).inv ≫
        (mapCospan.comp.mapDiagramIso S T U ψ φ).inv := sorry

end CategoryTheory.Bicategory.PseudoPullbackCone
