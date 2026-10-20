/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.TransformationFunctor.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Lift

/-!
# Functoriality of universal pseudopullback maps

For fixed source and bilimit target pseudopullback cones, the universal map induced by a
cospan transformation is functorial in modifications. The construction composes the
readable change-of-cospan functor with the neutral universal-lift functor.

This module owns the functor and its comparison with the shape-independent
`PseudoCone.mapDiagram.functor`. Componentwise computations for the induced `2`-cells and
coherence under identity and composition are kept in separate modules.
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
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- Universal maps from a fixed readable source cone to a fixed bilimit target cone are
functorial in cospan transformations and their modifications.

This is the composite of the readable change-of-cospan functor and the single neutral
quasi-inverse functor selected by the target bilimit. -/
noncomputable def mapCospan.functor
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit] :
    CospanTransform f g f' g' ⥤ (S.pt ⟶ T.pt) :=
  changeCospan.transformation.functor S f' g' ⋙
    PseudoCone.lift.functor T.toPseudoCone S.pt

/-- A modification between parallel cospan transformations induces a `2`-morphism
between their universal pseudopullback maps. -/
noncomputable def mapCospan.map₂
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    mapCospan S T ψ ⟶ mapCospan S T φ :=
  (PseudoCone.lift.functor T.toPseudoCone S.pt).map
    (changeCospan.modification Γ S)

/-- The object action of `mapCospan.functor` is the named universal cospan map. -/
@[simp]
theorem mapCospan.functor.obj
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    (ψ : CospanTransform f g f' g') :
    (mapCospan.functor S T).obj ψ = mapCospan S T ψ := sorry

/-- The morphism action of `mapCospan.functor` is the named induced `2`-morphism. -/
@[simp]
theorem mapCospan.functor.map
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    (mapCospan.functor S T).map Γ = mapCospan.map₂ S T Γ := sorry

/-- The induced `2`-morphism is obtained by applying the neutral lift functor to the
readable changed-cospan modification. -/
@[simp]
theorem mapCospan.map₂.eq_lift_map
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    mapCospan.map₂ S T Γ =
      (PseudoCone.lift.functor T.toPseudoCone S.pt).map
        (changeCospan.modification Γ S) := sorry

/-- A readable universal cospan map is canonically isomorphic to the neutral universal
map induced by the corresponding diagram transformation.

The comparison is obtained by applying the existing lift functor to the unique
readable/neutral presentation isomorphism. -/
noncomputable def mapCospan.mapDiagramIso
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    (ψ : CospanTransform f g f' g') :
    mapCospan S T ψ ≅
      PseudoCone.mapDiagram S.toPseudoCone T.toPseudoCone ψ :=
  (PseudoCone.lift.functor T.toPseudoCone S.pt).mapIso
    (changeCospan.presentation.modification.iso S ψ)

/-- The complete functor of readable universal cospan maps is naturally isomorphic to
the neutral universal-map functor. -/
noncomputable def mapCospan.functorIso
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit] :
    mapCospan.functor S T ≅
      PseudoCone.mapDiagram.functor S.toPseudoCone T.toPseudoCone :=
  Functor.isoWhiskerRight
    (changeCospan.transformation.functor.iso S f' g')
    (PseudoCone.lift.functor T.toPseudoCone S.pt)

/-- The forward component of the readable/neutral universal-map functor isomorphism is
the lifted presentation comparison. -/
@[simp]
theorem mapCospan.functorIso.hom_app
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    (ψ : CospanTransform f g f' g') :
    (mapCospan.functorIso S T).hom.app ψ =
      (mapCospan.mapDiagramIso S T ψ).hom := sorry

/-- The inverse component of the readable/neutral universal-map functor isomorphism is
the inverse lifted presentation comparison. -/
@[simp]
theorem mapCospan.functorIso.inv_app
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    (ψ : CospanTransform f g f' g') :
    (mapCospan.functorIso S T).inv.app ψ =
      (mapCospan.mapDiagramIso S T ψ).inv := sorry

/-- The lifted presentation comparisons intertwine readable and neutral induced
`2`-morphisms.

This is the downstream transfer rule for moving a calculation about `mapCospan.map₂` to the
shape-independent `PseudoCone.mapDiagram.map₂` API. -/
theorem mapCospan.mapDiagramIso.hom_naturality
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    mapCospan.map₂ S T Γ ≫ (mapCospan.mapDiagramIso S T φ).hom =
      (mapCospan.mapDiagramIso S T ψ).hom ≫
        PseudoCone.mapDiagram.map₂ S.toPseudoCone T.toPseudoCone Γ := sorry

/-- The inverse lifted presentation comparisons intertwine neutral and readable induced
`2`-morphisms.

This is the reverse downstream transfer rule for returning a calculation about
`PseudoCone.mapDiagram.map₂` to the readable `mapCospan.map₂` API. -/
theorem mapCospan.mapDiagramIso.inv_naturality
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    PseudoCone.mapDiagram.map₂ S.toPseudoCone T.toPseudoCone Γ ≫
        (mapCospan.mapDiagramIso S T φ).inv =
      (mapCospan.mapDiagramIso S T ψ).inv ≫
        mapCospan.map₂ S T Γ := sorry

/- Data and axiom audit (mathlib 4.32):

`mapCospan.functor` is the composite of two existing functors, and `mapCospan.map₂` is the
corresponding explicit map through the same neutral lift functor.
`mapCospan.mapDiagramIso` and `mapCospan.functorIso` apply that functor to the previously
explicit presentation comparison. No second lift, inverse, modification, or comparison
component is chosen in this module. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
