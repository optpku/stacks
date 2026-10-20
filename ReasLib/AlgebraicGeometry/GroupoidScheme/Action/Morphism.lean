/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action

/-!
# Morphisms of action groupoids

This module constructs the morphism of action groupoids induced by an equivariant morphism.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The map on arrows induced by an equivariant morphism between group-scheme actions. -/
def ofActionArrow {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) :
    (ofAction G Y).R ⟶ (ofAction G X).R :=
  G.X ◁ f.hom

/-- The arrow map induced by an equivariant morphism commutes with the source maps. -/
theorem ofActionArrow_source {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) :
    (ofAction G Y).s ≫ f.hom = ofActionArrow G f ≫ (ofAction G X).s := sorry

/-- The arrow map induced by an equivariant morphism commutes with the target maps. -/
theorem ofActionArrow_target {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) :
    (ofAction G Y).t ≫ f.hom = ofActionArrow G f ≫ (ofAction G X).t := sorry

/-- The arrow map induced by an equivariant morphism preserves groupoid composition. -/
theorem ofActionArrow_composition {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) :
    (ofAction G Y).c ≫ ofActionArrow G f =
      composableMap f.hom (ofActionArrow G f)
          (ofActionArrow_source G f) (ofActionArrow_target G f) ≫
        (ofAction G X).c := sorry

/-- The morphism of action groupoids induced by an equivariant morphism. -/
def ofActionHom {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) :
    Hom (ofAction G Y) (ofAction G X) where
  obj := f.hom
  arrow := ofActionArrow G f
  map_s := ofActionArrow_source G f
  map_t := ofActionArrow_target G f
  map_c := ofActionArrow_composition G f

/-- The object component of the induced action-groupoid morphism is the given equivariant
morphism on underlying objects. -/
theorem ofActionHom_obj {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) :
    (ofActionHom G f).obj = f.hom := sorry

/-- The arrow component of the induced action-groupoid morphism is the product of the
identity on the group scheme with the underlying object morphism. -/
theorem ofActionHom_arrow {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) :
    (ofActionHom G f).arrow = G.X ◁ f.hom := sorry

end AlgebraicGeometry.GroupoidScheme
