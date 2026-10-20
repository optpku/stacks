/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action

/-!
# Morphisms of action groupoids of algebraic spaces

An equivariant morphism induces a morphism of action groupoids with arrow map `1_G × f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The map on arrows induced by an equivariant morphism between group algebraic space
actions. -/
def ofActionArrow (G : GroupAlgebraicSpace B) {X Y : GroupAlgebraicSpace.Action G}
    (f : X ⟶ Y) : (ofAction G X).R ⟶ (ofAction G Y).R :=
  G.X ◁ f.hom

/-- The arrow map induced by an equivariant morphism commutes with the source maps. -/
theorem ofActionArrow_source (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofAction G X).s ≫ f.hom = ofActionArrow G f ≫ (ofAction G Y).s :=
  sorry

/-- The arrow map induced by an equivariant morphism commutes with the target maps. -/
theorem ofActionArrow_target (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofAction G X).t ≫ f.hom = ofActionArrow G f ≫ (ofAction G Y).t :=
  sorry

/-- The arrow map induced by an equivariant morphism preserves groupoid composition. -/
theorem ofActionArrow_composition (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofAction G X).c ≫ ofActionArrow G f =
      composableMap f.hom (ofActionArrow G f)
          (ofActionArrow_source G f) (ofActionArrow_target G f) ≫
        (ofAction G Y).c :=
  sorry

/-- The morphism of action groupoids induced by a `G`-equivariant morphism. -/
def ofActionHom (G : GroupAlgebraicSpace B) {X Y : GroupAlgebraicSpace.Action G}
    (f : X ⟶ Y) : Hom (ofAction G X) (ofAction G Y) where
  obj := f.hom
  arrow := ofActionArrow G f
  map_s := ofActionArrow_source G f
  map_t := ofActionArrow_target G f
  map_c := ofActionArrow_composition G f

/-- The object component of the induced action-groupoid morphism is the given equivariant
morphism on underlying objects. -/
theorem ofActionHom_obj (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofActionHom G f).obj = f.hom :=
  sorry

/-- The arrow component of the induced action-groupoid morphism is the product of the
identity on the group algebraic space with the underlying object morphism. -/
theorem ofActionHom_arrow (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofActionHom G f).arrow = G.X ◁ f.hom :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
