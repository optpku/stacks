/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale

/-!
# Locally Noetherian rig-étale morphisms of formal algebraic spaces

The full subcategory of morphisms of functors of points whose source and target
are locally Noetherian formal algebraic spaces and whose structure morphism is
rig-étale.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism `g : W ⟶ Y` of functors of points is a rig-étale morphism of
locally Noetherian formal algebraic spaces when both objects are locally
Noetherian formal algebraic spaces and `g` is `RigEtale`. -/
def IsLocallyNoetherianRigEtale {S : Scheme.{u}} {W Y : (Over S)ᵒᵖ ⥤ Type u}
    (g : W ⟶ Y) : Prop :=
  ∃ (_ : IsFormalAlgebraicSpace W) (_ : IsFormalAlgebraicSpace Y)
    (_ : IsLocallyNoetherian W) (_ : IsLocallyNoetherian Y),
    RigEtale g

/-- `IsLocallyNoetherianRigEtale g` is exactly `IsFormalAlgebraicSpace` and
`IsLocallyNoetherian` of both objects together with `RigEtale g`. -/
theorem isLocallyNoetherianRigEtale_iff {S : Scheme.{u}}
    {W Y : (Over S)ᵒᵖ ⥤ Type u} (g : W ⟶ Y) :
    IsLocallyNoetherianRigEtale g ↔
      ∃ (_ : IsFormalAlgebraicSpace W) (_ : IsFormalAlgebraicSpace Y)
        (_ : IsLocallyNoetherian W) (_ : IsLocallyNoetherian Y),
        RigEtale g :=
  Iff.rfl

/-- A `RigEtale` morphism of locally Noetherian formal algebraic spaces is
`IsLocallyNoetherianRigEtale`. -/
theorem IsLocallyNoetherianRigEtale.of {S : Scheme.{u}}
    {W Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace W] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian W] [IsLocallyNoetherian Y]
    (g : W ⟶ Y) [RigEtale g] : IsLocallyNoetherianRigEtale g :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The object property on `Over Y` selecting morphisms whose source is a
locally Noetherian formal algebraic space and whose structure morphism is
rig-étale. -/
def isLocallyNoetherianRigEtaleOver {S : Scheme.{u}} (Y : (Over S)ᵒᵖ ⥤ Type u) :
    ObjectProperty (Over Y) :=
  fun W ↦ IsLocallyNoetherianRigEtale W.hom

/-- Membership in `isLocallyNoetherianRigEtaleOver Y` is
`IsLocallyNoetherianRigEtale` of the structure morphism. -/
theorem isLocallyNoetherianRigEtaleOver_iff {S : Scheme.{u}}
    (Y : (Over S)ᵒᵖ ⥤ Type u) (W : Over Y) :
    isLocallyNoetherianRigEtaleOver Y W ↔ IsLocallyNoetherianRigEtale W.hom :=
  Iff.rfl

/-- The full subcategory of morphisms `g : W ⟶ Y` of functors of points with `W`
a locally Noetherian formal algebraic space and `g` rig-étale. -/
abbrev LocallyNoetherianRigEtaleOver {S : Scheme.{u}} (Y : (Over S)ᵒᵖ ⥤ Type u) :=
  (isLocallyNoetherianRigEtaleOver Y).FullSubcategory

namespace LocallyNoetherianRigEtaleOver

/-- The inclusion of `LocallyNoetherianRigEtaleOver Y` into the ambient slice
category `Over Y`. -/
abbrev inclusion {S : Scheme.{u}} (Y : (Over S)ᵒᵖ ⥤ Type u) :
    LocallyNoetherianRigEtaleOver Y ⥤ Over Y :=
  (isLocallyNoetherianRigEtaleOver Y).ι

/-- A rig-étale morphism of locally Noetherian formal algebraic spaces, as an
object of `LocallyNoetherianRigEtaleOver Y`. -/
def of {S : Scheme.{u}} {Y W : (Over S)ᵒᵖ ⥤ Type u} (g : W ⟶ Y)
    (hg : IsLocallyNoetherianRigEtale g) : LocallyNoetherianRigEtaleOver Y where
  obj := Over.mk g
  property := hg

end LocallyNoetherianRigEtaleOver

end AlgebraicGeometry.FormalAlgebraicSpace
