/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.BaseChange

/-!
# Algebraic spaces affine over a base algebraic space

The full subcategory of the slice consisting of affine structure morphisms admits
base change along any morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The object property on `Over X` consisting of affine structure morphisms. -/
abbrev affineMorphismOverProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (Over X) :=
  MorphismProperty.overObj (@Affine S)

/-- The full subcategory of algebraic spaces whose structure morphism to `X` is affine. -/
abbrev AffineMorphismOver {S : Scheme.{u}} (X : AlgebraicSpace S) : Type (u + 1) :=
  (affineMorphismOverProperty X).FullSubcategory

namespace AffineMorphismOver

/-- The inclusion of algebraic spaces with affine structure morphism into all algebraic
spaces over `X`. -/
abbrev inclusion {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AffineMorphismOver X ⥤ Over X :=
  (affineMorphismOverProperty X).ι

/-- The structure morphism of an object of `AffineMorphismOver X` is affine. -/
instance instAffine {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : AffineMorphismOver X) : Affine Y.obj.hom :=
  Y.property

/-- Base change preserves the property of having an affine structure morphism. -/
theorem baseChange_mem {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    (Y : AffineMorphismOver X) :
    affineMorphismOverProperty X' ((Over.pullback g).obj Y.obj) :=
  Affine.pullback_snd Y.property g

/-- The base-change functor between categories of algebraic spaces affine over a
given algebraic space. -/
abbrev baseChange {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X) :
    AffineMorphismOver X ⥤ AffineMorphismOver X' :=
  ObjectProperty.lift (affineMorphismOverProperty X')
    (inclusion X ⋙ Over.pullback g) (fun Y ↦ baseChange_mem g Y)

end AffineMorphismOver

end AlgebraicGeometry.AlgebraicSpace
