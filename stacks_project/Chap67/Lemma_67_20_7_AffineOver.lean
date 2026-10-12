/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_20_5_Pullback

/-!
# Algebraic spaces affine over a base algebraic space

This file defines the full subcategory of the slice over an algebraic space whose
structure morphisms are affine, together with its canonical base-change functor.
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
    affineMorphismOverProperty X' ((Over.pullback g).obj Y.obj) := sorry

/-- The base-change functor between categories of algebraic spaces affine over a
given algebraic space. -/
abbrev baseChange {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X) :
    AffineMorphismOver X ⥤ AffineMorphismOver X' :=
  ObjectProperty.lift (affineMorphismOverProperty X')
    (inclusion X ⋙ Over.pullback g) (fun Y ↦ baseChange_mem g Y)

end AffineMorphismOver

end AlgebraicGeometry.AlgebraicSpace
