/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Affine morphisms over a base scheme

This file defines the full subcategory of the slice over a scheme whose
structure morphisms are affine, together with its canonical base-change
functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The object property on `Over S` consisting of affine structure morphisms. -/
abbrev affineMorphismOverProperty (S : Scheme.{u}) : ObjectProperty (Over S) :=
  MorphismProperty.overObj @IsAffineHom

/-- The full subcategory of schemes whose structure morphism to `S` is affine. -/
abbrev AffineMorphismOver (S : Scheme.{u}) : Type (u + 1) :=
  (affineMorphismOverProperty S).FullSubcategory

namespace AffineMorphismOver

/-- The inclusion of schemes with affine structure morphism into all schemes over `S`. -/
abbrev inclusion (S : Scheme.{u}) : AffineMorphismOver S ⥤ Over S :=
  (affineMorphismOverProperty S).ι

/-- The structure morphism of an object of `AffineMorphismOver S` is affine. -/
instance instIsAffineHom {S : Scheme.{u}} (X : AffineMorphismOver S) :
    IsAffineHom X.obj.hom :=
  X.property

/-- Base change preserves the property of having an affine structure morphism. -/
theorem baseChange_mem {S S' : Scheme.{u}} (g : S' ⟶ S)
    (X : AffineMorphismOver S) :
    affineMorphismOverProperty S' ((Over.pullback g).obj X.obj) :=
  MorphismProperty.baseChange_obj (P := @IsAffineHom) g X.obj X.property

/-- The base-change functor between categories of affine morphisms over schemes. -/
abbrev baseChange {S S' : Scheme.{u}} (g : S' ⟶ S) :
    AffineMorphismOver S ⥤ AffineMorphismOver S' :=
  ObjectProperty.lift (affineMorphismOverProperty S')
    (inclusion S ⋙ Over.pullback g) (fun X ↦ baseChange_mem g X)

end AffineMorphismOver

end AlgebraicGeometry
