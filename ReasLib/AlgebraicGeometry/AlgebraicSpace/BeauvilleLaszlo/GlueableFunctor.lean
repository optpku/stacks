/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.Glueable

/-!
# Glueable algebraic spaces and the Beauville–Laszlo functor

The canonical Beauville–Laszlo functor restricted to glueable algebraic spaces
is faithful.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- The object property of algebraic spaces over `Spec R` whose affine étale
tests have glueable global sections for `(algebraMap R R', f)`. -/
abbrev glueableProperty {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) : ObjectProperty (Over (space R)) :=
  fun Y ↦
    ∀ {T : Over (Spec (CommRingCat.of R))} [AlgebraicGeometry.IsAffine T.left]
      (φ : ofOver T ⟶ Y.left) [Etale φ],
      Scheme.Hom.glueableGlobalSections R' f T

/-- Membership in `glueableProperty R' f` is characterized by its affine étale
test condition. -/
theorem glueableProperty_iff {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) (Y : Over (space R)) :
    glueableProperty R' f Y ↔
      ∀ {T : Over (Spec (CommRingCat.of R))} [AlgebraicGeometry.IsAffine T.left]
        (φ : ofOver T ⟶ Y.left) [Etale φ],
        Scheme.Hom.glueableGlobalSections R' f T := by
  rfl

/-- The canonical Beauville–Laszlo functor restricted to the full subcategory
of glueable algebraic spaces over `Spec R`. -/
abbrev glueableFunctor {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) : (glueableProperty R' f).FullSubcategory ⥤ category R' f :=
  (glueableProperty R' f).ι ⋙ functor R' f

/-- The restricted functor is the composite of the full-subcategory inclusion
with the canonical Beauville–Laszlo functor. -/
theorem glueableFunctor_eq {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) :
    glueableFunctor R' f = (glueableProperty R' f).ι ⋙ functor R' f := by
  rfl

/-- The restricted Beauville–Laszlo functor is faithful for a glueing pair. -/
@[stacks 0F9S, instance]
instance glueableFunctor_faithful {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] :
    (glueableFunctor R' f).Faithful :=
  sorry

/-- Morphisms between glueable algebraic spaces are determined by their images
under the canonical Beauville–Laszlo functor. -/
theorem functor_map_injective {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    {Y Z : Over (space R)} (hY : glueableProperty R' f Y) (hZ : glueableProperty R' f Z) :
    Function.Injective (fun α : Y ⟶ Z ↦ (functor R' f).map α) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
