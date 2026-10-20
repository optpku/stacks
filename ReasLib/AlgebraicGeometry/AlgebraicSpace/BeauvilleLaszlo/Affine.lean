/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.GlueableFunctor

/-!
# Affine glueable algebraic spaces for a Beauville–Laszlo pair

Restricting `functor R' f` along the object property of affine glueable algebraic
spaces over `X = space R` yields a functor into the full subcategory of affine
objects of `category R' f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- The object property of algebraic spaces `Y` over `X = space R` that are affine
and glueable for `(algebraMap R R', f)`. -/
abbrev affineGlueableProperty {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) : ObjectProperty (Over (space R)) :=
  fun Y ↦ AlgebraicSpace.IsAffine Y.left ∧ glueableProperty R' f Y

/-- Membership in `affineGlueableProperty R' f` is affineness of `Y.left` together
with glueability for the pair. -/
theorem affineGlueableProperty_iff {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) (Y : Over (space R)) :
    affineGlueableProperty R' f Y ↔
      AlgebraicSpace.IsAffine Y.left ∧ glueableProperty R' f Y :=
  sorry

/-- The object property of objects of `category R' f` whose components `V`, `V'`,
and `Y'` are affine algebraic spaces. -/
abbrev affineTripleProperty {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) : ObjectProperty (category R' f) :=
  fun obj ↦
    AlgebraicSpace.IsAffine obj.fst.left ∧
      AlgebraicSpace.IsAffine (overlap obj).left ∧
      AlgebraicSpace.IsAffine obj.snd.left

/-- Membership in `affineTripleProperty R' f` is affineness of `obj.fst.left`,
`(overlap obj).left`, and `obj.snd.left`. -/
theorem affineTripleProperty_iff {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) (obj : category R' f) :
    affineTripleProperty R' f obj ↔
      AlgebraicSpace.IsAffine obj.fst.left ∧
        AlgebraicSpace.IsAffine (overlap obj).left ∧
        AlgebraicSpace.IsAffine obj.snd.left :=
  sorry

/-- The canonical glueing functor sends an affine algebraic space over `X` to an
object of `category R' f` with affine components. -/
theorem functor_obj_mem_affineTriple {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) {Y : Over (space R)} (hY : AlgebraicSpace.IsAffine Y.left) :
    affineTripleProperty R' f ((functor R' f).obj Y) :=
  sorry

/-- The restriction of `functor R' f` to affine glueable algebraic spaces over `X`,
landing in the full subcategory of affine objects of `category R' f`. -/
abbrev affineGlueableFunctor {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) :
    (affineGlueableProperty R' f).FullSubcategory ⥤
      (affineTripleProperty R' f).FullSubcategory :=
  (affineTripleProperty R' f).lift ((affineGlueableProperty R' f).ι ⋙ functor R' f)
    (fun Y ↦ functor_obj_mem_affineTriple R' f Y.property.1)

/-- `affineGlueableFunctor R' f` composed with `ι` recovers `ι ⋙ functor R' f`. -/
theorem affineGlueableFunctor_comp_ι {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) :
    affineGlueableFunctor R' f ⋙ (affineTripleProperty R' f).ι =
      (affineGlueableProperty R' f).ι ⋙ functor R' f :=
  sorry

/-- Let `(algebraMap R R', f)` be a glueing pair. The functor
`functor R' f` restricts to an equivalence between the category of affine
algebraic spaces `Y` over `X` which are glueable for the pair and the full
subcategory of objects `(V, V', Y')` of `category R' f` with `V`, `V'`, and
`Y'` affine. -/
@[stacks 0F9Q, instance]
instance affineGlueableFunctor_isEquivalence {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] :
    (affineGlueableFunctor R' f).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
