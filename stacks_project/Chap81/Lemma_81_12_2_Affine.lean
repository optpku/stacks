module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap81.«81_12_0_1_Glueing»
public import stacks_project.Chap81.Lemma_81_12_4_Glueable

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

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
