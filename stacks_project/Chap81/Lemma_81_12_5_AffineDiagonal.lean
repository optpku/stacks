module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap81.Lemma_81_12_4_Glueable

/-!
# Glueable algebraic spaces with affine relative diagonal

Restricting `functor R' f` along the object property of glueable algebraic
spaces over `X = space R` with affine relative diagonal yields the canonical
functor on that full subcategory.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- The object property of algebraic spaces `Y` over `X = space R` that are
glueable for `(algebraMap R R', f)` and have affine relative diagonal
`pullback.diagonal Y.hom : Y.left ⟶ pullback Y.hom Y.hom`. -/
abbrev glueableAffineDiagonalProperty {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) : ObjectProperty (Over (space R)) :=
  fun Y ↦ glueableProperty R' f Y ∧ Affine (pullback.diagonal Y.hom)

/-- Membership in `glueableAffineDiagonalProperty R' f` is glueability for the
pair together with affineness of the relative diagonal of `Y.hom`. -/
theorem glueableAffineDiagonalProperty_iff {R : Type u} (R' : Type u) [CommRing R]
    [CommRing R'] [Algebra R R'] (f : R) (Y : Over (space R)) :
    glueableAffineDiagonalProperty R' f Y ↔
      glueableProperty R' f Y ∧ Affine (pullback.diagonal Y.hom) :=
  sorry

/-- The canonical functor `Over (space R) ⥤ category R' f` restricted to the full
subcategory of glueable algebraic spaces over `X` with affine relative
diagonal. -/
abbrev glueableAffineDiagonalFunctor {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) :
    (glueableAffineDiagonalProperty R' f).FullSubcategory ⥤ category R' f :=
  (glueableAffineDiagonalProperty R' f).ι ⋙ functor R' f

/-- `glueableAffineDiagonalFunctor R' f` is the composite of `ι` with
`functor R' f`. -/
theorem glueableAffineDiagonalFunctor_eq {R : Type u} (R' : Type u) [CommRing R]
    [CommRing R'] [Algebra R R'] (f : R) :
    glueableAffineDiagonalFunctor R' f =
      (glueableAffineDiagonalProperty R' f).ι ⋙ functor R' f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
