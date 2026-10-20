module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.GlueableFunctor

/-!
# Glueable algebraic spaces with affine relative diagonal

The canonical Beauville–Laszlo functor is fully faithful on glueable algebraic
spaces with affine relative diagonal.
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
      glueableProperty R' f Y ∧ Affine (pullback.diagonal Y.hom) := by
  rfl

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
  rfl

/-- A morphism of glueable algebraic spaces over `X` that exists after applying
`functor R' f` lifts, when the target has affine relative diagonal. -/
theorem functor_map_surjective {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    {Y Z : Over (space R)} (hY : glueableProperty R' f Y) (hZ : glueableProperty R' f Z)
    [Affine (pullback.diagonal Z.hom)] :
    Function.Surjective (fun α : Y ⟶ Z ↦ (functor R' f).map α) :=
  sorry

/-- For a glueing pair, the canonical Beauville–Laszlo functor restricted to
glueable algebraic spaces with affine relative diagonal is full. -/
@[stacks 0F9T, instance]
instance glueableAffineDiagonalFunctor_full {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] :
    (glueableAffineDiagonalFunctor R' f).Full :=
  sorry

/-- The restriction of `functor R' f` to glueable algebraic spaces over `X` with
affine relative diagonal is faithful. -/
instance glueableAffineDiagonalFunctor_faithful {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] :
    (glueableAffineDiagonalFunctor R' f).Faithful :=
  sorry

/-- Morphisms of glueable algebraic spaces over `X` correspond bijectively, after
applying `functor R' f`, when the target has affine relative diagonal. -/
theorem functor_map_bijective {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    {Y Z : Over (space R)} (hY : glueableProperty R' f Y) (hZ : glueableProperty R' f Z)
    [Affine (pullback.diagonal Z.hom)] :
    Function.Bijective (fun α : Y ⟶ Z ↦ (functor R' f).map α) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
