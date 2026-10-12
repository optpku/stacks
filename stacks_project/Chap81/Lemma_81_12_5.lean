/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap81.Lemma_81_12_5_AffineDiagonal

/-!
# Lemma 81.12.5

For a Beauville–Laszlo glueing pair, the canonical functor
`Over (space R) ⥤ category R' f` is fully faithful on the full subcategory of
glueable algebraic spaces over `X` with affine relative diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- Lemma 81.12.5: let `(algebraMap R R', f)` be a glueing pair. The functor
`functor R' f : Over (space R) ⥤ category R' f` is fully faithful on the full
subcategory of algebraic spaces `Y` over `X` which are glueable for the pair
and have affine relative diagonal `Y.left ⟶ pullback Y.hom Y.hom`. -/
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

/-- A morphism of glueable algebraic spaces over `X` that exists after applying
`functor R' f` lifts, when the target has affine relative diagonal. -/
theorem functor_map_surjective {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    {Y Z : Over (space R)} (hY : glueableProperty R' f Y) (hZ : glueableProperty R' f Z)
    [Affine (pullback.diagonal Z.hom)] :
    Function.Surjective (fun α : Y ⟶ Z ↦ (functor R' f).map α) :=
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
