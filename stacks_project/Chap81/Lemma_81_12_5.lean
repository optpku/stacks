module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.AffineDiagonal
import StacksCheckRecall

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

/- Lemma 81.12.5: the canonical Beauville–Laszlo functor induces bijections on
morphisms between glueable algebraic spaces when the target has affine relative
diagonal. In particular, its restriction to glueable spaces with affine relative
diagonal is fully faithful. -/
@[stacks 0F9T] #check
  (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.functor_map_bijective :
    ∀ {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
      (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
      {Y Z : Over (space R)} (hY : glueableProperty R' f Y) (hZ : glueableProperty R' f Z)
      [Affine (pullback.diagonal Z.hom)],
      Function.Bijective (fun α : Y ⟶ Z ↦ (functor R' f).map α))

#check
  (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.glueableAffineDiagonalFunctor_full :
    ∀ {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
      (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f],
      (glueableAffineDiagonalFunctor R' f).Full)

#check
  (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.glueableAffineDiagonalFunctor_faithful :
    ∀ {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
      (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f],
      (glueableAffineDiagonalFunctor R' f).Faithful)
