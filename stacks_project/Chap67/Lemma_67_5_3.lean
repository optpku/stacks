module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_5_3_Surjective

/-!
# Characterizations of surjective morphisms of algebraic spaces

Lemma 67.5.3 records that surjectivity of a morphism of algebraic spaces is
equivalent to scheme-valued and affine base change, étale atlas, and Zariski
covering tests.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Surjective

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.5.3: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Surjective f`; every scheme-valued base
change of `f` is surjective; every affine-scheme-valued base change of `f` is
surjective; some surjective étale scheme atlas of `Y` has surjective pullback of
`f`; some surjective étale scheme atlas of `X` has surjective composite with
`f`; some commutative square of surjective étale scheme atlases over `f` has
surjective top arrow; and some Zariski covering of `Y` has each inverse image
under `f` surjective. -/
@[stacks 03MF]
theorem tfae :
    List.TFAE [Surjective f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsEtaleOnSource f, existsEtaleSquare f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is surjective iff every scheme-valued base
change is surjective. -/
theorem iff_forallScheme : Surjective f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is surjective iff every affine-scheme-valued
base change is surjective. -/
theorem iff_forallAffine : Surjective f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is surjective iff some surjective étale
scheme atlas of the target has surjective pullback. -/
theorem iff_existsEtaleOnTarget : Surjective f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is surjective iff some surjective étale
scheme atlas of the source has surjective composite with `f`. -/
theorem iff_existsEtaleOnSource : Surjective f ↔ existsEtaleOnSource f := sorry

/-- A morphism of algebraic spaces is surjective iff some commutative square of
surjective étale scheme atlases has surjective top arrow. -/
theorem iff_existsEtaleSquare : Surjective f ↔ existsEtaleSquare f := sorry

/-- A morphism of algebraic spaces is surjective iff some Zariski covering of
the target has surjective inverse images under `f`. -/
theorem iff_existsZariskiCover : Surjective f ↔ existsZariskiCover f := sorry

end Surjective

end AlgebraicGeometry.AlgebraicSpace
