module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_40_2_Local

/-!
# Characterizations of proper morphisms of algebraic spaces

Lemma 67.40.2 records that a morphism of algebraic spaces is proper iff this is
tested by proper projections after scheme-valued and affine base change, by a
surjective étale scheme atlas of the target, and by a Zariski covering of the
target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.40.2: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Proper f`; every scheme-valued base change
of `f` has proper projection; every affine-scheme-valued base change of `f` has
proper projection; some surjective étale scheme atlas of `Y` has proper
pullback of `f`; and some Zariski covering of `Y` has each inverse-image
projection `f⁻¹(Yᵢ) ⟶ Yᵢ` proper. -/
@[stacks 083R]
theorem tfae :
    List.TFAE [Proper f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is proper iff every scheme-valued base
change has proper projection. -/
theorem iff_forallScheme : Proper f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is proper iff every affine-scheme-valued
base change has proper projection. -/
theorem iff_forallAffine : Proper f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is proper iff some surjective étale scheme
atlas of the target has proper pullback. -/
theorem iff_existsEtaleOnTarget : Proper f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is proper iff some Zariski covering of the
target has proper inverse images under `f`. -/
theorem iff_existsZariskiCover : Proper f ↔ existsZariskiCover f := sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
