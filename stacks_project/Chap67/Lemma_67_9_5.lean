module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_9_5_Local

/-!
# Characterizations of universally closed morphisms of algebraic spaces

Lemma 67.9.5 records that a morphism of algebraic spaces is universally closed
iff this is tested by closed projections after scheme-valued and affine base
change, by a surjective étale scheme atlas of the target, and by a Zariski
covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.9.5: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `UniversallyClosed f`; every scheme-valued
base change of `f` has closed projection on points; every affine-scheme-valued
base change of `f` has closed projection on points; some surjective étale
scheme atlas of `Y` has universally closed pullback of `f`; and some Zariski
covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ` universally
closed. -/
@[stacks 03IT]
theorem tfae :
    List.TFAE [UniversallyClosed f, Closed.forallScheme f, Closed.forallAffine f,
      existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is universally closed iff every
scheme-valued base change has closed projection on points. -/
theorem iff_forallScheme : UniversallyClosed f ↔ Closed.forallScheme f := sorry

/-- A morphism of algebraic spaces is universally closed iff every
affine-scheme-valued base change has closed projection on points. -/
theorem iff_forallAffine : UniversallyClosed f ↔ Closed.forallAffine f := sorry

/-- A morphism of algebraic spaces is universally closed iff some surjective
étale scheme atlas of the target has universally closed pullback. -/
theorem iff_existsEtaleOnTarget :
    UniversallyClosed f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is universally closed iff some Zariski
covering of the target has universally closed inverse images under `f`. -/
theorem iff_existsZariskiCover :
    UniversallyClosed f ↔ existsZariskiCover f := sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicSpace
