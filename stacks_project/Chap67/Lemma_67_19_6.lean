/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_19_6_Local

/-!
# Characterizations of universally injective morphisms of algebraic spaces

Lemma 67.19.6 records that a morphism of algebraic spaces is universally
injective iff this is tested by universally injective projections after
scheme-valued and affine base change, by a surjective scheme morphism to the
target, and by a Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyInjective

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.19.6: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `UniversallyInjective f`; every
scheme-valued base change of `f` is universally injective; every
affine-scheme-valued base change of `f` is universally injective; some
surjective scheme morphism to `Y` has universally injective pullback of `f`;
and some Zariski covering of `Y` has each inverse-image projection
`f⁻¹(Yᵢ) ⟶ Yᵢ` universally injective. -/
@[stacks 03MX]
theorem tfae :
    List.TFAE [UniversallyInjective f, forallScheme f, forallAffine f,
      existsSchemeSurjectiveOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is universally injective iff every
scheme-valued base change is universally injective. -/
theorem iff_forallScheme : UniversallyInjective f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is universally injective iff every
affine-scheme-valued base change is universally injective. -/
theorem iff_forallAffine : UniversallyInjective f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is universally injective iff some surjective
scheme morphism to the target has universally injective pullback. -/
theorem iff_existsSchemeSurjectiveOnTarget :
    UniversallyInjective f ↔ existsSchemeSurjectiveOnTarget f := sorry

/-- A morphism of algebraic spaces is universally injective iff some Zariski
covering of the target has universally injective inverse images under `f`. -/
theorem iff_existsZariskiCover :
    UniversallyInjective f ↔ existsZariskiCover f := sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicSpace
