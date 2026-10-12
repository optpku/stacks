/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_6_5_Local

/-!
# Characterizations of universally open morphisms of algebraic spaces

Lemma 67.6.5 records that a morphism of algebraic spaces is universally open iff
this is tested on scheme-valued and affine base change, an étale atlas of the
target, and a Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyOpen

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.6.5: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `UniversallyOpen f`; every scheme-valued
base change of `f` has open projection `|Z ×_Y X| ⟶ |Z|`; every
affine-scheme-valued base change of `f` has open projection `|Z ×_Y X| ⟶ |Z|`;
some surjective étale scheme atlas of `Y` has universally open pullback of `f`;
and some Zariski covering of `Y` has each inverse-image projection
`f⁻¹(Yᵢ) ⟶ Yᵢ` universally open. -/
@[stacks 03Z5]
theorem tfae :
    List.TFAE [UniversallyOpen f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is universally open iff every scheme-valued
base change has open projection. -/
theorem iff_forallScheme : UniversallyOpen f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is universally open iff every
affine-scheme-valued base change has open projection. -/
theorem iff_forallAffine : UniversallyOpen f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is universally open iff some surjective étale
scheme atlas of the target has universally open pullback. -/
theorem iff_existsEtaleOnTarget : UniversallyOpen f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is universally open iff some Zariski covering
of the target has universally open inverse images under `f`. -/
theorem iff_existsZariskiCover : UniversallyOpen f ↔ existsZariskiCover f := sorry

end UniversallyOpen

end AlgebraicGeometry.AlgebraicSpace
