/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_10_6_Mono

/-!
# Characterizations of monomorphisms of algebraic spaces

Lemma 67.10.6 records that a morphism of algebraic spaces is a monomorphism iff
this is tested on scheme-valued and affine base change, an étale atlas of the
target, and a Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Monomorphisms

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.10.6: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Mono f`; every scheme-valued base change of
`f` is a monomorphism; every affine-scheme-valued base change of `f` is a
monomorphism; some surjective étale scheme atlas of `Y` has monomorphic
pullback of `f`; and some Zariski covering of `Y` has each inverse-image
projection `f⁻¹(Yᵢ) ⟶ Yᵢ` a monomorphism. -/
@[stacks 042Q]
theorem tfae :
    List.TFAE [Mono f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is a monomorphism iff every scheme-valued
base change is a monomorphism. -/
theorem iff_forallScheme : Mono f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is a monomorphism iff every
affine-scheme-valued base change is a monomorphism. -/
theorem iff_forallAffine : Mono f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is a monomorphism iff some surjective étale
scheme atlas of the target has monomorphic pullback. -/
theorem iff_existsEtaleOnTarget : Mono f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is a monomorphism iff some Zariski covering
of the target has monomorphic inverse images under `f`. -/
theorem iff_existsZariskiCover : Mono f ↔ existsZariskiCover f := sorry

end Monomorphisms

end AlgebraicGeometry.AlgebraicSpace
