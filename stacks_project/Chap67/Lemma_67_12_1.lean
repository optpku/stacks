/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_12_1_Immersion

/-!
# Characterizations of immersions of algebraic spaces

Lemma 67.12.1 records that a morphism of algebraic spaces is a closed
immersion, an open immersion, or an immersion iff this is tested on
scheme-valued and affine base change, an étale atlas of the target, and a
Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsClosedImmersion

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.12.1 (1): for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `IsClosedImmersion f`; every
scheme-valued base change of `f` is a closed immersion; every
affine-scheme-valued base change of `f` is a closed immersion; some surjective
étale scheme atlas of `Y` has closed-immersion pullback of `f`; and some
Zariski covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ` a
closed immersion. -/
@[stacks 03M4]
theorem tfae :
    List.TFAE [IsClosedImmersion f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is a closed immersion iff every
scheme-valued base change is a closed immersion. -/
theorem iff_forallScheme : IsClosedImmersion f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is a closed immersion iff every
affine-scheme-valued base change is a closed immersion. -/
theorem iff_forallAffine : IsClosedImmersion f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is a closed immersion iff some surjective
étale scheme atlas of the target has closed-immersion pullback. -/
theorem iff_existsEtaleOnTarget : IsClosedImmersion f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is a closed immersion iff some Zariski
covering of the target has closed-immersion inverse images under `f`. -/
theorem iff_existsZariskiCover : IsClosedImmersion f ↔ existsZariskiCover f := sorry

end IsClosedImmersion

namespace IsOpenImmersion

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.12.1 (2): for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `IsOpenImmersion f`; every
scheme-valued base change of `f` is an open immersion; every
affine-scheme-valued base change of `f` is an open immersion; some surjective
étale scheme atlas of `Y` has open-immersion pullback of `f`; and some Zariski
covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ` an open
immersion. -/
@[stacks 03M4]
theorem tfae :
    List.TFAE [IsOpenImmersion f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is an open immersion iff every scheme-valued
base change is an open immersion. -/
theorem iff_forallScheme : IsOpenImmersion f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is an open immersion iff every
affine-scheme-valued base change is an open immersion. -/
theorem iff_forallAffine : IsOpenImmersion f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is an open immersion iff some surjective
étale scheme atlas of the target has open-immersion pullback. -/
theorem iff_existsEtaleOnTarget : IsOpenImmersion f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is an open immersion iff some Zariski
covering of the target has open-immersion inverse images under `f`. -/
theorem iff_existsZariskiCover : IsOpenImmersion f ↔ existsZariskiCover f := sorry

end IsOpenImmersion

namespace IsImmersion

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.12.1 (3): for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `IsImmersion f`; every scheme-valued
base change of `f` is an immersion; every affine-scheme-valued base change of
`f` is an immersion; some surjective étale scheme atlas of `Y` has immersion
pullback of `f`; and some Zariski covering of `Y` has each inverse-image
projection `f⁻¹(Yᵢ) ⟶ Yᵢ` an immersion. -/
@[stacks 03M4]
theorem tfae :
    List.TFAE [IsImmersion f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is an immersion iff every scheme-valued base
change is an immersion. -/
theorem iff_forallScheme : IsImmersion f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is an immersion iff every
affine-scheme-valued base change is an immersion. -/
theorem iff_forallAffine : IsImmersion f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is an immersion iff some surjective étale
scheme atlas of the target has immersion pullback. -/
theorem iff_existsEtaleOnTarget : IsImmersion f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is an immersion iff some Zariski covering of
the target has immersion inverse images under `f`. -/
theorem iff_existsZariskiCover : IsImmersion f ↔ existsZariskiCover f := sorry

end IsImmersion

end AlgebraicGeometry.AlgebraicSpace
