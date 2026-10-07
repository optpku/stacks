module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap68.Lemma_68_17_9_Local

/-!
# Local character of relative property (β), decent, reasonable, and very reasonable morphisms

Lemma 68.17.9 records that these morphism classes of algebraic spaces may be
tested on affine-scheme-valued base change, on the resulting pullback spaces,
and on a Zariski covering of the target. For property (β), decent, and
reasonable morphisms, they may also be tested on a surjective étale scheme
atlas of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace PropertyBeta

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 68.17.9 (1): for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `PropertyBeta f`; every affine-scheme-valued
base change of `f` has property (β); every such pullback space has property (β);
some Zariski covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ`
with property (β); and some surjective étale scheme atlas of `Y` has pullback of
`f` with property (β). -/
@[stacks 03L3]
theorem tfae :
    List.TFAE [PropertyBeta f, forallAffine f, forallAffineObject f, existsZariskiCover f,
      existsEtaleOnTarget f] := sorry

/-- A morphism of algebraic spaces has property (β) iff every affine-scheme-valued
base change has property (β). -/
theorem iff_forallAffine : PropertyBeta f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces has property (β) iff every affine-scheme-valued
pullback of its source has property (β). -/
theorem iff_forallAffineObject : PropertyBeta f ↔ forallAffineObject f := sorry

/-- A morphism of algebraic spaces has property (β) iff some Zariski covering of
the target has inverse images under `f` with property (β). -/
theorem iff_existsZariskiCover : PropertyBeta f ↔ existsZariskiCover f := sorry

/-- A morphism of algebraic spaces has property (β) iff some surjective étale
scheme atlas of the target has pullback of `f` with property (β). -/
theorem iff_existsEtaleOnTarget : PropertyBeta f ↔ existsEtaleOnTarget f := sorry

end PropertyBeta

namespace Decent

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 68.17.9 (2): for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Decent f`; every affine-scheme-valued base
change of `f` is decent; every such pullback space is decent; some Zariski
covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ` decent; and
some surjective étale scheme atlas of `Y` has decent pullback of `f`. -/
@[stacks 03L3]
theorem tfae :
    List.TFAE [Decent f, forallAffine f, forallAffineObject f, existsZariskiCover f,
      existsEtaleOnTarget f] := sorry

/-- A morphism of algebraic spaces is decent iff every affine-scheme-valued base
change is decent. -/
theorem iff_forallAffine : Decent f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is decent iff every affine-scheme-valued
pullback of its source is decent. -/
theorem iff_forallAffineObject : Decent f ↔ forallAffineObject f := sorry

/-- A morphism of algebraic spaces is decent iff some Zariski covering of the
target has decent inverse images under `f`. -/
theorem iff_existsZariskiCover : Decent f ↔ existsZariskiCover f := sorry

/-- A morphism of algebraic spaces is decent iff some surjective étale scheme
atlas of the target has decent pullback of `f`. -/
theorem iff_existsEtaleOnTarget : Decent f ↔ existsEtaleOnTarget f := sorry

end Decent

namespace Reasonable

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 68.17.9 (3): for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Reasonable f`; every affine-scheme-valued
base change of `f` is reasonable; every such pullback space is reasonable; some
Zariski covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ`
reasonable; and some surjective étale scheme atlas of `Y` has reasonable
pullback of `f`. -/
@[stacks 03L3]
theorem tfae :
    List.TFAE [Reasonable f, forallAffine f, forallAffineObject f, existsZariskiCover f,
      existsEtaleOnTarget f] := sorry

/-- A morphism of algebraic spaces is reasonable iff every affine-scheme-valued
base change is reasonable. -/
theorem iff_forallAffine : Reasonable f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is reasonable iff every affine-scheme-valued
pullback of its source is reasonable. -/
theorem iff_forallAffineObject : Reasonable f ↔ forallAffineObject f := sorry

/-- A morphism of algebraic spaces is reasonable iff some Zariski covering of the
target has reasonable inverse images under `f`. -/
theorem iff_existsZariskiCover : Reasonable f ↔ existsZariskiCover f := sorry

/-- A morphism of algebraic spaces is reasonable iff some surjective étale scheme
atlas of the target has reasonable pullback of `f`. -/
theorem iff_existsEtaleOnTarget : Reasonable f ↔ existsEtaleOnTarget f := sorry

end Reasonable

namespace VeryReasonable

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 68.17.9 (4): for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `VeryReasonable f`; every affine-scheme-valued
base change of `f` is very reasonable; every such pullback space is very
reasonable; and some Zariski covering of `Y` has each inverse-image projection
`f⁻¹(Yᵢ) ⟶ Yᵢ` very reasonable. -/
@[stacks 03L3]
theorem tfae :
    List.TFAE [VeryReasonable f, forallAffine f, forallAffineObject f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is very reasonable iff every
affine-scheme-valued base change is very reasonable. -/
theorem iff_forallAffine : VeryReasonable f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is very reasonable iff every
affine-scheme-valued pullback of its source is very reasonable. -/
theorem iff_forallAffineObject : VeryReasonable f ↔ forallAffineObject f := sorry

/-- A morphism of algebraic spaces is very reasonable iff some Zariski covering
of the target has very reasonable inverse images under `f`. -/
theorem iff_existsZariskiCover : VeryReasonable f ↔ existsZariskiCover f := sorry

end VeryReasonable

end AlgebraicGeometry.AlgebraicSpace
