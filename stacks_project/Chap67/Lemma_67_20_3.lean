module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_20_3_Affine

/-!
# Characterizations of affine morphisms of algebraic spaces

Lemma 67.20.3 records that a morphism of algebraic spaces is affine iff it is
representable and affine, iff étale pullbacks from affine schemes are affine,
iff some surjective étale scheme atlas has affine projection, and iff some
Zariski covering of the target has affine inverse images.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Affine

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.20.3: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `f` is representable and affine; `Affine f`;
for every affine scheme `V` and étale morphism `V ⟶ Y` the scheme `X ×_Y V` is
affine; some scheme `V` with a surjective étale morphism `V ⟶ Y` has
`V ×_Y X ⟶ V` affine; and some Zariski covering `Y = ⋃ Yᵢ` has each
inverse-image morphism `f⁻¹(Yᵢ) ⟶ Yᵢ` affine. -/
@[stacks 03WG]
theorem tfae :
    List.TFAE [representableAffine f, Affine f, forallAffineEtale f,
      existsSurjectiveEtaleTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is affine iff it is representable and affine
in the Section 67.3 sense. -/
theorem iff_representableAffine : Affine f ↔ representableAffine f := sorry

/-- A morphism of algebraic spaces is affine iff every étale morphism from an
affine scheme to the target has affine fibre product. -/
theorem iff_forallAffineEtale : Affine f ↔ forallAffineEtale f := sorry

/-- A morphism of algebraic spaces is affine iff some surjective étale scheme
atlas of the target has affine pullback projection. -/
theorem iff_existsSurjectiveEtaleTarget :
    Affine f ↔ existsSurjectiveEtaleTarget f := sorry

/-- A morphism of algebraic spaces is affine iff some Zariski covering of the
target has affine inverse images under `f`. -/
theorem iff_existsZariskiCover : Affine f ↔ existsZariskiCover f := sorry

end Affine

end AlgebraicGeometry.AlgebraicSpace
