/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
public import stacks_project.Chap67.Lemma_67_21_3_QuasiAffine

/-!
# Characterizations of quasi-affine morphisms of algebraic spaces

Lemma 67.21.3 records that a morphism of algebraic spaces is quasi-affine iff
it is representable and quasi-affine, iff some surjective étale scheme atlas of
the target has quasi-affine pullback projection, and iff some Zariski covering
of the target has quasi-affine inverse images.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiAffine

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.21.3: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `f` is representable and quasi-affine;
`QuasiAffine f`; some scheme `V` with a surjective étale morphism `V ⟶ Y` has
`V ×_Y X ⟶ V` quasi-affine; and some Zariski covering `Y = ⋃ Yᵢ` has each
inverse-image morphism `f⁻¹(Yᵢ) ⟶ Yᵢ` quasi-affine. -/
@[stacks 03WM]
theorem tfae :
    List.TFAE [(over (@QuasiAffineHom : MorphismProperty Scheme.{u})).presheaf f,
      QuasiAffine f, existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is quasi-affine iff it is representable and
quasi-affine in the Section 67.3 sense. -/
theorem iff_over_presheaf :
    QuasiAffine f ↔
      (over (@QuasiAffineHom : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- A morphism of algebraic spaces is quasi-affine iff some surjective étale
scheme atlas of the target has quasi-affine pullback projection. -/
theorem iff_existsEtaleOnTarget : QuasiAffine f ↔ existsEtaleOnTarget f :=
  sorry

/-- A morphism of algebraic spaces is quasi-affine iff some Zariski covering of
the target has quasi-affine inverse images under `f`. -/
theorem iff_existsZariskiCover : QuasiAffine f ↔ existsZariskiCover f := sorry

/-- A quasi-affine morphism of algebraic spaces is relatively representable. -/
theorem relativelyRepresentable [QuasiAffine f] :
    yoneda.relativelyRepresentable f := sorry

end QuasiAffine

end AlgebraicGeometry.AlgebraicSpace
