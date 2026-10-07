module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap87.Lemma_87_31_2_Local

/-!
# Characterizations of proper morphisms of formal algebraic spaces

Lemma 87.31.2 records that a morphism of formal algebraic spaces is proper iff
this is tested by proper projections after scheme-valued and affine base
change, by algebraic-space properness of affine-scheme-valued fibre products,
and by a Definition 87.11.1 étale atlas of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Proper

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

/-- Lemma 87.31.2: for a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S`, the following are equivalent: `Proper f`; every scheme-valued base
change of `f` is proper (`forallScheme f`); every affine-scheme-valued base
change of `f` is proper (`forallAffine f`); every affine-scheme-valued fibre
product `Z ×_Y X` is an algebraic space proper over `Z`
(`forallAffineAlgebraicSpace f`); and some covering `{Y_j ⟶ Y}` as in
Definition 87.11.1 has each base change `Y_j ×_Y X ⟶ Y_j` proper
(`existsCoverOnTarget f`). -/
@[stacks 0ART]
theorem tfae :
    List.TFAE [Proper f, forallScheme f, forallAffine f,
      forallAffineAlgebraicSpace f, existsCoverOnTarget f] := sorry

/-- A morphism of formal algebraic spaces is proper iff every scheme-valued
base change has proper projection. -/
theorem iff_forallScheme : Proper f ↔ forallScheme f := sorry

/-- A morphism of formal algebraic spaces is proper iff every
affine-scheme-valued base change has proper projection. -/
theorem iff_forallAffine : Proper f ↔ forallAffine f := sorry

/-- A morphism of formal algebraic spaces is proper iff every
affine-scheme-valued fibre product is an algebraic space proper over the
affine scheme. -/
theorem iff_forallAffineAlgebraicSpace :
    Proper f ↔ forallAffineAlgebraicSpace f := sorry

/-- A morphism of formal algebraic spaces is proper iff some Definition
87.11.1 covering of the target has proper pullbacks of `f`. -/
theorem iff_existsCoverOnTarget : Proper f ↔ existsCoverOnTarget f := sorry

end Proper

end AlgebraicGeometry.FormalAlgebraicSpace
