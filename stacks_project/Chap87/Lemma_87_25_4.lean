module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap87.Lemma_87_25_4_Local

/-!
# Characterizations of surjective morphisms of formal algebraic spaces

Lemma 87.25.4 records that a morphism of formal algebraic spaces is surjective
iff this is tested by surjective projections after scheme-valued and affine
base change, by a Definition 87.11.1 étale atlas of the target, and by some
surjective morphism of formal algebraic spaces to the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Surjective

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y)

/-- Lemma 87.25.4: for a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S`, the following are equivalent: `Surjective f`; every scheme-valued
base change of `f` is surjective (`forallScheme f`); every affine-scheme-valued
base change of `f` is surjective (`forallAffine f`); some covering `{Y_j ⟶ Y}`
as in Definition 87.11.1 has each base change `X ×_Y Y_j ⟶ Y_j` surjective
(`existsCoverOnTarget f`); and some surjective morphism `Z ⟶ Y` of formal
algebraic spaces has `X ×_Y Z ⟶ Z` surjective (`existsSurjectiveOnTarget f`). -/
@[stacks 0GHS]
theorem tfae :
    List.TFAE [Surjective f, forallScheme f, forallAffine f,
      existsCoverOnTarget f, existsSurjectiveOnTarget f] := sorry

/-- A morphism of formal algebraic spaces is surjective iff every scheme-valued
base change has surjective projection. -/
theorem iff_forallScheme : Surjective f ↔ forallScheme f := sorry

/-- A morphism of formal algebraic spaces is surjective iff every
affine-scheme-valued base change has surjective projection. -/
theorem iff_forallAffine : Surjective f ↔ forallAffine f := sorry

/-- A morphism of formal algebraic spaces is surjective iff some Definition
87.11.1 covering of the target has surjective pullbacks of `f`. -/
theorem iff_existsCoverOnTarget : Surjective f ↔ existsCoverOnTarget f := sorry

/-- A morphism of formal algebraic spaces is surjective iff some surjective
morphism of formal algebraic spaces to the target has surjective pullbacks of
`f`. -/
theorem iff_existsSurjectiveOnTarget :
    Surjective f ↔ existsSurjectiveOnTarget f := sorry

end Surjective

end AlgebraicGeometry.FormalAlgebraicSpace
