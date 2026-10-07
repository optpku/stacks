module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap87.Lemma_87_30_5_Local

/-!
# Characterizations of separation axioms for morphisms of formal algebraic spaces

Lemma 87.30.5 records that a morphism of formal algebraic spaces is separated
or quasi-separated iff this is tested by the corresponding projections after
scheme-valued and affine base change, by Definition 87.16.3 on affine-scheme-
valued fibre products, and by a Definition 87.11.1 étale atlas of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Separated

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

/-- Lemma 87.30.5 (1): for a morphism `f : X ⟶ Y` of formal algebraic spaces
over a scheme `S`, the following are equivalent: `Separated f`; every
scheme-valued base change of `f` is separated (`forallScheme f`); every
affine-scheme-valued base change of `f` is separated (`forallAffine f`); every
affine-scheme-valued fibre product `Z ×_Y X` is a separated formal algebraic
space in the sense of Definition 87.16.3 (`forallAffineSpace f`); and some
covering `{Y_j ⟶ Y}` as in Definition 87.11.1 has each base change
`Y_j ×_Y X ⟶ Y_j` separated (`existsCoverOnTarget f`). -/
@[stacks 0ARS]
theorem tfae :
    List.TFAE [Separated f, forallScheme f, forallAffine f, forallAffineSpace f,
      existsCoverOnTarget f] := sorry

/-- A morphism of formal algebraic spaces is separated iff every scheme-valued
base change has separated projection. -/
theorem iff_forallScheme : Separated f ↔ forallScheme f := sorry

/-- A morphism of formal algebraic spaces is separated iff every
affine-scheme-valued base change has separated projection. -/
theorem iff_forallAffine : Separated f ↔ forallAffine f := sorry

/-- A morphism of formal algebraic spaces is separated iff every
affine-scheme-valued fibre product is a separated formal algebraic space. -/
theorem iff_forallAffineSpace : Separated f ↔ forallAffineSpace f := sorry

/-- A morphism of formal algebraic spaces is separated iff some Definition
87.11.1 covering of the target has separated pullbacks of `f`. -/
theorem iff_existsCoverOnTarget : Separated f ↔ existsCoverOnTarget f := sorry

end Separated

namespace QuasiSeparated

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

/-- Lemma 87.30.5 (2): for a morphism `f : X ⟶ Y` of formal algebraic spaces
over a scheme `S`, the following are equivalent: `QuasiSeparated f`; every
scheme-valued base change of `f` is quasi-separated (`forallScheme f`); every
affine-scheme-valued base change of `f` is quasi-separated (`forallAffine f`);
every affine-scheme-valued fibre product `Z ×_Y X` is a quasi-separated formal
algebraic space in the sense of Definition 87.16.3 (`forallAffineSpace f`); and
some covering `{Y_j ⟶ Y}` as in Definition 87.11.1 has each base change
`Y_j ×_Y X ⟶ Y_j` quasi-separated (`existsCoverOnTarget f`). -/
@[stacks 0ARS]
theorem tfae :
    List.TFAE [QuasiSeparated f, forallScheme f, forallAffine f,
      forallAffineSpace f, existsCoverOnTarget f] := sorry

/-- A morphism of formal algebraic spaces is quasi-separated iff every
scheme-valued base change has quasi-separated projection. -/
theorem iff_forallScheme : QuasiSeparated f ↔ forallScheme f := sorry

/-- A morphism of formal algebraic spaces is quasi-separated iff every
affine-scheme-valued base change has quasi-separated projection. -/
theorem iff_forallAffine : QuasiSeparated f ↔ forallAffine f := sorry

/-- A morphism of formal algebraic spaces is quasi-separated iff every
affine-scheme-valued fibre product is a quasi-separated formal algebraic
space. -/
theorem iff_forallAffineSpace :
    QuasiSeparated f ↔ forallAffineSpace f := sorry

/-- A morphism of formal algebraic spaces is quasi-separated iff some
Definition 87.11.1 covering of the target has quasi-separated pullbacks of
`f`. -/
theorem iff_existsCoverOnTarget :
    QuasiSeparated f ↔ existsCoverOnTarget f := sorry

end QuasiSeparated

end AlgebraicGeometry.FormalAlgebraicSpace
