/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap87.Lemma_87_17_3_QuasiCompact
public import stacks_project.Chap87.Lemma_87_17_3_Predicates

/-!
# Characterizations of quasi-compact morphisms of formal algebraic spaces

Lemma 87.17.3 records that a morphism of formal algebraic spaces has
quasi-compact algebraic-space reduction if and only if this is tested by
quasi-compact fibre products after quasi-compact scheme-valued and affine base
change, and by a Definition 87.11.1 étale atlas of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y)

/-- Lemma 87.17.3: for a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S`, the following are equivalent: the induced map
`mapReduction f : reduction X ⟶ reduction Y` is a quasi-compact morphism of
algebraic spaces; every base change of `f` along a quasi-compact scheme
`T ⟶ Y` has quasi-compact fibre product (`forallQuasiCompactScheme f`); the
same with `T` affine (`forallAffine f`); and some covering `{Y_j ⟶ Y}` as in
Definition 87.11.1 has each fibre product of `f` along `Y_j` a quasi-compact
formal algebraic space (`existsCoverOnTarget f`). -/
@[stacks 0AJB]
theorem tfae :
    List.TFAE [AlgebraicSpace.QuasiCompact (mapReduction f),
      forallQuasiCompactScheme f, forallAffine f, existsCoverOnTarget f] :=
  sorry

/-- The induced map of reductions is a quasi-compact morphism of algebraic
spaces iff every quasi-compact scheme-valued base change of `f` is a
quasi-compact formal algebraic space. -/
theorem iff_forallQuasiCompactScheme :
    AlgebraicSpace.QuasiCompact (mapReduction f) ↔
      forallQuasiCompactScheme f :=
  sorry

/-- The induced map of reductions is a quasi-compact morphism of algebraic
spaces iff every affine-scheme-valued base change of `f` is a quasi-compact
formal algebraic space. -/
theorem iff_forallAffine :
    AlgebraicSpace.QuasiCompact (mapReduction f) ↔ forallAffine f :=
  sorry

/-- The induced map of reductions is a quasi-compact morphism of algebraic
spaces iff some Definition 87.11.1 covering of the target has quasi-compact
pullback vertices of `f`. -/
theorem iff_existsCoverOnTarget :
    AlgebraicSpace.QuasiCompact (mapReduction f) ↔ existsCoverOnTarget f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
