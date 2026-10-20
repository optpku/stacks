/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap77.Theorem_77_11_7_Space

/-!
# Universal flattening under finite presentation, purity, and properness

A finitely presented morphism of algebraic spaces admits a universal flattening of a
finitely presented module when that module is pure relative to the base, and of the
source space when the space itself is pure. If the morphism is also proper, the
flattening still exists. In the first three cases the flattening morphism is a
monomorphism of finite presentation.

The source identifies `F_flat` with `F_0`. Relative purity cannot be co-imported with
`Modules.Flattening.overSFunctor` (duplicate `schemeEtaleRingedHom`), so these clauses
use the Comparison-side `flatInDimensionsOverSFunctor` at `0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)

/-- Lemma 77.11.8 (1): if `f` is of finite presentation, `ℱ` is of finite presentation,
and `ℱ` is pure relative to `Y`, then a universal flattening of `ℱ` exists. -/
@[stacks 0CX2]
theorem hasUniversalFlattening_of_isPureOver [FinitePresentation f]
    [ℱ.IsFinitePresentation] (h_pure : ℱ.IsPureOver f) :
    IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ 0) :=
  sorry

/-- Lemma 77.11.8 (3): if `f` is proper and of finite presentation and `ℱ` is of finite
presentation, then a universal flattening of `ℱ` exists. -/
@[stacks 0CX2, instance]
instance instIsAlgebraicSpace_of_isProper [Proper f] [FinitePresentation f]
    [ℱ.IsFinitePresentation] :
    IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ 0) :=
  sorry

/-- If `f` and `ℱ` are of finite presentation and `ℱ` is pure relative to `Y`, then
the universal flattening morphism `F_0 ⟶ Y` is of finite presentation. -/
theorem finitePresentation_toY_of_isPureOver [FinitePresentation f]
    [ℱ.IsFinitePresentation] (h_pure : ℱ.IsPureOver f)
    [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ 0)] :
    FinitePresentation (flatInDimensionsOverSFunctor.toY f ℱ 0) :=
  sorry

/-- If `f` is proper and of finite presentation and `ℱ` is of finite presentation, then
the universal flattening morphism `F_0 ⟶ Y` is of finite presentation. -/
instance finitePresentation_toY_of_isProper [Proper f] [FinitePresentation f]
    [ℱ.IsFinitePresentation] [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ 0)] :
    FinitePresentation (flatInDimensionsOverSFunctor.toY f ℱ 0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Flattening

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 77.11.8 (2): if `f` is of finite presentation and `X` is pure relative to `Y`,
then a universal flattening of `X` exists. -/
@[stacks 0CX2]
theorem hasUniversalFlattening_of_isPureOver [FinitePresentation f]
    (h_pure : IsPureOver f) :
    IsAlgebraicSpace
      (Flattening.flatInDimensionsOverSFunctor f
        (SheafOfModules.unit (structureSheaf X)) 0) :=
  sorry

/-- If `f` is of finite presentation and `X` is pure relative to `Y`, then the universal
flattening morphism of `X` is of finite presentation. -/
theorem finitePresentation_toY_of_isPureOver [FinitePresentation f]
    (h_pure : IsPureOver f)
    [IsAlgebraicSpace
      (Flattening.flatInDimensionsOverSFunctor f
        (SheafOfModules.unit (structureSheaf X)) 0)] :
    FinitePresentation
      (Flattening.flatInDimensionsOverSFunctor.toY f
        (SheafOfModules.unit (structureSheaf X)) 0) :=
  sorry

/-- Lemma 77.11.8 (4): if `f` is proper and of finite presentation, then a universal
flattening of `X` exists. -/
@[stacks 0CX2, instance]
instance instIsAlgebraicSpace_of_isProper [Proper f] [FinitePresentation f] :
    IsAlgebraicSpace
      (Flattening.flatInDimensionsOverSFunctor f
        (SheafOfModules.unit (structureSheaf X)) 0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
