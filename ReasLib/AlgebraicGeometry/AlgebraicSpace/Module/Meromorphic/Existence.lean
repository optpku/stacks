/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-!
# Existence of regular meromorphic sections

Under the standard codimension-zero, finite-component, and monomorphic-point
conditions, every tensor-invertible module on an algebraic space admits a
regular meromorphic section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.isInvertibleObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If weakly associated points are codimension zero, compact opens have finitely many
irreducible components, and codimension-zero points admit monomorphic field-valued points,
then every tensor-invertible module has a regular meromorphic section. -/
@[stacks 0EPQ]
theorem exists_isRegularMeromorphicSection {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (L : X.Modules) [isInvertibleObject L] :
    ∃ s : meromorphicSections X L, IsRegularMeromorphicSection X L s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
