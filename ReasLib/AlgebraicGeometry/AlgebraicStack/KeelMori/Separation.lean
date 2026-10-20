/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KeelMori
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Separation of moduli spaces of algebraic stacks with finite inertia

Quasi-separatedness and separatedness descend from an algebraic stack with
finite inertia to its uniform categorical moduli algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The uniform categorical moduli algebraic space of a quasi-separated
algebraic stack with finite inertia is absolutely quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_isUniformCategoricalModuliSpace
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f]
    [IsQuasiSeparated X] : AlgebraicSpace.IsAbsolutelyQuasiSeparated M :=
  sorry

/-- The uniform categorical moduli algebraic space of a separated algebraic
stack with finite inertia is absolutely separated. -/
theorem isAbsolutelySeparated_of_isUniformCategoricalModuliSpace
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f]
    [IsSeparated X] : AlgebraicSpace.IsAbsolutelySeparated M :=
  sorry

end AlgebraicGeometry.AlgebraicStack
