/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Moduli
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia

/-!
# Moduli spaces of algebraic stacks with finite inertia

An algebraic stack with finite inertia admits a uniform categorical moduli
space whose morphism is separated, quasi-compact, and a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack with finite inertia admits a uniform categorical moduli
space whose morphism is separated, quasi-compact, and a universal homeomorphism. -/
theorem exists_isUniformCategoricalModuliSpace_of_isFinite_inertia
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] :
    ∃ (M : AlgebraicSpace S) (f : X ⟶ M.toGroupoids),
      IsUniformCategoricalModuliSpace f ∧ Separated f ∧ QuasiCompact f ∧
        UniversalHomeomorphism f :=
  sorry

/-- A uniform categorical moduli morphism of an algebraic stack with finite
inertia is separated. -/
instance instSeparated_of_isFinite_inertia {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f] :
    Separated f :=
  sorry

/-- A uniform categorical moduli morphism of an algebraic stack with finite
inertia is quasi-compact. -/
instance instQuasiCompact_of_isFinite_inertia {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f] :
    QuasiCompact f :=
  sorry

/-- A uniform categorical moduli morphism of an algebraic stack with finite
inertia is a universal homeomorphism. -/
instance instUniversalHomeomorphism_of_isFinite_inertia {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f] :
    UniversalHomeomorphism f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
