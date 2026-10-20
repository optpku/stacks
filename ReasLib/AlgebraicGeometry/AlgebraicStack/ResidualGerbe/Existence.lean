/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia

/-!
# Existence of residual gerbes under quasi-compact inertia

An algebraic stack whose canonical inertia projection is quasi-compact has a
residual gerbe at every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack with quasi-compact canonical inertia projection has a
residual gerbe at every point. -/
@[stacks 06RD, instance]
instance instHasResidualGerbe_of_quasiCompactInertia {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] (x : Points X) :
    HasResidualGerbe X x :=
  sorry

namespace IsResidualGerbe

/-- If the inertia morphism of an algebraic stack `X` is quasi-compact, then
there is a residual gerbe of `X` at every point `x ∈ |X|`. -/
theorem exists_at_of_quasiCompactInertia {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] (x : Points X) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      IsResidualGerbe ι x :=
  ⟨residualGerbe X x, inferInstance, residualGerbeι X x, inferInstance⟩

end IsResidualGerbe

end AlgebraicGeometry.AlgebraicStack
