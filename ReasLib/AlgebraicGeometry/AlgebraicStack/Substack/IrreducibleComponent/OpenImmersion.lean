/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.IrreducibleComponent

/-!
# Open immersions into irreducible components

An open immersion into a reduced algebraic stack whose image lies in an
irreducible component factors through its reduced induced substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom (OpenImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An open immersion into a reduced algebraic stack with image contained in
an irreducible component factors as an open immersion through the reduced
induced substack of that component, with composite equal to the original map. -/
theorem openImmersion_factor_irreducibleComponentSubstack
    {S : Scheme.{u}} {Y X : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack X] [IsReduced X]
    (f : Y ⟶ X) (h_open : OpenImmersion f)
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {C : @irreducibleComponents (Points X) τ}
    (h_subset : Set.range (Points.map f) ⊆ (C : Set (Points X))) :
    ∃ j : Y ⟶ (irreducibleComponentSubstack hτ C).Y,
      OpenImmersion j ∧ j ≫ (irreducibleComponentSubstack hτ C).ι = f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
