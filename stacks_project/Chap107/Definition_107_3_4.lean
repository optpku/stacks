/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.IrreducibleComponent.Multiplicity
import StacksCheckRecall

@[expose]
public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.AlgebraicStack

universe u

/- Definition 107.3.4: for a locally Noetherian algebraic stack `X` and an
irreducible component `T` of `|X|`, the multiplicity of `T` in `X` equals
the scheme-level multiplicity of any irreducible component `T'` of a scheme
`U` admitting a smooth morphism `U ⟶ X` with `f(T') ⊆ T`. -/
@[stacks 0DR8] #check (AlgebraicGeometry.AlgebraicStack.irreducibleComponentMultiplicity_eq :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {T : @irreducibleComponents (Points X) τ} (c : ComponentChart T),
    irreducibleComponentMultiplicity X τ T = c.multiplicity)

#check (AlgebraicGeometry.AlgebraicStack.irreducibleComponentMultiplicity :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian X]
    (τ : TopologicalSpace (Points X)),
    @irreducibleComponents (Points X) τ → ℕ)
