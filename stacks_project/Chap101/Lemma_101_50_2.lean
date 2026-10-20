/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Integral
import StacksCheckRecall

/-!
# Structure of integral algebraic stacks

The points space of an integral algebraic stack is sober (hence has a unique
generic point), and the stack contains an open substack which is a gerbe over
an integral scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 101.50.2 (1): The point space of an integral algebraic stack is sober. -/
@[stacks 0GWC] #check (AlgebraicGeometry.AlgebraicStack.IsIntegral.sober :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsIntegral X],
    T0Space (Points X) ∧ QuasiSober (Points X))

/- Lemma 101.50.2 (1): IsIntegral inherits IsIrreducible, whose existing API
gives irreducibility in every canonical topology on the point space. -/
@[stacks 0GWC] #check (AlgebraicGeometry.AlgebraicStack.IsIrreducible.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsIrreducible X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ),
    @IrreducibleSpace (Points X) τ)

/- Lemma 101.50.2 (1): The point space has a unique generic point. -/
@[stacks 0GWC] #check (AlgebraicGeometry.AlgebraicStack.IsIntegral.existsUnique_genericPoint :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsIntegral X],
    ∃! x : Points X, IsGenericPoint x Set.univ)

/- Lemma 101.50.2 (2): An integral algebraic stack contains an open substack
that is a gerbe over an integral scheme. -/
@[stacks 0GWC] #check
  (AlgebraicGeometry.AlgebraicStack.IsIntegral.exists_openSubstack_gerbeOver_integralScheme :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsIntegral X],
      ∃ (U : GroupoidsOver S) (ι : U ⟶ X) (V : Over S)
        (π : U ⟶ GroupoidsOver.slice V),
        AlgebraicStack U ∧ AlgebraicGeometry.Groupoids.Hom.OpenImmersion ι ∧
          AlgebraicGeometry.IsIntegral V.left ∧
          CategoryTheory.FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism
            (Scheme.fppfTopology.over S) π)
