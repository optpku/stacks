/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Definition_101_50_1_Integral

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

namespace AlgebraicGeometry.AlgebraicStack.IsIntegral

/-- Lemma 101.50.2 (1): Let `X` be an integral algebraic stack. Then `|X|` is
sober, i.e. `@T0Space (Points X) τ` and `@QuasiSober (Points X) τ` for every
canonical `IsPointsTopology`. Irreducibility of `|X|` is inherited from
`IsIrreducible`. -/
@[stacks 0GWC]
theorem sober {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsIntegral X] (τ : TopologicalSpace (Points X))
    (hτ : IsPointsTopology X τ) :
    @T0Space (Points X) τ ∧ @QuasiSober (Points X) τ :=
  sorry

/-- The points space of an integral algebraic stack has a unique generic point. -/
theorem existsUnique_genericPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsIntegral X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) :
    ∃! x, @IsGenericPoint (Points X) τ x Set.univ :=
  sorry

/-- Lemma 101.50.2 (2): Let `X` be an integral algebraic stack. Then there exists
an open substack `U ⊂ X` which is a gerbe over an integral scheme. -/
@[stacks 0GWC]
theorem exists_openSubstack_gerbeOver_integralScheme
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsIntegral X] :
    ∃ (U : OpenSubstack X) (V : Over S) (π : U.Y ⟶ GroupoidsOver.slice V),
      AlgebraicGeometry.IsIntegral V.left ∧ Gerbe π :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsIntegral
