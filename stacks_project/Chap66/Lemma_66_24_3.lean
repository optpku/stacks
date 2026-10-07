module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.NoetherianSpace
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-!
# Points of Noetherian algebraic spaces

The space of points of a Noetherian algebraic space is a sober Noetherian topological space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsNoetherian

/-- Lemma 66.24.3 (1): if an algebraic space `X` over a scheme `S` is Noetherian, then
`Points X` is sober. -/
@[stacks 04ZG]
theorem sober {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian X] :
    T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

/-- Lemma 66.24.3 (2): if an algebraic space `X` over a scheme `S` is Noetherian, then
`Points X` is a Noetherian topological space. -/
@[stacks 04ZG]
instance noetherianSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X] : TopologicalSpace.NoetherianSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsNoetherian
