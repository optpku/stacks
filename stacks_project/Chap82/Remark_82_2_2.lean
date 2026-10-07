module

public import Mathlib.Topology.Sober
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Sobriety of points of a good algebraic space

In the setup of Situation 82.2.1, a good algebraic space over a quasi-separated
base has sober space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 82.2.2: in Situation 82.2.1, if `X / B` is good, then `Points X` is a sober
topological space. Good means the structure morphism `f : X ⟶ B` is `QuasiSeparated`
and `LocallyOfFiniteType`, over a quasi-separated base `B`; sober means `T0Space` and
`QuasiSober`. -/
@[stacks 0EDU]
theorem points_sober_of_quasiSeparated {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] :
    T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

/-- Every irreducible closed subset of `Points X` has a unique generic point, when `X / B`
is good over a quasi-separated base. -/
theorem existsUnique_isGenericPoint_of_quasiSeparated {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f]
    [LocallyOfFiniteType f] {T : Set (Points X)} (hT_irred : IsIrreducible T)
    (hT_closed : IsClosed T) :
    ∃! x : Points X, IsGenericPoint x T :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
