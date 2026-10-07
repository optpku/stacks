module

public import ReasLib.Topology.Noetherian.Basic
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Points of locally Noetherian algebraic spaces

The points space of a locally Noetherian algebraic space is locally Noetherian, and it is
Noetherian when the algebraic space is also quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian

/-- The points space of a locally Noetherian algebraic space is a locally Noetherian topological
space. -/
theorem locallyNoetherianSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
    (A : Points.OpenQuotientAtlas X τ) :
    @TopologicalSpace.LocallyNoetherianSpace (Points X) τ :=
  sorry

/-- The points space of a quasi-compact locally Noetherian algebraic space is a Noetherian
topological space. -/
theorem noetherianSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
    (A : Points.OpenQuotientAtlas X τ) :
    @TopologicalSpace.NoetherianSpace (Points X) τ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian
