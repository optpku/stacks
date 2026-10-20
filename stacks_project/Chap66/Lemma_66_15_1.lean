module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Sober
import StacksCheckRecall

/-!
# Sobriety of Zariski locally quasi-separated algebraic spaces

The space of points of a Zariski locally quasi-separated algebraic space is sober
in the sense of Topology, Definition 5.8.6, i.e. both Kolmogorov and quasi-sober.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.15.1: let `S` be a scheme. Let `X` be a Zariski locally quasi-separated
algebraic space over `S`. Then the topological space `Points X` is sober. -/
@[stacks 06NJ] #check (AlgebraicGeometry.AlgebraicSpace.points_sober :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsZariskiLocallyQuasiSeparated X],
    T0Space (AlgebraicGeometry.AlgebraicSpace.Points X) ∧
      QuasiSober (AlgebraicGeometry.AlgebraicSpace.Points X))

/- Lemma 66.15.1: the point space of a Zariski locally quasi-separated algebraic space is
Kolmogorov. -/
@[stacks 06NJ] #check (AlgebraicGeometry.AlgebraicSpace.IsZariskiLocallyQuasiSeparated.instT0SpacePoints :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsZariskiLocallyQuasiSeparated X],
    T0Space (AlgebraicGeometry.AlgebraicSpace.Points X))

/- Lemma 66.15.1: the point space of a Zariski locally quasi-separated algebraic space is
quasi-sober. -/
@[stacks 06NJ] #check (AlgebraicGeometry.AlgebraicSpace.IsZariskiLocallyQuasiSeparated.instQuasiSoberPoints :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsZariskiLocallyQuasiSeparated X],
    QuasiSober (AlgebraicGeometry.AlgebraicSpace.Points X))

/- Lemma 66.15.1: every irreducible closed subset of the point space has a unique generic point. -/
@[stacks 06NJ] #check (AlgebraicGeometry.AlgebraicSpace.IsZariskiLocallyQuasiSeparated.existsUnique_isGenericPoint :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X : AlgebraicGeometry.AlgebraicSpace S}
    [AlgebraicGeometry.AlgebraicSpace.IsZariskiLocallyQuasiSeparated X]
    {T : Set (AlgebraicGeometry.AlgebraicSpace.Points X)},
    IsIrreducible T → IsClosed T →
      ∃! x : AlgebraicGeometry.AlgebraicSpace.Points X, IsGenericPoint x T)

end AlgebraicGeometry.AlgebraicSpace
