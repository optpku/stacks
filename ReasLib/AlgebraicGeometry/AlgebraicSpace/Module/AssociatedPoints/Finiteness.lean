module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import Mathlib.Topology.Sets.Opens

/-!
# Finiteness of associated points

The associated points of a coherent module on a locally Noetherian algebraic space
form a finite set on every quasi-compact open subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules TopologicalSpace
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The associated points of a coherent module on a locally Noetherian algebraic space
that lie in a quasi-compact open subset form a finite set. -/
@[stacks 0CUN]
theorem associatedPoints_inter_quasiCompactOpen_finite
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (W : Opens |X|) (hW : IsCompact (W : Set |X|)) :
    (F.weakAss ∩ (W : Set |X|)).Finite :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
