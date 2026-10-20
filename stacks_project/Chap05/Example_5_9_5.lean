module

public import ReasLib.Topology.Compactness.ClosedPoints
public import ReasLib.Topology.Order.LowerSet.PNat
public import ReasLib.AlgebraicGeometry.Noetherian.ClosedPoints
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Example 5.9.5

The Noetherian closed-point theorem and the lower-set topology on positive
integers are reusable support API. The non-realizability conclusion is the
direct scheme specialization of their closed-point obstruction.
-/

/- Example 5.9.5 (1): every nonempty Kolmogorov Noetherian space has a closed point. -/
@[stacks 02HZ "closed point in a nonempty Kolmogorov Noetherian space"]
#check @CompactSpace.exists_closedPoint

/- Example 5.9.5 (2): lower-set opens on positive integers have the initial-segment form. -/
@[stacks 02HZ "open sets of the positive-integer lower-set topology"]
#check @Topology.WithLowerSet.pnat_isOpen_iff

/- Example 5.9.5 (3): positive integers with the lower-set topology are locally Noetherian. -/
@[stacks 02HZ "local Noetherianity of the positive-integer lower-set topology"]
#check
  (inferInstance :
    TopologicalSpace.LocallyNoetherianSpace (Topology.WithLowerSet ℕ+))

/- Example 5.9.5 (4): positive integers with the lower-set topology have no closed points. -/
@[stacks 02HZ "absence of closed points in the positive-integer lower-set topology"]
#check @Topology.WithLowerSet.pnat_closedPoints_eq_empty

/- Example 5.9.5 (5): the positive integers with the lower-set topology are not homeomorphic to
the underlying topological space of a locally Noetherian scheme. -/
@[stacks 02HZ "non-realizability as a locally Noetherian scheme space"]
#check fun (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X] ↦
  X.not_homeomorphic_of_closedPoints_eq_empty
    (A := Topology.WithLowerSet ℕ+) Topology.WithLowerSet.pnat_closedPoints_eq_empty
