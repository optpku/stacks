module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Definition_87_5_1_Taut

/-!
# The t-adic power series ring

`AdicPowerSeries k` is the type synonym of `PowerSeries k` carrying the
`(X)`-adic topology, so the discrete topology on a coefficient field `k` does
not collide with a product topology on `k[[t]]`.
-/

@[expose] public section

noncomputable section

universe u

namespace TopologicalRing

/-- A field with the discrete topology is a weakly admissible topological ring. -/
instance instIsWeaklyAdmissibleRing_of_discreteTopology
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k] :
    IsWeaklyAdmissibleRing k :=
  sorry

end TopologicalRing

/-- Formal power series `k[[t]]` equipped with the `t`-adic topology rather than
any product topology inherited from `k`. -/
def AdicPowerSeries (k : Type u) [CommRing k] : Type u :=
  PowerSeries k

namespace AdicPowerSeries

/-- The ring structure of `k[[t]]` on `AdicPowerSeries k`. -/
instance instCommRing (k : Type u) [CommRing k] : CommRing (AdicPowerSeries k) :=
  inferInstanceAs (CommRing (PowerSeries k))

/-- The coefficient algebra structure `k → k[[t]]` on `AdicPowerSeries k`. -/
instance instAlgebra (k : Type u) [CommRing k] : Algebra k (AdicPowerSeries k) :=
  inferInstanceAs (Algebra k (PowerSeries k))

/-- The indeterminate `t` of `k[[t]]`. -/
def x (k : Type u) [CommRing k] : AdicPowerSeries k :=
  PowerSeries.X

/-- The principal ideal `(t)` of `k[[t]]`. -/
def xIdeal (k : Type u) [CommRing k] : Ideal (AdicPowerSeries k) :=
  Ideal.span {x k}

/-- The topology on `AdicPowerSeries k` is the `(t)`-adic topology. -/
instance instTopologicalSpace (k : Type u) [CommRing k] :
    TopologicalSpace (AdicPowerSeries k) :=
  (xIdeal k).adicTopology

/-- The `(t)`-adic topology is a ring topology on `k[[t]]`. -/
instance instIsTopologicalRing (k : Type u) [CommRing k] :
    IsTopologicalRing (AdicPowerSeries k) :=
  sorry

/-- The `(t)`-adic topology is linear on `k[[t]]`. -/
instance instIsLinearTopology (k : Type u) [CommRing k] :
    IsLinearTopology (AdicPowerSeries k) (AdicPowerSeries k) :=
  sorry

/-- The ambient topology on `AdicPowerSeries k` is the `(t)`-adic topology. -/
theorem isAdic_xIdeal (k : Type u) [CommRing k] : IsAdic (xIdeal k) :=
  sorry

/-- `k[[t]]` with the `t`-adic topology is weakly admissible. -/
instance instIsWeaklyAdmissibleRing (k : Type u) [Field k] :
    TopologicalRing.IsWeaklyAdmissibleRing (AdicPowerSeries k) :=
  sorry

/-- The algebra map from a discrete field to `t`-adic `k[[t]]` is continuous. -/
theorem continuous_algebraMap {k : Type u} [Field k] [TopologicalSpace k]
    [DiscreteTopology k] : Continuous (algebraMap k (AdicPowerSeries k)) :=
  sorry

/-- The algebra map from a discrete field to `t`-adic `k[[t]]` is not taut. -/
theorem not_isTaut_algebraMap {k : Type u} [Field k] [TopologicalSpace k]
    [DiscreteTopology k] : ¬ (algebraMap k (AdicPowerSeries k)).IsTaut :=
  sorry

end AdicPowerSeries
