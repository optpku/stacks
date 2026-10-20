module

public import ReasLib.RingTheory.AdicCompletion.LimitTopology
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

@[expose] public section

noncomputable section

universe u

namespace AdicCompletion

namespace WithLimitTopology

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The inverse-limit completion is a complete separated weakly admissible ring. -/
instance instIsWeaklyAdmissibleRing :
    TopologicalRing.IsWeaklyAdmissibleRing (WithLimitTopology I) := sorry

/-- The inverse-limit completion of a finitely generated ideal is an adic ring. -/
theorem isAdicRing_of_fg (hI : I.FG) :
    TopologicalRing.IsAdicRing (WithLimitTopology I) := sorry

end WithLimitTopology

end AdicCompletion
