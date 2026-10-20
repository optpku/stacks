module

public import ReasLib.Topology.Algebra.Ring.Taut

@[expose] public section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

#check (RingHom.IsTaut : (A →+* B) → Prop)
