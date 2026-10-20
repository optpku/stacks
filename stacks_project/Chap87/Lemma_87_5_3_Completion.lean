module

public import ReasLib.Topology.Algebra.LinearTopology.Completion.Ring

@[expose] public section

universe u

/- Ring homomorphisms associated to the inverse-limit completion. -/
#check (IsLinearTopology.Completion.coeRingHom :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A], A →+* IsLinearTopology.Completion A A)

#check (IsLinearTopology.Completion.πRingHom :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (I : Ideal A), IsOpen (I : Set A) →
    IsLinearTopology.Completion A A →+* A ⧸ I)
