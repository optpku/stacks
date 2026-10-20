module

public import ReasLib.Topology.Specialization.FivePoint
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open Topology

/- Exercise 111.62.6 (Dimension) (1): the five-point specialization diagram
forces topological Krull dimension at least `2`. -/
@[stacks 0FWQ] #check
  (FivePointSpecialization.two_le_topologicalKrullDim :
    ∀ {X : Type u} [TopologicalSpace X] [QuasiSober X] [T0Space X]
      (D : FivePointSpecialization X),
      2 ≤ topologicalKrullDim X)

/- Exercise 111.62.6 (Dimension) (2): the lower bound is attained by the
finite upper-set realization. -/
@[stacks 0FWQ] #check
  (FivePointSpecialization.standard_topologicalKrullDim_eq_two :
    topologicalKrullDim (Topology.WithUpperSet FivePointSpecialization.Point) = 2)

#check
  (FivePointSpecialization.standard :
    FivePointSpecialization (Topology.WithUpperSet FivePointSpecialization.Point))

/- Exercise 111.62.6 (Dimension) (3): in the finite-type spectrum situation,
`x ⤳ u` immediate implies `v ⤳ z` is not immediate. -/
@[stacks 0FWQ] #check
  (FivePointSpecialization.not_isImmediateSpecialization :
    ∀ {k A : Type u} [Field k] [CommRing A] [Algebra k A]
      [Algebra.FiniteType k A]
      (D : FivePointSpecialization (PrimeSpectrum A)),
      IsImmediateSpecialization D.x D.u →
        ¬ IsImmediateSpecialization D.v D.z)

/- The non-immediate specialization has an intermediate point. -/
#check
  (FivePointSpecialization.exists_mem_specialization_interval :
    ∀ {k A : Type u} [Field k] [CommRing A] [Algebra k A]
      [Algebra.FiniteType k A]
      (D : FivePointSpecialization (PrimeSpectrum A)),
      IsImmediateSpecialization D.x D.u →
        ∃ w, D.v ⤳ w ∧ w ⤳ D.z ∧ w ≠ D.v ∧ w ≠ D.z)
