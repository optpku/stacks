module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Topology.Inseparable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Support of a flat module

This leaf records the generalization-lifting property of the support map for
a finite module that is flat over the base ring.
-/

@[expose] public section

universe u v w

namespace Module

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

/-- If `N` is a finite `S`-module that is flat over `R`, then generalizations
lift along the map `support S N → Spec R` induced by
`PrimeSpectrum.comap (algebraMap R S)`. -/
@[stacks 080T]
theorem generalizingMap_support_comap_of_flat :
    GeneralizingMap
      (PrimeSpectrum.comap (algebraMap R S) ∘
        ((↑) : Module.support S N → PrimeSpectrum S)) := sorry

end Module
