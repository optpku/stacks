module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maximal ideals under specializing spectrum maps

The closed-point consequence of a specializing map on prime spectra is naturally a statement
about an explicit ring homomorphism. The algebra-map formulation used by the chapter is a thin
specialization of this owner.
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.112.2 (Stacks `00OI`): a specializing map on spectra pulls a maximal ideal back to
a maximal ideal. -/
@[stacks 00OI]
theorem isMaximal_comap_of_specializing
    (f : R →+* S) (h : SpecializingMap (PrimeSpectrum.comap f))
    (q : Ideal S) [q.IsMaximal] :
    (q.comap f).IsMaximal := sorry

end RingHom
