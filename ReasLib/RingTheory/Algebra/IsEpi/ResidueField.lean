module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.IsEpi
public import ReasLib.RingTheory.RingHom.Fiber.ResidueField

@[expose] public section

/-!
# Fibers and residue fields of algebra epimorphisms

This leaf owns the prime-spectrum and residue-field consequences of
`Algebra.IsEpi`. The statements use the canonical map of residue fields at a
target prime and do not choose any auxiliary local algebra instances.

@stack 04VW
-/

universe u v

namespace Algebra.IsEpi

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsEpi R S]

/-- Stacks Lemma 10.107.9 (1), tag `04VW`: contraction on prime spectra along an epic algebra is
injective. -/
@[stacks 04VW "(1)"]
theorem specComap_injective :
    Function.Injective (PrimeSpectrum.comap (algebraMap R S)) := sorry

namespace ResidueField

/-- Stacks Lemma 10.107.9 (2), tag `04VW`: an epic algebra has bijective residue-field maps at
every target prime. -/
@[stacks 04VW "(2)"]
theorem mapsBijective :
    RingHom.ResidueField.MapsBijective (algebraMap R S) := sorry

/-- The source-shaped pointwise form of `mapsBijective`, written with a named contraction to
match `Ideal.ResidueField.map`. -/
theorem map_bijective (q : PrimeSpectrum S) :
    Function.Bijective
      (Ideal.ResidueField.map (q.asIdeal.under R) q.asIdeal (algebraMap R S)
        (Ideal.over_def q.asIdeal (q.asIdeal.under R))) := sorry

end ResidueField

end Algebra.IsEpi
