module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.QuasiFinite.Decomposition
public import ReasLib.RingTheory.RingHom.Fiber.PurelyInseparable

@[expose] public section

/-!
# Purely inseparable residue fields in quasi-finite decompositions

@stack 00UL

The condition is stated for the canonical residue-field maps owned by the
decomposition, without installing competing residue-field algebra instances.
-/

universe u v

namespace PrimeSpectrum.QuasiFiniteDecomposition

/-- Every selected finite factor has purely inseparable residue field over the
selected base prime. -/
@[stacks 00UL "purely inseparable residue fields of a quasi-finite decomposition"]
def HasPurelyInseparableResidueFields
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) : Prop :=
  ∀ i, (D.factorResidueMap i).IsPurelyInseparable

/-- The residue-field map at each selected factor is purely inseparable. -/
@[stacks 00UL "purely inseparable residue field map of a quasi-finite factor"]
theorem factorResidueMap_isPurelyInseparable
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    {D : QuasiFiniteDecomposition p S}
    (hD : D.HasPurelyInseparableResidueFields) (i : D.ι) :
    (D.factorResidueMap i).IsPurelyInseparable := sorry

/-- The canonical residue-field map at a selected factor is finite and purely
inseparable. -/
@[stacks 00UL "finite purely inseparable residue field map"]
theorem factorResidueMap_spec
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    {D : QuasiFiniteDecomposition p S}
    (hD : D.HasPurelyInseparableResidueFields) (i : D.ι) :
    (D.factorResidueMap i).Finite ∧
      (D.factorResidueMap i).IsPurelyInseparable := sorry

end PrimeSpectrum.QuasiFiniteDecomposition
