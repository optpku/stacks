/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Integral.Decomposition
public import ReasLib.RingTheory.RingHom.Fiber.PurelyInseparable

@[expose] public section

/-!
# Purely inseparable residue fields of integral decompositions

This file records the refinement in which every selected factor residue map
of an integral product decomposition is purely inseparable.
-/

universe u v

namespace PrimeSpectrum.IntegralDecomposition

/-- Every selected factor residue-field map in `D` is purely inseparable. -/
def HasPurelyInseparableResidueFields
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : IntegralDecomposition p S) : Prop :=
  ∀ i, (D.factorResidueMap i).IsPurelyInseparable

/-- Pure inseparability of all selected residue maps is equivalent to its
pointwise formulation. -/
theorem hasPurelyInseparableResidueFields_iff
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : IntegralDecomposition p S) :
    D.HasPurelyInseparableResidueFields ↔
      ∀ i, (D.factorResidueMap i).IsPurelyInseparable := sorry

/-- The residue-field map at each selected factor is purely inseparable. -/
theorem factorResidueMap_isPurelyInseparable
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    {D : IntegralDecomposition p S}
    (hD : D.HasPurelyInseparableResidueFields) (i : D.product.index) :
    (D.factorResidueMap i).IsPurelyInseparable := sorry

end PrimeSpectrum.IntegralDecomposition
