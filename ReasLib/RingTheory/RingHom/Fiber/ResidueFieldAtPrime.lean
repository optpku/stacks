/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Fiber.Local
public import ReasLib.RingTheory.RingHom.Fiber.ResidueField
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Residue fields of canonical fiber primes

This leaf packages the residue-field equivalence attached to the canonical
fiber prime over a point of `PrimeSpectrum S`.  The construction is owned by
`PrimeSpectrum`, while the bijectivity input is the standard surjectivity-on-
stalks result for the residue-field fiber map.

@stack 0H8X
-/

@[expose] public section

noncomputable section

universe u v

open scoped Algebra.TensorProduct.Right

namespace PrimeSpectrum

/-- The residue field of the canonical fiber prime is canonically equivalent
to the residue field of the original target prime as an `S`-algebra. -/
noncomputable def fiberPrimeAt_residueFieldAlgEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    (fiberPrimeAt R S q).asIdeal.ResidueField ≃ₐ[S] q.asIdeal.ResidueField := by
  letI : Algebra S ((q.asIdeal.under R).Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  let hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ q.asIdeal (fiberPrimeAt R S q).asIdeal
          (Algebra.ofId S ((q.asIdeal.under R).Fiber S))
          (PrimeSpectrum.fiberPrimeAt_comap_algebraMap_asIdeal (R := R) (S := S) q).symm) := by
    simpa [Ideal.ResidueField.mapₐ,
      Algebra.TensorProduct.algebraMap_eq_includeRight] using
      RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        ((Ideal.surjectiveOnStalks_residueField (R := R) (q.asIdeal.under R)).baseChange')
        q.asIdeal (fiberPrimeAt R S q).asIdeal
        (PrimeSpectrum.fiberPrimeAt_comap_algebraMap_asIdeal (R := R) (S := S) q).symm
  exact
    (AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ q.asIdeal (fiberPrimeAt R S q).asIdeal
        (Algebra.ofId S ((q.asIdeal.under R).Fiber S))
        (PrimeSpectrum.fiberPrimeAt_comap_algebraMap_asIdeal (R := R) (S := S) q).symm)
      hbij).symm

end PrimeSpectrum

end
