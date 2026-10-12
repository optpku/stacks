/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.PrimitiveElement
public import ReasLib.RingTheory.Etale.Point
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale points realizing finite separable residue extensions

This leaf realizes a finite separable extension of a prime residue field by a
pointed etale extension.  The constructed algebra and selected prime remain
available through `PrimeSpectrum.EtalePoint`.

@stack 00UD
-/

@[expose] public section

universe u v

namespace PrimeSpectrum.EtalePoint

/-- Every finite separable extension of the residue field at a prime is the
residue field of a point on an etale algebra over the base ring. -/
@[stacks 00UD "etale point realizing a finite separable residue extension"]
theorem exists_with_residueFieldEquiv
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (L : Type v) [Field L] [Algebra p.asIdeal.ResidueField L]
    [FiniteDimensional p.asIdeal.ResidueField L]
    [Algebra.IsSeparable p.asIdeal.ResidueField L] :
    ∃ U : PrimeSpectrum.EtalePoint.{u, u} p,
      -- Local instance justification (defeq pin): expose the explicit residue-field
      -- algebra carried by the selected pointed etale extension in this proposition.
      letI : Algebra p.asIdeal.ResidueField U.point.asIdeal.ResidueField :=
        U.residueFieldAlgebra
      Nonempty (U.point.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] L) := sorry

end PrimeSpectrum.EtalePoint
