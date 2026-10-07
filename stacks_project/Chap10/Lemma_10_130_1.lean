module

public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Flat.Locus
public import ReasLib.RingTheory.CohenMacaulay.FlatLocal
public import ReasLib.RingTheory.KrullDimension.Fiber
public import stacks_project.Chap10.Lemma_10_122_4
public import ReasLib.RingTheory.KrullDimension.QuasiFinite
public import stacks_project.Chap10.Lemma_10_114_7
public import ReasLib.RingTheory.CohenMacaulay.Flatness
public import stacks_project.Chap10.Proposition_10_114_2
public import ReasLib.RingTheory.CohenMacaulay.Regular
public import ReasLib.RingTheory.KrullDimension.Finite
public import ReasLib.RingTheory.KrullDimension.FiniteType
public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
public import ReasLib.RingTheory.KrullDimension.FiniteType.ResidueField
public import ReasLib.RingTheory.KrullDimension.Prime
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.LocalRing.ResidueField.Transcendence
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-! @stack 00RE

The public item is the canonical equality of the polynomial-presentation flat locus with the
intersection of the Cohen--Macaulay locus and the local dimension stratum.  The presentation map
is an `AlgHom`, while quasi-finiteness is carried by its underlying `RingHom` property.
-/

universe u v

open scoped Algebra.TensorProduct.Right

section

variable {k : Type u} [Field k]
variable {d : ℕ}
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

-- Local notation justification: `P` is the single polynomial presentation ring fixed by the
-- source statement and keeps the locus formula readable without creating a global abbreviation.
local notation "P" => MvPolynomial (Fin d) k

/-- Chap10 Lemma 10 130 1: for a finite type `k`-algebra `S` and a quasi-finite polynomial
presentation `π : k[y₁, …, y_d] →ₐ[k] S`, the flatness locus of `S` over the presentation ring
is the intersection of the Cohen--Macaulay locus and the `d`-dimensional local stratum. -/
@[stacks 00RE]
theorem flat_locus_eq_cohenMacaulay_inter_dimensionStratum_of_quasiFinite_polynomial
    (π : P →ₐ[k] S) (hπ : RingHom.QuasiFinite π.toRingHom) :
    let _ : Algebra P S := π.toAlgebra
    let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
    Module.flatOverBaseLocus P S S =
      { q : PrimeSpectrum S |
          Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal) } ∩
        PrimeSpectrum.dimensionStratum S d := sorry

end
