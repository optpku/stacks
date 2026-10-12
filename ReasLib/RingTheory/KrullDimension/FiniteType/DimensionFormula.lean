/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Universally
public import ReasLib.RingTheory.LocalRing.ResidueField.Transcendence
public import ReasLib.RingTheory.Localization.FractionRing.Transcendence

@[expose] public section

/-!
# Dimension formula for finite-type domain maps

This leaf owns the prime-spectrum forms of the dimension formula for an
injective finite-type map of domains. The point `q : PrimeSpectrum S` is the
canonical owner of its contracted prime and residue-field extension; the
fraction-field contribution is encapsulated by
`FractionRing.trdegNatOf` so consumers do not choose a
fraction-field algebra instance.
-/

namespace PrimeSpectrum

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S]

/-- For an injective finite-type map of domains, the height of `q` plus the transcendence degree
of `κ(q)` over the residue field of its contraction is bounded by the height of the contraction
plus the generic transcendence degree. -/
@[stacks 02IJ "(1), prime-spectrum form"]
theorem height_add_residueFieldTrdeg_le_of_finiteType
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.height q.asIdeal) +
        Cardinal.toNat
          (Ideal.ResidueField.trdeg (q.asIdeal.under R) q.asIdeal) ≤
      ENat.toNat (Ideal.height (q.asIdeal.under R)) +
        FractionRing.trdegNatOf hinj := sorry
/- Proof strategy: apply the finite-type height formula at `q`, identify the
contracted residue extension with `Ideal.ResidueField.trdeg`, and rewrite the
generic term through `FractionRing.trdegNatOf`. -/

/-- For a universally catenary base, the finite-type domain dimension inequality is an equality. -/
@[stacks 02IJ "(2), prime-spectrum form"]
theorem height_add_residueFieldTrdeg_eq_of_universallyCatenary
    [Algebra.FiniteType R S] [UniversallyCatenaryRing.{u, v} R]
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.height q.asIdeal) +
        Cardinal.toNat
          (Ideal.ResidueField.trdeg (q.asIdeal.under R) q.asIdeal) =
      ENat.toNat (Ideal.height (q.asIdeal.under R)) +
        FractionRing.trdegNatOf hinj := sorry
/- Proof strategy: invoke the universally catenary dimension formula and use
the same named residue-field and fraction-ring transcendence-degree bridges. -/

end PrimeSpectrum

namespace Ideal.ResidueField.DimensionFormula

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Algebra (FractionRing R) (FractionRing S)]
  [IsScalarTower R (FractionRing R) (FractionRing S)]

/-- For an injective finite-type map of Noetherian domains and prime ideals `p` and `q` with `q`
lying over `p`, the height and residue-field transcendence-degree sum for `q` is bounded by the
corresponding sum for `p` and the fraction fields. -/
@[stacks 02IJ "(1), raw fraction-field form"]
theorem finiteType_le
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] (hq : q.LiesOver p) :
    ENat.toNat (Ideal.height q) +
        Cardinal.toNat (Ideal.ResidueField.trdeg p q) ≤
      ENat.toNat (Ideal.height p) +
        Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := sorry
/- Proof strategy: package `p` and `q` as the contracted prime-spectrum point,
apply the canonical inequality, then rewrite lying-over and the selected raw
fraction-field algebra in the source-facing conclusion. -/

end Ideal.ResidueField.DimensionFormula
