/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.KrullDimension.FiniteType
public import ReasLib.RingTheory.KrullDimension.FiniteType.ResidueField
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.Topology.KrullDimension.Local
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local dimension of finite-type affine spectra

@stack 00OS
@stack 00OT
@stack 00OU
@stack 00P1
@stack 00P6

This leaf records standard local topological Krull-dimension formulae on the
prime spectrum of a finite-type algebra over a field. The owner is
`PrimeSpectrum`: every formula concerns a point of `Spec(S)`, while the
finite-type presentation is only a hypothesis.
-/

universe u v w

namespace PrimeSpectrum

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S]

/-- Lemma 10.114.5 (Stacks 00OT): at a point of the spectrum of a finite-type
algebra over a field, local topological Krull dimension is the supremum of the
dimensions of the irreducible components through that point. -/
@[stacks 00OT "finite-type affine local dimension by components"]
theorem topologicalKrullDimAt_eq_iSup_irreducibleComponents_through
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S)) := sorry

/-- On an equidimensional finite-type affine spectrum over a field, local topological Krull
dimension is independent of the chosen point. -/
@[stacks 00OT "equidimensional finite-type affine local dimension"]
theorem topologicalKrullDimAt_eq_of_equidimensional
    [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)]
    (x y : PrimeSpectrum S) :
    topologicalKrullDimAt x = topologicalKrullDimAt y := sorry

/-- On an equidimensional finite-type affine spectrum over a field, local topological Krull
dimension at every point equals the global topological Krull dimension. -/
@[stacks 00OT "equidimensional finite-type affine local-to-global dimension"]
theorem topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional
    [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)]
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x = topologicalKrullDim (PrimeSpectrum S) := sorry

/-- Lemma 10.114.5 (Stacks 00OT): at a point of the spectrum of a finite-type
algebra over a field, local topological Krull dimension is the infimum of the
dimensions of maximal localizations above that point. -/
@[stacks 00OT "finite-type affine local dimension by maximal localizations"]
theorem topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal },
        ringKrullDim (Localization.AtPrime m.1.asIdeal) := sorry

/-- On an irreducible finite-type affine spectrum over a field, every point has local topological
Krull dimension equal to the Krull dimension of the coordinate ring. -/
@[stacks 00OT "irreducible finite-type affine local dimension"]
theorem topologicalKrullDimAt_eq_ringKrullDim_of_irreducibleSpace
    {F : Type u} {A : Type v} [Field F] [CommRing A] [Algebra F A]
    [Algebra.FiniteType F A] [IrreducibleSpace (PrimeSpectrum A)] (x : PrimeSpectrum A) :
    topologicalKrullDimAt x = ringKrullDim A := sorry

/-- Every point of affine space with finitely many coordinates over a field has local topological
Krull dimension equal to the cardinality of its coordinate type. -/
@[stacks 00OT "affine-space local dimension"]
theorem topologicalKrullDimAt_mvPolynomial_eq_card
    {F : Type u} {ι : Type w} [Field F] [Finite ι]
    (x : PrimeSpectrum (MvPolynomial ι F)) :
    topologicalKrullDimAt x = (Nat.card ι : WithBot ℕ∞) := sorry

/-- For a point of a finite-type algebra over a field, local topological Krull dimension is the
sum of prime height and the transcendence degree of the residue field. -/
@[stacks 00P1 "finite-type affine local dimension by height and residue transcendence"]
theorem topologicalKrullDimAt_eq_height_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      (x.asIdeal.height : WithBot ℕ∞) + Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := sorry

/-- For a point of a finite-type algebra over a field, local topological Krull dimension is the
Krull dimension of the local ring plus the transcendence degree of the residue field. -/
@[stacks 00P1 "finite-type affine local dimension by local ring and residue transcendence"]
theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ringKrullDim (Localization.AtPrime x.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := sorry

end PrimeSpectrum

namespace MaximalSpectrum

/-- If a closed point of a finite-type affine scheme lies on every irreducible
component, its local topological dimension is the global Krull dimension. -/
@[stacks 00P6 "(3), global dimension at a closed point"]
theorem ringKrullDim_eq_topologicalKrullDimAt_of_minimalPrimes_le
    {F : Type u} {A : Type v} [Field F] [CommRing A] [Algebra F A]
    [Algebra.FiniteType F A] (m : MaximalSpectrum A)
    (hmin : ∀ p : minimalPrimes A, p.1 ≤ m.asIdeal) :
    ringKrullDim A = topologicalKrullDimAt m.toPrimeSpectrum := sorry

/-- If a closed point of a finite-type affine scheme contains every minimal
prime, localization at that point preserves Krull dimension. -/
@[stacks 00P6 "(3), dimension of the closed-point localization"]
theorem ringKrullDim_eq_localizationAtPrime_of_minimalPrimes_le
    {F : Type u} {A : Type v} [Field F] [CommRing A] [Algebra F A]
    [Algebra.FiniteType F A] (m : MaximalSpectrum A)
    (hmin : ∀ p : minimalPrimes A, p.1 ≤ m.asIdeal) :
    ringKrullDim A = ringKrullDim (Localization.AtPrime m.asIdeal) := sorry

/-- At a closed point of a finite-type affine spectrum over a field, local topological Krull
dimension equals the Krull dimension of the corresponding maximal localization. -/
@[stacks 00OU "closed-point finite-type affine local dimension"]
theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime
    {F : Type u} {A : Type v} [Field F] [CommRing A] [Algebra F A]
    [Algebra.FiniteType F A] (m : MaximalSpectrum A) :
    topologicalKrullDimAt m.toPrimeSpectrum =
      ringKrullDim (Localization.AtPrime m.asIdeal) := sorry

end MaximalSpectrum

namespace Algebra.FiniteType

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S] [IsDomain S]

/-- Lemma 10.114.4 (Stacks tag `00OS`): a finite-type domain over a field has the same
Krull dimension as each of its maximal localizations. -/
@[stacks 00OS "dimension of a finite-type domain at a maximal point"]
theorem krullDim_eq_localizationAtMaximal
    (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := sorry

end Algebra.FiniteType
