module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.Algebra.Homology.HomologicalComplex.Bockstein
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise

/-!
# Localized Bockstein loci

For an integer-indexed cochain complex, the cycles-lift locus consists of primes containing the
chosen scalar at which cycles modulo its first power lift through the square quotient in every
degree.  Termwise regularity identifies this locus with vanishing of all localized Bockstein
operators.
@stack 0F81
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace HomologicalComplex.Bockstein

variable {A : Type u} [CommRing A]

/-- Extension of an integer-indexed module complex to the localization at a prime. -/
@[stacks 0F81 "localized integer-indexed complex"]
noncomputable abbrev localizedComplex
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (p : PrimeSpectrum A) :
    CochainComplex (ModuleCat.{max u v} (Localization.AtPrime p.asIdeal)) ℤ :=
  ((ModuleCat.extendScalars.{u, u, max u v}
      (algebraMap A (Localization.AtPrime p.asIdeal))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K

/-- The primes containing `f` at which cycles modulo `f` lift through reduction modulo
`(f)^2` in every degree. -/
@[stacks 0F81 "localized Bockstein cycles-lift locus"]
noncomputable def cyclesLiftLocus
    (f : A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ) : Set (PrimeSpectrum A) :=
  { p | f ∈ p.asIdeal ∧
      ∀ i : ℤ, CyclesLift (algebraMap A (Localization.AtPrime p.asIdeal) f)
        (localizedComplex K p) i }

/-- Termwise regularity is preserved by localization at a prime. -/
theorem localizedRegularity
    (f : A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) (p : PrimeSpectrum A) :
    (localizedComplex K p).IsTermwiseSMulRegular
      (algebraMap A (Localization.AtPrime p.asIdeal) f) := sorry

/-- The proof-explicit presentation of the localized Bockstein operator-vanishing locus. -/
noncomputable def operatorZeroLocusOf
    (f : A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) : Set (PrimeSpectrum A) :=
  { p | f ∈ p.asIdeal ∧ ∀ i : ℤ,
      operator (algebraMap A (Localization.AtPrime p.asIdeal) f)
        (localizedComplex K p) (localizedRegularity f K hK p)
        i (i + 1) (ComplexShape.up_mk i (i + 1) rfl) = 0 }

/-- The primes containing `f` at which every localized Bockstein operator vanishes.  The
regularity proof is owned by the shape-general bundled `Domain` object, so this canonical set has
no proof-valued data parameter. -/
@[stacks 0F81 "localized Bockstein operator-vanishing locus"]
noncomputable def operatorZeroLocus
    (f : A) (K : Domain.{u, 0, max u v} (c := ComplexShape.up ℤ) f) :
    Set (PrimeSpectrum A) :=
  operatorZeroLocusOf f K.obj K.property

/-- The operator-vanishing locus is independent of the displayed proof of termwise
regularity. -/
theorem operatorZeroLocus_proof_irrel
    (f : A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK hK' : K.IsTermwiseSMulRegular f) :
    operatorZeroLocusOf f K hK = operatorZeroLocusOf f K hK' := sorry

/-- Lemma 15.97.9, Tag 0F81: localized cycles lift exactly where all localized Bockstein
operators vanish. -/
@[stacks 0F81 "cycles lifting equals localized Bockstein vanishing"]
theorem cyclesLiftLocus_eq_operatorZeroLocus
    (f : A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) :
    cyclesLiftLocus f K = operatorZeroLocus f ⟨K, hK⟩ := sorry

/-- Regularity of the localized homology modules places a prime in the cycles-lift locus. -/
theorem mem_cyclesLiftLocus_of_localizedHomology_isSMulRegular
    (f : A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) (p : PrimeSpectrum A)
    (hpf : f ∈ p.asIdeal)
    (hH : ∀ i : ℤ,
      IsSMulRegular ((localizedComplex K p).homology i)
        (algebraMap A (Localization.AtPrime p.asIdeal) f)) :
    p ∈ cyclesLiftLocus f K := sorry

/-- If the localized scalar is a nonzerodivisor and every localized homology module is free,
then the prime belongs to the cycles-lift locus. -/
theorem mem_cyclesLiftLocus_of_localizedHomology_free
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) (p : PrimeSpectrum A)
    (hpf : f ∈ p.asIdeal)
    (hH : ∀ i : ℤ,
      Module.Free (Localization.AtPrime p.asIdeal)
        ((localizedComplex K p).homology i)) :
    p ∈ cyclesLiftLocus f K := sorry

/-- Freeness of the localizations of the original homology modules places a prime in the
cycles-lift locus.  This is the source-facing form of the flat-localization comparison. -/
theorem mem_cyclesLiftLocus_of_homologyAtPrime_free
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) (p : PrimeSpectrum A)
    (hpf : f ∈ p.asIdeal)
    (hH : ∀ i : ℤ,
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (K.homology i))) :
    p ∈ cyclesLiftLocus f K := sorry

end HomologicalComplex.Bockstein
