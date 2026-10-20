module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Ramification loci of extensions of number fields

This file defines the relative discriminant and the complementary opens of the different and
discriminant, and records their pointwise ramification characterizations.
-/

@[expose] public section

open AlgebraicGeometry
open scoped NumberField

noncomputable section

universe u

namespace NumberField.Ramification

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The relative discriminant ideal is the relative norm of the different. -/
noncomputable def discriminantIdeal : Ideal (𝓞 K) :=
  Ideal.relNorm (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L))

/-- The open complement of the zero locus of the different in `Spec(𝓞 L)`. -/
def differentOpen : (Spec (.of (𝓞 L))).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (differentIdeal (𝓞 K) (𝓞 L)).carrier)ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- A prime belongs to `differentOpen K L` exactly when it avoids the zero locus of the
different. -/
theorem mem_differentOpen_iff (p : PrimeSpectrum (𝓞 L)) :
    p ∈ differentOpen K L ↔
      p ∉ PrimeSpectrum.zeroLocus (differentIdeal (𝓞 K) (𝓞 L)).carrier := sorry

/-- The open complement of the zero locus of the relative discriminant in `Spec(𝓞 K)`. -/
def discriminantOpen : (Spec (.of (𝓞 K))).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (discriminantIdeal K L).carrier)ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- A prime belongs to `discriminantOpen K L` exactly when it avoids the zero locus of the
relative discriminant. -/
theorem mem_discriminantOpen_iff (p : PrimeSpectrum (𝓞 K)) :
    p ∈ discriminantOpen K L ↔
      p ∉ PrimeSpectrum.zeroLocus (discriminantIdeal K L).carrier := sorry

/-- The different is the annihilator of the module of Kähler differentials. -/
theorem differentIdeal_eq_annihilator :
    differentIdeal (𝓞 K) (𝓞 L) = Module.annihilator (𝓞 L) Ω[𝓞 L⁄𝓞 K] := sorry

/-- The conventional unramified locus is the complement of the zero locus of the different. -/
theorem unramifiedLocus_eq_differentOpen :
    Algebra.unramifiedLocus (𝓞 K) (𝓞 L) = (differentOpen K L).carrier := sorry

/-- The relative discriminant ideal unfolds to the relative norm of the different. -/
theorem discriminantIdeal_eq_relNorm :
    discriminantIdeal K L = Ideal.relNorm (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L)) := sorry

/-- The zero locus of the relative discriminant consists exactly of the base primes ramified
in the extension of rings of integers. -/
theorem ramificationLocus_eq_zeroLocus :
    PrimeSpectrum.zeroLocus (discriminantIdeal K L).carrier =
      {p : PrimeSpectrum (𝓞 K) | ¬ Algebra.IsUnramifiedIn (𝓞 L) p.asIdeal} := sorry

end NumberField.Ramification
