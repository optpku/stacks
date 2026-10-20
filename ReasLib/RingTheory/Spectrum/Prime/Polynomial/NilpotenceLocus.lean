module

public import ReasLib.RingTheory.Algebra.Fiber.NilpotenceLocus
public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiberwise Nilpotence Loci

For an element of an algebra, its nilpotence locus records the base primes over which the element
becomes nilpotent in the canonical fiber algebra.  For finite free algebras this locus is the zero
locus of the non-leading characteristic-polynomial coefficients.

@stack 00FC
-/

@[expose] public section

open PrimeSpectrum
open scoped TensorProduct

universe u v

namespace Algebra

variable (R : Type u) {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

namespace NilpotenceLocus

/-- For a finite free algebra, fiberwise nilpotence is cut out by the non-leading coefficients of
the characteristic polynomial of multiplication by `f`. -/
@[stacks 00FC "characteristic-polynomial equations for fiberwise nilpotence"]
theorem eq_zeroLocus_charpoly_coeffs
    [Module.Free R A] [Module.Finite R A] (f : A) :
    nilpotenceLocus R f =
      zeroLocus
        (Set.range fun i : Fin (Module.finrank R A) ↦
          (Algebra.lmul R A f).charpoly.coeff i) := by
  ext p
  rw [mem_nilpotenceLocus, PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff]
  change IsNilpotent
    ((Algebra.TensorProduct.comm R A p.asIdeal.ResidueField)
      ((algebraMap A (A ⊗[R] p.asIdeal.ResidueField)) f)) ↔ _
  rw [IsNilpotent.map_iff (Algebra.TensorProduct.comm R A _).injective,
    isNilpotent_tensor_residueField_iff, Nat.forall_lt_iff_fin]
  simp only [SetLike.mem_coe]

/-- Membership in the nilpotence locus is detected coefficient by coefficient. -/
@[stacks 00FC "pointwise characteristic-polynomial equations"]
theorem mem_iff_forall_charpoly_coeff_mem
    [Module.Free R A] [Module.Finite R A] (f : A) (p : PrimeSpectrum R) :
    p ∈ nilpotenceLocus R f ↔
      ∀ i : Fin (Module.finrank R A), (Algebra.lmul R A f).charpoly.coeff i ∈ p.asIdeal := by
  rw [eq_zeroLocus_charpoly_coeffs R f, PrimeSpectrum.mem_zeroLocus,
    Set.range_subset_iff]
  simp only [SetLike.mem_coe]

/-- Pointwise form of the characteristic-polynomial description of the nilpotence locus. -/
@[stacks 00FC "fiber nilpotence criterion"]
theorem isNilpotent_iff_mem_zeroLocus
    [Module.Free R A] [Module.Finite R A] (f : A) (p : PrimeSpectrum R) :
    IsNilpotent ((algebraMap A (A ⊗[R] p.asIdeal.ResidueField)) f) ↔
      p ∈ zeroLocus
        (Set.range fun i : Fin (Module.finrank R A) ↦
          (Algebra.lmul R A f).charpoly.coeff i) := by
  simpa [PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff] using
    (isNilpotent_tensor_residueField_iff f p.asIdeal).trans Nat.forall_lt_iff_fin

/-- The fiberwise nilpotence locus of an element in a finite free algebra is closed. -/
@[stacks 00FC "closedness of the fiberwise nilpotence locus"]
theorem isClosed
    [Module.Free R A] [Module.Finite R A] (f : A) :
    IsClosed (nilpotenceLocus R f) := by
  rw [eq_zeroLocus_charpoly_coeffs R f]
  exact PrimeSpectrum.isClosed_zeroLocus _

end NilpotenceLocus

end Algebra
