/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section

universe u v w

namespace Module

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

/-- The support of an element of a module, defined by the zero locus of its annihilator. -/
def elementSupport (A : Type u) [CommRing A] {M : Type v}
    [AddCommGroup M] [Module A M] (m : M) : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus ((A ∙ m : Submodule A M).annihilator)

/-- The element support of the zero element is empty. -/
theorem elementSupport_zero : elementSupport A (0 : M) = ∅ := sorry

/-- The support of a sum is contained in the union of the two element supports. -/
theorem elementSupport_add_subset (m n : M) :
    elementSupport A (m + n) ⊆ elementSupport A m ∪ elementSupport A n := sorry

/-- Scalar multiplication cannot enlarge element support. -/
theorem elementSupport_smul_subset (a : A) (m : M) :
    elementSupport A (a • m) ⊆ elementSupport A m := sorry

/-- Element support agrees with the module support of the cyclic submodule. -/
theorem elementSupport_eq_support_span (m : M) :
    elementSupport A m = support A (A ∙ m : Submodule A M) := sorry

/-- The support of a module is the union of the supports of all its elements. -/
theorem support_eq_iUnion_elementSupport :
    support A M = ⋃ m : M, elementSupport A m := sorry

/-- A linear map cannot enlarge the support of an element. -/
theorem elementSupport_map_subset (f : M →ₗ[A] N) (m : M) :
    elementSupport A (f m) ⊆ elementSupport A m := sorry

/-- Zero has element support contained in every prescribed subset. -/
theorem sectionsWithSupport_zero_mem (T : Set (PrimeSpectrum A)) :
    elementSupport A (0 : M) ⊆ T := sorry

/-- The sum of two elements supported in `T` is supported in `T`. -/
theorem sectionsWithSupport_add_mem (T : Set (PrimeSpectrum A)) {m n : M}
    (hm : elementSupport A m ⊆ T) (hn : elementSupport A n ⊆ T) :
    elementSupport A (m + n) ⊆ T := sorry

/-- A scalar multiple of an element supported in `T` is supported in `T`. -/
theorem sectionsWithSupport_smul_mem (T : Set (PrimeSpectrum A))
    (a : A) {m : M} (hm : elementSupport A m ⊆ T) :
    elementSupport A (a • m) ⊆ T := sorry

/-- The submodule of elements whose support is contained in `T`. -/
def sectionsWithSupport (T : Set (PrimeSpectrum A)) (M : Type v)
    [AddCommGroup M] [Module A M] : Submodule A M where
  carrier := {m | elementSupport A m ⊆ T}
  zero_mem' := sectionsWithSupport_zero_mem T
  add_mem' := sectionsWithSupport_add_mem T
  smul_mem' := sectionsWithSupport_smul_mem T

/-- Membership in `sectionsWithSupport T M` is the elementwise support condition. -/
theorem mem_sectionsWithSupport_iff (T : Set (PrimeSpectrum A)) (m : M) :
    m ∈ sectionsWithSupport T M ↔ elementSupport A m ⊆ T := sorry

/-- For a Noetherian ring and specialization-stable `T`, all sections are supported in `T`
if and only if the module support is contained in `T`. -/
theorem sectionsWithSupport_eq_top_iff_support_subset [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : Type v) [AddCommGroup M] [Module A M] :
    sectionsWithSupport T M = ⊤ ↔ support A M ⊆ T := sorry

/-- A linear map carries sections supported in `T` to sections supported in `T`. -/
theorem sectionsWithSupport_map_le (T : Set (PrimeSpectrum A)) (f : M →ₗ[A] N) :
    Submodule.map f (sectionsWithSupport T M) ≤ sectionsWithSupport T N := sorry

/-- The support of a direct sum is the union of the supports of its summands. -/
theorem support_directSum {I : Type w} (F : I → Type v)
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)] :
    support A (DirectSum I F) = ⋃ i, support A (F i) := sorry

end Module
