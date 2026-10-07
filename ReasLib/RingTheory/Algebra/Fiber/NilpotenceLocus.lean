module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiberwise Nilpotence Loci

@stack 00FC
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

variable (R : Type u) {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The primes of the base over which an element becomes nilpotent in the fiber algebra. -/
@[stacks 00FC "fiberwise nilpotence locus"]
def nilpotenceLocus (f : A) : Set (PrimeSpectrum R) :=
  {p | IsNilpotent
    ((Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A) f)}

@[simp, stacks 00FC "membership in the fiberwise nilpotence locus"]
theorem mem_nilpotenceLocus (f : A) (p : PrimeSpectrum R) :
    p ∈ nilpotenceLocus R f ↔
      IsNilpotent ((Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A) f) :=
  Iff.rfl

end Algebra
