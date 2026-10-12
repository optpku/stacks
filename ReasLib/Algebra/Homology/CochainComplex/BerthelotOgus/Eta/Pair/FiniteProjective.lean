/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Pair
public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective

/-!
# Finite-projective visible power modules

For a nonzerodivisor `f`, multiplication by the visible powers of `f` identifies the relevant
power submodules with the original finite free terms.  Their reductions modulo `(f)` are therefore
finite projective over `A / (f)`.
-/

@[expose] public section

open scoped nonZeroDivisors

universe u v

namespace CochainComplex.BerthelotOgus.Nat.Pair

variable {A : Type u} [CommRing A]

/-- A visible power submodule of a free term is free. -/
theorem powerSubmodule_free_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Free A (K.X n)] (hf : f ∈ nonZeroDivisors A) :
    Module.Free A (powerSubmodule f K n) := sorry

/-- A visible power submodule of a finite term is finite. -/
theorem powerSubmodule_finite_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Finite A (K.X n)] (hf : f ∈ nonZeroDivisors A) :
    Module.Finite A (powerSubmodule f K n) := sorry

/-- The next visible power submodule of a free term is free. -/
theorem nextPowerSubmodule_free_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Free A (K.X (n + 1))] (hf : f ∈ nonZeroDivisors A) :
    Module.Free A (nextPowerSubmodule f K n) := sorry

/-- The next visible power submodule of a finite term is finite. -/
theorem nextPowerSubmodule_finite_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Finite A (K.X (n + 1))] (hf : f ∈ nonZeroDivisors A) :
    Module.Finite A (nextPowerSubmodule f K n) := sorry

end CochainComplex.BerthelotOgus.Nat.Pair

namespace CochainComplex.BerthelotOgus.Nat.Reduction.Pair

open CochainComplex.BerthelotOgus.Nat.Pair

variable {A : Type u} [CommRing A]

/-- The first reduced visible power module is finite over `A / (f)`. -/
theorem powerQuotient_finite_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Finite A (K.X n)] (hf : f ∈ nonZeroDivisors A) :
    Module.Finite (A ⧸ principalIdeal f) (powerQuotient f K n) := sorry

/-- The first reduced visible power module is projective over `A / (f)`. -/
theorem powerQuotient_projective_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Free A (K.X n)] (hf : f ∈ nonZeroDivisors A) :
    Module.Projective (A ⧸ principalIdeal f) (powerQuotient f K n) := sorry

/-- The second reduced visible power module is finite over `A / (f)`. -/
theorem nextPowerQuotient_finite_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Finite A (K.X (n + 1))] (hf : f ∈ nonZeroDivisors A) :
    Module.Finite (A ⧸ principalIdeal f) (nextPowerQuotient f K n) := sorry

/-- The second reduced visible power module is projective over `A / (f)`. -/
theorem nextPowerQuotient_projective_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Free A (K.X (n + 1))] (hf : f ∈ nonZeroDivisors A) :
    Module.Projective (A ⧸ principalIdeal f) (nextPowerQuotient f K n) := sorry

end CochainComplex.BerthelotOgus.Nat.Reduction.Pair
