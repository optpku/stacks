/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Separated Quotients for Adic Filtrations

This leaf owns the quotient by the intersection of the powers of an ideal.
The module quotient is definitionally mathlib's `Hausdorffification`, so it
retains its existing universal-property API while gaining the canonical action
of the corresponding separated quotient ring.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The ideal `⋂ n, I ^ n` of elements infinitesimal for the `I`-adic
filtration. -/
@[stacks 065N "adic separated quotient"]
abbrev adicIntersection (I : Ideal R) : Ideal R :=
  ⨅ n : ℕ, I ^ n

/-- The `I`-adic intersection ideal is contained in every power of `I`. -/
theorem adicIntersection_le_pow (I : Ideal R) (n : ℕ) :
    adicIntersection I ≤ I ^ n := sorry

/-- The submodule `⋂ n, I ^ n M` of elements infinitesimal for the `I`-adic
filtration on `M`. -/
@[stacks 065N "adic separated quotient module"]
abbrev adicIntersectionSubmodule (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : Submodule R M :=
  ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)

/-- The `I`-adic intersection submodule is contained in every filtration
stage. -/
theorem adicIntersectionSubmodule_le_stage (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    adicIntersectionSubmodule I M ≤ I ^ n • (⊤ : Submodule R M) := sorry

/-- The quotient ring obtained by killing the `I`-adic intersection ideal. -/
@[stacks 065N "adic separated quotient"]
abbrev adicSeparatedQuotient (I : Ideal R) : Type u :=
  R ⧸ adicIntersection I

/-- The quotient of an `R`-module by its `I`-adic intersection submodule.
This is definitionally `Hausdorffification I M`. -/
@[stacks 065N "adic separated quotient module"]
abbrev adicSeparatedQuotientModule (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : Type v :=
  M ⧸ adicIntersectionSubmodule I M

namespace adicSeparatedQuotientModule

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The `I`-adic intersection ideal annihilates the corresponding separated
quotient module. -/
theorem isTorsionBySet (I : Ideal R) :
    Module.IsTorsionBySet R (adicSeparatedQuotientModule I M) (adicIntersection I) := sorry

/-- The separated quotient module has its canonical module structure over
the separated quotient ring. -/
instance module (I : Ideal R) :
    Module (adicSeparatedQuotient I) (adicSeparatedQuotientModule I M) :=
  Module.IsTorsionBySet.module (isTorsionBySet (M := M) I)

/-- Scalar multiplication on the separated quotient module is compatible
with the quotient map `R →+* R ⧸ ⋂ n, I ^ n`. -/
instance isScalarTower (I : Ideal R) :
    IsScalarTower R (adicSeparatedQuotient I) (adicSeparatedQuotientModule I M) :=
  Module.IsTorsionBySet.isScalarTower (isTorsionBySet (M := M) I)

end adicSeparatedQuotientModule

end Ideal
