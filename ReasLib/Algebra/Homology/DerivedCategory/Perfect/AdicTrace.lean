/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Finiteness.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Adic.Homology
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Trace
public import ReasLib.Algebra.Ring.CommutatorQuotient.Equiv

/-!
# Traces and cohomology of Cartesian perfect prime-adic towers
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Ring

namespace CategoryTheory.DerivedCategory.IsPerfect

section StageTrace

variable {ℓ : ℕ}
variable (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
variable (hK : ∀ n, (K n).IsPerfect)
variable (π : ∀ n, End (K n))

/-- The stage trace `t_n = Tr(π_n | K_n)` in `ZMod (ℓ ^ (n + 1))`, obtained by
transporting `traceNatural` along `mkAddEquiv`. -/
noncomputable def stageTrace (n : ℕ) : ZMod (ℓ ^ (n + 1)) :=
  Ring.CommutatorQuotient.mkAddEquiv.symm ((hK n).traceNatural (π n))

/-- The stage trace is the inverse image of `traceNatural` under `mkAddEquiv`. -/
theorem stageTrace_spec (n : ℕ) :
    Ring.CommutatorQuotient.mk (stageTrace K hK π n) = (hK n).traceNatural (π n) := sorry

end StageTrace

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
variable (hK : ∀ n, (K n).IsPerfect)
variable (π : ∀ n, End (K n))
variable (φ : ∀ n, (derivedBaseChange ℓ n).obj (K (n + 1)) ≅ K n)
variable (hπ : ∀ n,
    CommSq ((derivedBaseChange ℓ n).map (π (n + 1))) (φ n).hom (φ n).hom (π n))

include φ hπ in
/-- The traces of compatible endomorphisms of a Cartesian perfect prime-adic tower
assemble uniquely to a p-adic integer. -/
theorem existsUnique_tracePadic :
    ∃! t : ℤ_[ℓ], ∀ n, PadicInt.toZModPow (n + 1) t = stageTrace K hK π n := sorry

include hK in
/-- The inverse-limit cohomology of a Cartesian perfect prime-adic tower is a finite module
over the p-adic integers in every degree. -/
theorem moduleFinite_homologyLimit (i : ℤ) :
    Module.Finite ℤ_[ℓ] (homologyLimit K φ i) := sorry

include hK in
/-- The inverse-limit cohomology of a Cartesian perfect prime-adic tower vanishes outside
finitely many degrees. -/
theorem finiteSupport_homologyLimit :
    {i : ℤ | ¬ IsZero (homologyLimit K φ i)}.Finite := sorry

include hK in
/-- The inverse-limit cohomology of a Cartesian perfect prime-adic tower becomes
finite-dimensional over the p-adic field. -/
theorem finiteDimensional_homologyLimitEndQEll (i : ℤ) :
    FiniteDimensional ℚ_[ℓ] (homologyLimitQEll K φ i) := sorry

/-- A perfect Cartesian prime-adic tower has finite inverse-limit cohomology in every degree. -/
instance instModuleFiniteHomologyLimit [hPerfect : Fact (∀ n, (K n).IsPerfect)] (i : ℤ) :
    Module.Finite ℤ_[ℓ] (homologyLimit K φ i) :=
  moduleFinite_homologyLimit K hPerfect.out φ i

/-- Rational inverse-limit cohomology of a perfect Cartesian prime-adic tower is
finite-dimensional. -/
instance instFiniteDimensionalHomologyLimitQEll [hPerfect : Fact (∀ n, (K n).IsPerfect)]
    (i : ℤ) : FiniteDimensional ℚ_[ℓ] (homologyLimitQEll K φ i) :=
  finiteDimensional_homologyLimitEndQEll K hPerfect.out φ i

/-- The alternating rational cohomological trace of compatible endomorphisms of a Cartesian
perfect prime-adic tower equals the image of their assembled integral trace. -/
theorem trace_eq_sum_homologyLimitEnd (t : ℤ_[ℓ])
    (ht : ∀ n, PadicInt.toZModPow (n + 1) t = stageTrace K hK π n) :
    (∑ᶠ i : ℤ, (-1 : ℚ_[ℓ]) ^ i *
        LinearMap.trace ℚ_[ℓ] _ (homologyLimitEndQEll K π φ hπ i)) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] t := sorry

end CategoryTheory.DerivedCategory.IsPerfect
