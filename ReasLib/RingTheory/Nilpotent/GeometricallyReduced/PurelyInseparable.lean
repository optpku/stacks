/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.PurelyInseparable.OnePthRoot

/-!
# Purely inseparable tests for geometric reducedness

This leaf owns ring-side views of geometric reducedness detected by purely inseparable field
extensions.  The source-facing equivalences are represented here by atomic criteria, so later
field and scheme arguments can reuse the individual directions without depending on a bundled
TFAE wrapper.

@stack 030V
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.IsGeometricallyReduced

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

namespace FinitePurelyInseparable

/-- Reducedness after every finite purely inseparable field base change implies geometric
reducedness. -/
@[stacks 030V]
theorem of_forall_isReduced_tensorProduct
    (h : ∀ (K : Type (max u v)) [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsPurelyInseparable k K],
      IsReduced (K ⊗[k] S)) :
    Algebra.IsGeometricallyReduced k S := sorry

/-- Geometric reducedness is equivalent to reducedness after every finite purely inseparable
field base change. -/
@[stacks 030V]
theorem iff_forall_isReduced_tensorProduct :
    Algebra.IsGeometricallyReduced k S ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K]
        [FiniteDimensional k K] [IsPurelyInseparable k K],
        IsReduced (K ⊗[k] S) := sorry

end FinitePurelyInseparable

namespace OnePthRoot

/-- At exponential characteristic `p`, geometric reducedness is equivalent to reducedness after
tensoring with the canonical first Frobenius-root extension. The characteristic-zero case is
included with `p = 1`. -/
@[stacks 030V]
theorem iff_isReduced_tensorProduct
    {p : ℕ} [ExpChar k p] :
    Algebra.IsGeometricallyReduced k S ↔
      IsReduced (IntermediateField.onePthRootExtension k p ⊗[k] S) := sorry

end OnePthRoot

namespace PerfectClosure

/-- Geometric reducedness is equivalent to reducedness after tensoring with the relative perfect
closure inside an algebraic closure. -/
@[stacks 030V]
theorem iff_isReduced_tensorProduct :
    Algebra.IsGeometricallyReduced k S ↔
      IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S) := sorry

end PerfectClosure

end

end Algebra.IsGeometricallyReduced
