/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The first Frobenius-root extension

@stack 030V
@stack 030W

This leaf provides a concrete model of the field obtained by adjoining first
Frobenius roots at a field's exponential characteristic.  It is realized as an
intermediate field of a fixed algebraic closure, so it has canonical maps to
the algebraic and relative perfect closures used by tensor-product arguments;
in characteristic zero the exponential characteristic is `1`.
-/

@[expose] public section

open IntermediateField

universe u

namespace IntermediateField

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]

/-- The subfield of `AlgebraicClosure k` whose `p`th powers come from `k`. -/
@[stacks 030W "first Frobenius-root subfield"]
noncomputable def onePthRootSubfield : Subfield (AlgebraicClosure k) :=
  let _ : ExpChar (AlgebraicClosure k) p :=
    expChar_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  Subfield.comap (frobenius (AlgebraicClosure k) p) ((algebraMap k (AlgebraicClosure k)).fieldRange)

/-- The image of `k` belongs to its first Frobenius-root subfield. -/
@[stacks 030W "first Frobenius-root subfield"]
theorem algebraMap_mem_onePthRootSubfield (x : k) :
    algebraMap k (AlgebraicClosure k) x ∈ onePthRootSubfield k p := sorry

/-- The intermediate field of `AlgebraicClosure k` formed by adjoining first Frobenius roots. -/
@[stacks 030W]
noncomputable def onePthRootExtension : IntermediateField k (AlgebraicClosure k) :=
  (onePthRootSubfield k p).toIntermediateField (algebraMap_mem_onePthRootSubfield k p)

/-- An element of `AlgebraicClosure k` lies in `onePthRootExtension k p` exactly when its `p`th
power belongs to the image of `k`. -/
@[stacks 030W]
theorem mem_onePthRootExtension_iff {x : AlgebraicClosure k} :
    x ∈ onePthRootExtension k p ↔
      x ^ p ∈ (algebraMap k (AlgebraicClosure k)).fieldRange := sorry

variable {k p}

/-- The first Frobenius-root extension is contained in the relative perfect closure inside an
algebraic closure. -/
@[stacks 030V]
theorem onePthRootExtension_le_perfectClosure :
    onePthRootExtension k p ≤ perfectClosure k (AlgebraicClosure k) := sorry

/-- An intermediate field of the first Frobenius-root extension is purely inseparable over the
base field.  This is the reusable subextension form; it does not require a finite-dimensionality
assumption. -/
@[stacks 030V "subextension of first Frobenius-root extension"]
theorem isPurelyInseparable_of_le_onePthRootExtension
    {K : IntermediateField k (AlgebraicClosure k)}
    (hK : K ≤ onePthRootExtension k p) :
    IsPurelyInseparable k K := sorry

/-- The canonical first Frobenius-root extension is purely inseparable over its base field. -/
@[stacks 030V "first Frobenius-root extension is purely inseparable"]
instance onePthRootExtension.isPurelyInseparable :
    IsPurelyInseparable k (onePthRootExtension k p) :=
  sorry

end IntermediateField
