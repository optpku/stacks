/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure
public import ReasLib.RingTheory.Normal.GeometricallyNormal

/-!
# Field tests for geometric normality

This leaf packages the standard equivalent test families for a field algebra's
geometric normality.  The intrinsic owner remains
`Algebra.IsGeometricallyNormal`; the finite-type, finite-purely-inseparable,
and perfect-closure clauses are views of that owner rather than new predicates.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.IsGeometricallyNormal

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- Normality of every field tensor base change can be tested on essentially finite type
extensions, finite purely inseparable extensions, or the perfect closure of an algebraic closure. -/
@[stacks 037Z]
theorem fieldTensorTests_tfae :
    List.TFAE [
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'],
        IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k']
        [Algebra.EssFiniteType k k'],
        IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k']
        [FiniteDimensional k k'] [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] A),
      IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A) ] := sorry

/-- The all-field test is equivalent to its finite purely inseparable restriction, without
requiring the hypotheses to be packaged as `IsGeometricallyNormal k A`. -/
@[stacks 037Z "field-test projection"]
theorem forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable :
    (∀ (k' : Type (max u v)) [Field k'] [Algebra k k'],
      IsNormalRing (k' ⊗[k] A)) ↔
    ∀ (k' : Type (max u v)) [Field k'] [Algebra k k']
      [FiniteDimensional k k'] [IsPurelyInseparable k k'],
      IsNormalRing (k' ⊗[k] A) := sorry

/-- The finite purely inseparable field test is an intrinsic criterion for
geometric normality. -/
@[stacks 037Z]
theorem of_forall_isNormalRing_tensorProduct_finitePurelyInseparable
    (h : ∀ (k' : Type (max u v)) [Field k'] [Algebra k k']
      [FiniteDimensional k k'] [IsPurelyInseparable k k'],
      IsNormalRing (k' ⊗[k] A)) :
    IsGeometricallyNormal k A := sorry

/-- Geometric normality is equivalent to the finite purely inseparable field
test. -/
@[stacks 037Z]
theorem iff_forall_isNormalRing_tensorProduct_finitePurelyInseparable :
    IsGeometricallyNormal k A ↔
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k']
        [FiniteDimensional k k'] [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] A) := sorry

/-- The essentially finite type field test is an intrinsic criterion for
geometric normality. -/
@[stacks 037Z]
theorem iff_forall_isNormalRing_tensorProduct_essFiniteType :
    IsGeometricallyNormal k A ↔
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k']
        [Algebra.EssFiniteType k k'],
        IsNormalRing (k' ⊗[k] A) := sorry

/-- The perfect closure of an algebraic closure is a single-field criterion
for geometric normality. -/
@[stacks 037Z]
theorem iff_isNormalRing_tensorProduct_perfectClosure :
    IsGeometricallyNormal k A ↔
      IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A) := sorry

/-- A geometrically normal algebra stays normal after tensoring with a field
extension in any universe.  The bounded universe in the class definition is
only a test universe. -/
@[stacks 037Z "arbitrary-universe field tensor consequence"]
theorem tensorProduct_isNormalRing
    {K : Type w} [Field K] [Algebra k K]
    (hA : IsGeometricallyNormal k A) :
    IsNormalRing (K ⊗[k] A) := sorry

end Algebra.IsGeometricallyNormal
