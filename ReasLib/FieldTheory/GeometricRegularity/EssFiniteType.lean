/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.GeometricRegularity

/-!
# Essentially Finite Type Tests for Geometric Regularity

This leaf gives the field-extension criterion for geometric regularity.  It is
owned by `Algebra.IsGeometricallyRegular`, rather than by the first chapter
that uses the criterion.

@stack 0381
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.IsGeometricallyRegular

universe u v

/-- Lemma 10.166.1, tag `0381`: a field algebra is geometrically regular if and only if its
tensor product with every essentially finite type field extension is a regular ring. -/
@[stacks 0381 "essentially finite type field-extension criterion"]
theorem iff_forall_essFiniteType_tensorProduct_isRegularRing
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] :
    IsGeometricallyRegular k A ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
        IsRegularRing (K ⊗[k] A) := sorry

/-- Lemma 10.166.1, tag `0381`: the essentially-finite-type field-extension test is equivalent
to the defining finite purely inseparable field-extension test. -/
@[stacks 0381 "equivalent geometric-regularity field tests"]
theorem forall_essFiniteType_tensorProduct_isRegularRing_iff_forall_finite_purelyInseparable
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] :
    (∀ (K : Type (max u v)) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
      IsRegularRing (K ⊗[k] A)) ↔
      (∀ (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
        [IsPurelyInseparable k K], IsRegularRing (K ⊗[k] A)) := sorry

end Algebra.IsGeometricallyRegular
