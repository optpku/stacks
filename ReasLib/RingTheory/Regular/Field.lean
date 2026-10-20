/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.GeometricRegularity.Equiv
public import ReasLib.FieldTheory.Separable.Generated
public import ReasLib.RingTheory.Regular.BaseChange
public import ReasLib.RingTheory.Regular.Fiber
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Regular maps from fields

@stack 07BZ
@stack 07EQ

This module relates geometric regularity and separability to the regularity of
the canonical structure map from a field.
-/

namespace RingHom.Regular

universe u v

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- A geometrically regular algebra over a field has a regular structure map. -/
@[stacks 07BZ "geometrically regular field algebra map"]
instance instAlgebraMap [Algebra.IsGeometricallyRegular k A] :
    (algebraMap k A).Regular := sorry

/-- The target of a regular ring map from a field is a regular ring. -/
@[stacks 07BZ "regular target of a regular field map"]
theorem isRegularRing_of_field
    (h : (algebraMap k A).Regular) : IsRegularRing A := sorry

section

variable {K : Type v} [Field K] [Algebra k K]

/-- Lemma 15.41.6: a field extension is regular exactly when it is separable. -/
@[stacks 07EQ "regular field extension iff separable"]
theorem algebraMap_iff_isSeparableOver :
    (algebraMap k K).Regular ↔ Algebra.IsSeparableOver k K := sorry

end

end RingHom.Regular

namespace Algebra.IsGeometricallyRegular

universe u v

/-- A regular structure map from a field is geometrically regular. -/
@[stacks 07BZ "geometric regularity from a regular field algebra map"]
theorem of_regularMap
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (h : (algebraMap k A).Regular) : Algebra.IsGeometricallyRegular k A := sorry

end Algebra.IsGeometricallyRegular
