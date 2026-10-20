/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.IrreducibleCriteria
import StacksCheckRecall

@[expose] public section

/-!
# Affine Field-Extension Criteria for Geometric Irreducibility

Lemma 10.47.3 is a canonical recall.  Its textbook four-way `TFAE` is exposed
as independent affine criteria: the defining arbitrary-field-base-change
criterion, a finite-separable test, a separable-closure test, and an
algebraic-closure test.  ReasLib states the closure tests first for arbitrary
chosen `IsSepClosure` and `IsAlgClosure` objects, with canonical closures as
convenience specializations.

@stack 037K
-/

/- Lemma 10.47.3 (1) (Tag 037K): geometric irreducibility is the condition on
all field-valued affine base changes. -/
@[stacks 037K]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.Spectrum.iff_baseChange

/- Lemma 10.47.3 (2) (Tag 037K): it is enough to test finite separable field
extensions. -/
@[stacks 037K]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.Spectrum.iff_finiteSeparableBaseChange

/- Lemma 10.47.3 (3) (Tag 037K): any separable closure, and in particular the
canonical `SeparableClosure k`, suffices. -/
@[stacks 037K]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.Spectrum.iff_of_isSepClosure
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.Spectrum.iff_separableClosure

/- Lemma 10.47.3 (4) (Tag 037K): any algebraic closure, and in particular the
canonical `AlgebraicClosure k`, suffices. -/
@[stacks 037K]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.Spectrum.iff_of_isAlgClosure
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.Spectrum.iff_algebraicClosure
