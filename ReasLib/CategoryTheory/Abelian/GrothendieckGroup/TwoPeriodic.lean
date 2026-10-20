/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Additivity
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Grothendieck Classes of Two-Periodic Homology

The two homology objects of a two-periodic endomorphism complex have equal classes in the
Grothendieck group.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The degree-`0` and degree-`1` homology objects of a two-periodic endomorphism have equal
Grothendieck classes. -/
@[stacks 02MX]
theorem k0_homology_zero_eq_one (K : TwoPeriodicEndomorphism A) :
    K₀[K.toCochainComplex.homology 0] =
      K₀[K.toCochainComplex.homology 1] := sorry

end CategoryTheory.TwoPeriodicEndomorphism
