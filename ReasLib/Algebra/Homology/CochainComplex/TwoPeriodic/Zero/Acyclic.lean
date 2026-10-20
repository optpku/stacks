module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Acyclic Two-Periodic Complexes with One Zero Differential

This file records the acyclicity of a two-periodic complex whose first differential is zero and
whose second differential is an isomorphism.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- A two-periodic complex with zero first differential and invertible second differential is
acyclic. -/
theorem ofZero_acyclic_of_isIso {X : C} (ψ : X ⟶ X) [IsIso ψ] :
    (ofZero ψ).toCochainComplex.Acyclic := sorry

end CategoryTheory.TwoPeriodicEndomorphism
