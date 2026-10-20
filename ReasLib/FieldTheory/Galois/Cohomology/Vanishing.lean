/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Galois.Cohomology.Coefficients
public import ReasLib.FieldTheory.Galois.Cohomology.Units
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Action ModuleCat

universe u

namespace GaloisCohomology

variable (K Ksep : Type u) [Field K] [Field Ksep]
  [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The first derived-invariants cohomology of separable-closure units vanishes. -/
theorem hilbert90 :
    IsZero ((DiscreteModuleCat.derivedCohomologyFunctor ℤ (Gal(Ksep / K)) 1).obj
      (unitsModule K Ksep)) := sorry

/-- Positive-degree derived-invariants cohomology of the additive separable closure vanishes. -/
theorem additiveCohomologyIsZero (i : ℕ) (hi : 0 < i) :
    IsZero ((DiscreteModuleCat.derivedCohomologyFunctor ℤ (Gal(Ksep / K)) i).obj
      (additiveModule K Ksep)) := sorry

end GaloisCohomology
