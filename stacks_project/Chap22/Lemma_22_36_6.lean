/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Compact.KProjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (E : DifferentialGradedModule.Derived.Category.{u, v} A)

/-!
# Correction to Lemma 22.36.6 (09RB), using Proposition 22.36.4 (09R3)

For any DGA, compact derived objects are precisely the retract closure of the essential image
of finite graded K-projective DG-modules.  This is the general finite-cell retract criterion
of 09R3.  The bounded-only representative converse stated in 09RB is false: the example of
09R5 is bounded in degrees [-1, 0] and has a compact object with no finite graded projective
representative.  Thus 09RB is recorded here as a source error, not as a valid representative
theorem.  Actual DG-module retract stability does not split arbitrary derived retracts.
-/

@[stacks 09R3 "replacement for the false bounded converse of 09RB"] #check
  (DifferentialGradedModule.Derived.FiniteKProjective.isCompactObject_iff A E :
    IsCompactObject E ↔
      ((DifferentialGradedModule.finiteKProjective A).map
        (DifferentialGradedModule.Derived.fromModules A)).retractClosure E)
#check @DifferentialGradedModule.Derived.FiniteKProjective.isCompactObject_iff_exists
#check @DifferentialGradedModule.finiteKProjective
#check @DifferentialGradedModule.Derived.FiniteKProjective.isCompactObject
#check @DifferentialGradedModule.finiteKProjective_iff_q_map_bijective
#check @DifferentialGradedModule.isKProjective_iff_q_map_bijective
#check @CochainDGAlgebra.IsBounded
#check @CochainDGAlgebra.IsBounded.exists_bounds
#check @DifferentialGradedModule.Homotopy.kProjective_iff_q_map_bijective
