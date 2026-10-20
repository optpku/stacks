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
variable (hA : A.IsBounded)
variable (E : DifferentialGradedModule.Derived.Category.{u, v} A)

/-!
# Lemma 22.36.6 (09RB)

For a bounded DGA, compact derived objects are precisely the essential image of finite graded
K-projective DG-modules.
-/

@[stacks 09RB] #check
  (DifferentialGradedModule.Derived.FiniteKProjective.isCompactObject_iff A hA E :
    IsCompactObject E ↔
      (DifferentialGradedModule.finiteKProjective A).map
        (DifferentialGradedModule.Derived.fromModules A) E)
#check @DifferentialGradedModule.Derived.FiniteKProjective.isCompactObject_iff_exists
#check @DifferentialGradedModule.finiteKProjective
#check @DifferentialGradedModule.Derived.FiniteKProjective.isCompactObject
#check @DifferentialGradedModule.finiteKProjective_iff_q_map_bijective
#check @DifferentialGradedModule.isKProjective_iff_q_map_bijective
#check @CochainDGAlgebra.IsBounded
#check @CochainDGAlgebra.IsBounded.exists_bounds
#check @DifferentialGradedModule.Homotopy.kProjective_iff_q_map_bijective
