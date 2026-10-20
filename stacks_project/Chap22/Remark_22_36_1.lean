/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.KProjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (P : DifferentialGradedCategory.K R
  (DifferentialGradedModule.{u, v} A))

/-!
# Remark 22.36.1 (09R0)

For right modules over a differential graded algebra, the full subcategory defined by bijectivity
of outgoing Hom sets under `Derived.Q` is the intrinsic K-projective object property.  Its
triangulated and retract closure is inherited from the reusable orthogonal API.
-/

@[stacks 09R0] #check
  (DifferentialGradedModule.Homotopy.kProjective_iff_q_map_bijective A P :
    DifferentialGradedModule.Homotopy.kProjective A P ↔
      ∀ M : DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A),
        Function.Bijective
          ((DifferentialGradedModule.Derived.Q A).map :
            (P ⟶ M) →
              ((DifferentialGradedModule.Derived.Q A).obj P ⟶
                (DifferentialGradedModule.Derived.Q A).obj M)))
#check @DifferentialGradedModule.Homotopy.kProjective
#check @DifferentialGradedModule.Homotopy.kProjective_iff
#check @DifferentialGradedModule.Homotopy.KProjective.subcategory
#check @DifferentialGradedModule.IsKProjective
