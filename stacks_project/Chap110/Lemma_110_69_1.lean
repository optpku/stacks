/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Compact.NonRepresentable
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedModule.Derived

/- Lemma 110.69.1: there exists a cochain DG algebra `(A, d)` and a compact
object `E` of `D(A, d)` that is not isomorphic in `D(A, d)` to the image of any
finite graded-projective DG `A`-module. -/
@[stacks 09R5] #check (DifferentialGradedModule.Derived.exists_compactObject_not_iso_finiteGradedProjective :
    ∃ (R : Type u) (_ : CommRing R) (A : CochainDGAlgebra.{u, v} R)
      (E : Category.{u, v} A),
      IsCompactObject E ∧
        ¬ ∃ (P : DifferentialGradedModule.{u, v} A),
            IsFiniteGradedProjective A P ∧
              Nonempty ((fromModules A).obj P ≅ E))

end DifferentialGradedModule.Derived
