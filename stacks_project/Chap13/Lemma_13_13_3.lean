/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Complex.FiniteHomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open scoped CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-
Lemma `13.13.3` is a canonical recall of the three named homological functors owned by
`ReasLib.CategoryTheory.Filtration.Complex.FiniteHomology`.  No chosen derived category is needed
for these homotopy-level statements.
-/

/- Lemma 13.13.3 (1): degree-zero homology after finite associated graded is homological. -/
@[stacks 05S0] #check
  (inferInstance :
    (FilteredObject.Finite.AssociatedGraded.Homology.zero 𝒜).IsHomological)

/- Lemma 13.13.3 (2): degree-zero homology of every finite associated-graded piece is
homological. -/
@[stacks 05S0] #check
  (fun p : ℤ ↦
    (inferInstance :
      (FilteredObject.Finite.GradedPiece.Homology.zero 𝒜 p).IsHomological))

/- Lemma 13.13.3 (3): degree-zero homology after forgetting a finite filtration is
homological. -/
@[stacks 05S0] #check
  (inferInstance :
    (FilteredObject.Finite.Forget.Homology.zero 𝒜).IsHomological)

end CategoryTheory
