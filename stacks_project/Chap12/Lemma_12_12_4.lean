/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Effaceable
import StacksCheckRecall

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (F : CohomologicalDeltaFunctor A B)
variable (hF : ∀ n : ℕ, n > 0 → ∀ X : A,
  ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F.F n).obj.map u = 0)

/- Lemma 12.12.4 [010T]: effaceability in every positive degree implies universality of the
cohomological delta functor. -/
@[stacks 010T]
#check (isUniversal_of_effaceable F hF : F.IsUniversal)

end CategoryTheory.CohomologicalDeltaFunctor
