/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Covering
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cofinal families of covers

This leaf records the refinement direction used by local-to-global arguments: every covering
`S` admits a selected covering `T` together with a morphism `T ⟶ S`.  Keeping this predicate at the
site-family level avoids repeating the same quantifier package in unrelated cohomology APIs.
-/

open CategoryTheory

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- A set of covers is cofinal when every cover admits a selected refinement. -/
@[stacks 0D6M "cofinal family of covering objects"]
def cofinalCoverFamily
    (J : GrothendieckTopology C) (V : C)
    (Cov : Set (J.Cover V)) : Prop :=
  ∀ S : J.Cover V, ∃ T : J.Cover V, T ∈ Cov ∧ Nonempty (T ⟶ S)

end CategoryTheory.GrothendieckTopology

end
