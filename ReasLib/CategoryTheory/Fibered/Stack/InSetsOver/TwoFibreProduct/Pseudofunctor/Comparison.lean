/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Pseudofunctor.Action
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Forgetful
public import ReasLib.CategoryTheory.Fibered.Sets.TwoFibreProduct.Pseudofunctor.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison API for set-stack two-fibre products

This leaf records complete setoid and neutral set-fibred factorizations. These pseudofunctor
equalities transport identity and composition comparisons together with their endpoints.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.TwoFibreProduct

/-- Forgetting the discrete-fibration condition recovers the complete ambient
setoid-stack pseudofunctor. -/
@[stacks 0434 "set-stack two-fibre-product forgetful factorization"]
theorem pseudofunctor.comp_forget :
    (pseudofunctor J).comp
        (StackOver.Sets.forget J).toPseudofunctor =
      ambientPseudofunctor J := sorry

/-- Forgetting to set-fibred categories commutes with componentwise cospan mapping and the
neutral two-fibre-product pseudofunctor. -/
@[stacks 0434 "set-stack two-fibre-product neutral factorization"]
theorem pseudofunctor.comp_toSets :
    (pseudofunctor J).comp
        (StackOver.Sets.toSets.pseudofunctor J).toPseudofunctor =
      (Bicategory.Cospan.map
          (StackOver.Sets.toSets.pseudofunctor J).toPseudofunctor).comp
        (FiberedCategoryOver.Sets.TwoFibreProduct.pseudofunctor C) := sorry

end StackOver.Sets.TwoFibreProduct

end CategoryTheory
