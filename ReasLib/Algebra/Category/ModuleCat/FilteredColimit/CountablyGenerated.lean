/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.CountablyGenerated.Operations
public import ReasLib.CategoryTheory.Functor.TailFactorization
public import ReasLib.CategoryTheory.Limits.Presentation

/-!
# Countably generated filtered colimits

The countable-subpresentation theorem belongs to tail factorization of a module diagram; the
Mittag-Leffler property is one important way of obtaining that categorical hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Functor.HasTailFactorization

variable {R : Type u} [Ring R]
variable {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {F : I ⥤ ModuleCat.{v} R} [HasColimit F]

/-- A tail-factorizing module diagram with countably generated colimit has a countable directed
subsystem with the same colimit. -/
@[stacks 059W "tail factorization"]
theorem exists_countable_subpresentation (hF : F.HasTailFactorization)
    (hcg : Module.CountablyGenerated R
      (colimit F : ModuleCat.{v} R)) :
    ∃ (S : Set I) (_ : Countable S) (_ : Nonempty S) (_ : IsDirectedOrder S),
      (ColimitPresentation.colimit F).IsColimitRestriction S := sorry

end CategoryTheory.Functor.HasTailFactorization
