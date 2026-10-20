/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Precoverage.Tautological

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Remark 7.48.3 (00ZE): an enlargement of a precoverage that adds only
tautologically equivalent covering families generates the same Grothendieck
topology.  The reusable statement is intentionally formulated for arbitrary
precoverages, rather than only for a coverage presentation. -/
@[stacks 00ZE] #check @Precoverage.toGrothendieck_eq_of_le_of_tautological_covers

end CategoryTheory
