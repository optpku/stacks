/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.CommonRefinement
public import ReasLib.CategoryTheory.Pro.Sequential.Functoriality

/-!
# Functoriality of common refinement

Postcomposition of explicit sequential representatives preserves their common-refinement relation.
This bridge is separate from representative functoriality so consumers of `SequentialHom.map` do
not need the quotient presentation layer.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD

namespace CategoryTheory.Pro.SequentialHom.Equivalent

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {X Y : ℕᵒᵖ ⥤ C}

/-- Common-refinement equivalence of sequential representatives is preserved by postcomposition. -/
theorem map {r s : Pro.SequentialHom X Y} (h : Equivalent r s) (F : C ⥤ D) :
    Equivalent (r.map F) (s.map F) := sorry

end CategoryTheory.Pro.SequentialHom.Equivalent
