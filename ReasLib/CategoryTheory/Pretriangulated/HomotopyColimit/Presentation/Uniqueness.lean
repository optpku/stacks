/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Iso.Definition
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Iso.Existence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Uniqueness of Telescope Presentations

Homotopy-colimit objects are unique up to isomorphism.  The presentation-level API retains
compatibility with an arbitrary isomorphism of sequential diagrams and every canonical stage
map, without selecting a public comparison isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Presentations over isomorphic sequential diagrams admit a compatible presentation
isomorphism. -/
@[stacks 0CRH "uniqueness of a homotopy-colimit presentation"]
theorem Presentation.nonemptyIso {S T : ℕ ⥤ D} (e : S ≅ T)
    {X Y : D} (P : Presentation S X) (Q : Presentation T Y) :
    Nonempty (Presentation.Iso e P Q) := sorry

namespace IsOf

/-- Homotopy-colimit objects of isomorphic sequential diagrams are nonemptily isomorphic. -/
@[stacks 0CRH "uniqueness across isomorphic sequential diagrams"]
theorem nonemptyIsoOfDiagramIso {S T : ℕ ⥤ D} (e : S ≅ T) {X Y : D}
    (hX : HomotopyColimit.IsOf S X) (hY : HomotopyColimit.IsOf T Y) :
    Nonempty (X ≅ Y) := sorry

/-- Any two homotopy-colimit objects of the same sequential diagram are nonemptily
isomorphic. -/
@[stacks 0CRH "uniqueness of a sequential homotopy colimit"]
theorem nonemptyIso {K : ℕ ⥤ D} {X Y : D}
    (hX : HomotopyColimit.IsOf K X) (hY : HomotopyColimit.IsOf K Y) :
    Nonempty (X ≅ Y) := sorry

end IsOf

end CategoryTheory.HomotopyColimit
