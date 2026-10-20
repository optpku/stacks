/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Iso.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of Invertible Presentation Maps

An isomorphism of sequential diagrams induces an invertible map between any explicit
telescope presentations.  This leaf also installs the canonical typeclass bridge from an
isomorphism-valued diagram map to invertibility of the object map of a fixed
`Presentation.Hom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The object map of a presentation morphism over an isomorphism-valued diagram morphism is
canonically available to typeclass search as an isomorphism. -/
@[stacks 0CRH "invertibility of a homotopy-colimit presentation map"]
instance Presentation.Hom.homIsIso {S T : ℕ ⥤ D} {α : S ⟶ T} [IsIso α]
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y}
    (φ : Presentation.Hom α P Q) : IsIso φ.hom := sorry

/-- Any two telescope presentations over an isomorphism-valued diagram morphism admit an
invertible compatible presentation map. -/
@[stacks 0CRH "existence of an invertible presentation map"]
theorem Presentation.nonemptyHomWithIso {S T : ℕ ⥤ D} (α : S ⟶ T) [IsIso α]
    {X Y : D} (P : Presentation S X) (Q : Presentation T Y) :
    Nonempty (Presentation.HomWithIso α P Q) := sorry

end CategoryTheory.HomotopyColimit
