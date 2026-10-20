/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Transport.Object
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Transport.Diagram
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism-Closed Homotopy-Colimit Properties

This leaf exposes the two currying directions of `HomotopyColimit.IsOf` as standard
`ObjectProperty` APIs. Consequently, downstream arguments can use the generic
`ObjectProperty.prop_of_iso`, `prop_iff_of_iso`, `prop_of_isIso`, and
`prop_iff_of_isIso` interfaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.HomotopyColimit.IsOf

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Sequential diagrams for which `X` is a homotopy colimit, regarded as a property of
objects of the functor category. -/
@[stacks 0CRH]
def diagram (X : D) : ObjectProperty (ℕ ⥤ D) :=
  fun K => HomotopyColimit.IsOf K X

/-- Membership in `IsOf.diagram X` is the homotopy-colimit relation with target `X`. -/
@[simp]
theorem diagram_apply (X : D) (K : ℕ ⥤ D) :
    diagram X K ↔ HomotopyColimit.IsOf K X := sorry

/-- Homotopy-colimit objects of a fixed sequential diagram are closed under isomorphisms. -/
@[stacks 0CRH]
instance isClosedUnderIsomorphisms (K : ℕ ⥤ D) :
    ObjectProperty.IsClosedUnderIsomorphisms (HomotopyColimit.IsOf K) := sorry

/-- Sequential diagrams presenting a fixed homotopy-colimit object are closed under
isomorphisms. -/
@[stacks 0CRH]
instance diagramIsClosedUnderIsomorphisms (X : D) :
    ObjectProperty.IsClosedUnderIsomorphisms (diagram X) := sorry

end CategoryTheory.HomotopyColimit.IsOf
