/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Situation

@[expose] public section

/-!
# Source-facing compatibility for localized Chern classes

This file retains the established source-facing name for the complement of a closed center.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The open subscheme complementary to the image of a closed immersion. -/
abbrev openComplement {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : X.Opens :=
  closedImmersionComplement i

end AlgebraicGeometry.LocalizedChern
