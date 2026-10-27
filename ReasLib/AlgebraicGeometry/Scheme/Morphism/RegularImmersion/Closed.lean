/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsRegularClosedImmersion

/-- Every regular closed immersion is a regular immersion. -/
instance toIsRegularImmersion {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsRegularClosedImmersion i] : IsRegularImmersion i := sorry

end AlgebraicGeometry.IsRegularClosedImmersion
