/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Sheaf

/-!
# Invariance of ph sheaves under thickenings

Sheaves on the big ph site send thickenings to bijections on sections.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.Ph.Sheaf

/-- A sheaf on the big ph site sends a thickening contravariantly to a bijection
on sections. -/
theorem map_bijective_of_isThickening {S : Scheme.{u}}
    (𝓕 : CategoryTheory.Sheaf (Scheme.bigPhSite S) (Type v)) {X X' : Over S}
    (f : X ⟶ X') [IsThickening f.left] :
    Function.Bijective (𝓕.obj.map f.op) := sorry

end AlgebraicGeometry.Scheme.Ph.Sheaf
