/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative

/-!
# Cancellation for relative ampleness

This file records when relative ampleness over a composite morphism descends to the first
morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A module relatively ample over a composite is relatively ample over its first morphism
when that morphism is quasi-compact. -/
theorem RelativelyAmple.of_comp {X Y S : Scheme.{u}} {L : X.Modules}
    (f : X ⟶ Y) (g : Y ⟶ S) [QuasiCompact f]
    (hL : RelativelyAmple (f ≫ g) L) : RelativelyAmple f L := sorry

end AlgebraicGeometry
