/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsClosedImmersion

/-- A scheme morphism factors through a closed immersion exactly when the kernel ideal sheaf
of the closed immersion is contained in the kernel ideal sheaf of the morphism. -/
theorem exists_lift_iff_ker_le {X Y Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : Y ⟶ X) : (∃ g : Y ⟶ Z, g ≫ i = f) ↔ i.ker ≤ f.ker := sorry

/-- A factor of a closed immersion through a closed immersion is a closed immersion. -/
theorem of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    [IsClosedImmersion g] [IsClosedImmersion h] : f ≫ g = h → IsClosedImmersion f := sorry

/-- Two closed immersions into the same scheme are isomorphic over that scheme exactly when
their kernel ideal sheaves are equal. -/
theorem overIso_iff_ker_eq {X Y Z : Scheme.{u}} (i : Y ⟶ X) (i' : Z ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i'] :
    Nonempty (Over.mk i ≅ Over.mk i') ↔ i.ker = i'.ker := sorry

end AlgebraicGeometry.IsClosedImmersion
