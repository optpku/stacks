/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Object
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage

/-!
# Étale-local existence of smooth lifts along thickenings

A smooth morphism from an algebraic space to an algebraic stack admits,
étale-locally on its source, smooth cartesian lifts across a thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- A smooth morphism `x : W.toGroupoids ⟶ X` from an algebraic space admits
an étale covering by smooth cartesian lifts along any thickening `iX : X ⟶ X'`
of algebraic stacks. -/
@[stacks 0CJV]
theorem exists_etaleCovering {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    ∃ (ι : Type u) (ξ : ι → Object iX x),
      AlgebraicSpace.EtaleCovering (fun i ↦ Over.mk (ξ i |>.a)) := sorry

/-- A smooth morphism from an algebraic space admits a family of cartesian lifts
along a thickening of algebraic stacks whose maps to the original space are
étale and jointly surjective on points, and whose maps to the thickened stack
are smooth. -/
theorem exists_etaleCovering_spec {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    ∃ (ι : Type u) (ξ : ι → Object iX x),
      (∀ i, AlgebraicSpace.Etale (ξ i).a) ∧
        (∀ i, Groupoids.Hom.Smooth (ξ i).x') ∧
        (∀ i, Bicategory.PseudoPullbackCone.IsBilimit (ξ i).cone) ∧
        (⋃ i, Set.range (AlgebraicSpace.Points.map (ξ i).a)) = Set.univ := sorry

end AlgebraicGeometry.AlgebraicStack.Lift
