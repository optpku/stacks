/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.FinitePointSequence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RegularAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage

/-!
# Domination of proper modifications by sequences of point blowups
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper morphism to a Noetherian algebraic space that is an isomorphism away from
finitely many regular closed points of local dimension two is dominated by a finite
sequence of closed-point blowups whose centers lie over those points. -/
@[stacks 0BHH]
theorem exists_pointBlowupSequence_lift {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian X] (T : Set (Points X)) (hT_finite : T.Finite)
    (hT_closed : T ⊆ closedPoints (Points X))
    (hT_regular : ∀ x, x ∈ T → RegularAt X x)
    (hT_dimension : ∀ x, x ∈ T → localRingDimAt x = 2)
    (U : OpenSubspace X) (hU : U.pointsSet = Tᶜ) (f : Y ⟶ X) [Proper f]
    (h_iso : IsIso (restrictTo f U)) :
    ∃ (Xn : AlgebraicSpace S) (s : PointBlowupSequence X Xn) (g : Xn ⟶ Y),
      s.EveryCenterOver T ∧ g ≫ f = s.toSource :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
