/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BaseChange.Completion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Completion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Regular.Completion

/-!
# Regularity of algebraic spaces after base change to completion

Regularity of henselian local rings descends along base change to the
maximal-ideal completion of a Noetherian local ring, and is equivalent on the
closed fibre. For proper decent algebraic spaces, global regularity is equivalent
before and after this base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open SchemeRealization (toBase)

namespace completionBaseChange

/-- A point of `completionBaseChange A X` lies in the closed fibre when its image
in `Spec(A^∧)` is the closed point. -/
def memClosedFiber {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : AlgebraicSpace (Spec (.of A))} (y : Points (completionBaseChange A X)) :
    Prop :=
  Points.map (snd A X) y =
    ofOver.pointsEquiv (Over.mk (specAdicCompletionSchemeHom A))
      (closedPoint (AdicCompletion (maximalIdeal A) A))

/-- A point of `completionBaseChange A X` lies in the closed fibre if and only if
it lies over the closed point of `Spec(A)`. -/
theorem memClosedFiber_iff_base_eq_closedPoint
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : AlgebraicSpace (Spec (.of A))} (y : Points (completionBaseChange A X)) :
    memClosedFiber y ↔ Points.base y = closedPoint A :=
  sorry

end completionBaseChange

/-- For a decent algebraic space locally of finite type over a Noetherian local
ring, regularity of a henselian local ring after base change to the maximal-ideal
completion implies regularity of the henselian local ring at its image. -/
@[stacks 0BHQ]
theorem henselianLocalRing.isRegular_of_completionBaseChange
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : AlgebraicSpace (Spec (.of A)))
    [IsDecent X] [LocallyOfFiniteType (toBase X)]
    (y : Points (completionBaseChange A X)) :
    IsRegularLocalRing (henselianLocalRing (completionBaseChange A X) y) →
      IsRegularLocalRing
        (henselianLocalRing X (Points.map (completionBaseChange.fst A X) y)) :=
  sorry

/-- For a decent algebraic space locally of finite type over a Noetherian local
ring, henselian local rings at a point in the closed fibre of the completion base
change and at its image are regular simultaneously. -/
@[stacks 0BHQ]
theorem henselianLocalRing.isRegular_iff_completionBaseChange_of_closedFiber
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : AlgebraicSpace (Spec (.of A)))
    [IsDecent X] [LocallyOfFiniteType (toBase X)]
    (y : Points (completionBaseChange A X))
    (hy : completionBaseChange.memClosedFiber y) :
    IsRegularLocalRing (henselianLocalRing (completionBaseChange A X) y) ↔
      IsRegularLocalRing
        (henselianLocalRing X (Points.map (completionBaseChange.fst A X) y)) :=
  sorry

/-- A proper decent algebraic space over a Noetherian local ring is regular if
and only if its base change to the maximal-ideal completion is regular. -/
@[stacks 0BHQ]
theorem isRegular_iff_completionBaseChange_of_proper
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : AlgebraicSpace (Spec (.of A))) [IsDecent X] [Proper (toBase X)] :
    IsRegular X ↔ IsRegular (completionBaseChange A X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
