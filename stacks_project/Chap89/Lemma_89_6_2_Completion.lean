module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import stacks_project.Chap89.Lemma_89_6_1_BaseChange

/-!
# Closed fibre of base change to the maximal-ideal completion

A point of `Y = X ×_{Spec(A)} Spec(A^∧)` lies in the closed fibre when its image
in `Spec(A^∧)` is the closed point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionBaseChange

/-- A point of `Y = completionBaseChange A X` lies in the closed fibre when its
image in `Spec(A^∧)` is the closed point. -/
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

end AlgebraicGeometry.AlgebraicSpace
