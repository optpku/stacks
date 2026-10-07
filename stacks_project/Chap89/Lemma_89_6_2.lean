module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import stacks_project.Chap66.Lemma_66_25_4_Regular
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import stacks_project.Chap68.Lemma_68_17_7
public import stacks_project.Chap89.Lemma_89_6_1_BaseChange
public import stacks_project.Chap89.Lemma_89_6_2_Completion

/-!
# Lemma 89.6.2

Regularity of henselian local rings, and global regularity, after base change
to the maximal-ideal completion of a Noetherian local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 89.6.2 (1): For a Noetherian local ring `A` and a decent algebraic space `X`
locally of finite type over `Spec(A)`, with `Y = completionBaseChange A X`, regularity of
`henselianLocalRing Y y` implies regularity of `henselianLocalRing X x` at the image
point `x`. -/
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

/-- Lemma 89.6.2 (2): In the same setting, if `y` lies in the closed fibre, then
`henselianLocalRing Y y` is regular if and only if `henselianLocalRing X x` is
regular. -/
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

/-- Lemma 89.6.2 (3): If in addition `X` is proper over `A`, then `X` is regular if and
only if `Y = completionBaseChange A X` is regular. -/
@[stacks 0BHQ]
theorem isRegular_iff_completionBaseChange_of_proper
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : AlgebraicSpace (Spec (.of A))) [IsDecent X] [Proper (toBase X)] :
    IsRegular X ↔ IsRegular (completionBaseChange A X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
