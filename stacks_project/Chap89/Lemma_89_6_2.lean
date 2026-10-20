module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular.Completion
import StacksCheckRecall

/-!
# Lemma 89.6.2

Regularity of henselian local rings, and global regularity, after base change
to the maximal-ideal completion of a Noetherian local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open SchemeRealization (toBase)

/- Lemma 89.6.2 (1): For a Noetherian local ring `A` and a decent algebraic space `X`
locally of finite type over `Spec(A)`, with `Y = completionBaseChange A X`, regularity of
`henselianLocalRing Y y` implies regularity of `henselianLocalRing X x` at the image
point `x`. -/
@[stacks 0BHQ] #check
  (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.isRegular_of_completionBaseChange :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : AlgebraicSpace (Spec (.of A)))
    [IsDecent X] [LocallyOfFiniteType (toBase X)]
    (y : Points (completionBaseChange A X)),
    IsRegularLocalRing (henselianLocalRing (completionBaseChange A X) y) →
      IsRegularLocalRing
        (henselianLocalRing X (Points.map (completionBaseChange.fst A X) y)))

/- Lemma 89.6.2 (2): In the same setting, if `y` lies in the closed fibre, then
`henselianLocalRing Y y` is regular if and only if `henselianLocalRing X x` is
regular. -/
@[stacks 0BHQ] #check
  (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.isRegular_iff_completionBaseChange_of_closedFiber :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : AlgebraicSpace (Spec (.of A)))
    [IsDecent X] [LocallyOfFiniteType (toBase X)]
    (y : Points (completionBaseChange A X))
    (hy : completionBaseChange.memClosedFiber y),
    IsRegularLocalRing (henselianLocalRing (completionBaseChange A X) y) ↔
      IsRegularLocalRing
        (henselianLocalRing X (Points.map (completionBaseChange.fst A X) y)))

/- Lemma 89.6.2 (3): If in addition `X` is proper over `A`, then `X` is regular if and
only if `Y = completionBaseChange A X` is regular. -/
@[stacks 0BHQ] #check
  (AlgebraicGeometry.AlgebraicSpace.isRegular_iff_completionBaseChange_of_proper :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : AlgebraicSpace (Spec (.of A))) [IsDecent X] [Proper (toBase X)],
    IsRegular X ↔ IsRegular (completionBaseChange A X))

end AlgebraicGeometry.AlgebraicSpace
