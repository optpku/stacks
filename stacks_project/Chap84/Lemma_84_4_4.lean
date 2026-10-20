module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ProperBaseChange

@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn
noncomputable section
universe u

/- Lemma 84.4.4 -/
@[stacks 0DG0] #check
  (AlgebraicGeometry.AlgebraicSpace.proper_baseChange_isIso :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
      (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
      (h_cart : IsPullback g' f' f g)
      (F : Sheaf (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) (Type (u + 1))) [AlgebraicGeometry.AlgebraicSpace.Proper f],
      IsIso (AlgebraicGeometry.AlgebraicSpace.smallEtaleBaseChangeHom f g f' g' h_cart F))
