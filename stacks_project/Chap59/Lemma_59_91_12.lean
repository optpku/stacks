module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.DerivedProper
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf

noncomputable section

universe u

/- Lemma 59.91.12: for a proper morphism of schemes and any cartesian base-change
square, the canonical map `g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism for every
bounded-below complex of abelian étale sheaves with torsion cohomology sheaves. -/
@[stacks 0DDE] #check
  (AlgebraicGeometry.Scheme.Hom.derivedBaseChange_isIso_of_isProper :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMapOfCommSq
      f g f' g' h_cart.toCommSq (DerivedCategory.Plus.ι.obj E)))

#check
  (AlgebraicGeometry.Scheme.Hom.derivedBaseChange_isIso_of_isProper_pullback :
    ∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y)
    [HasPullback g f]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMapOfCommSq
      f g (pullback.fst g f) (pullback.snd g f)
      (IsPullback.of_hasPullback g f).flip.toCommSq (DerivedCategory.Plus.ι.obj E)))

end

end
