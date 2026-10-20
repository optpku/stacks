module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.ProperBaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry.AlgebraicSpace

universe u v

section

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `smallEtaleDerivedBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Theorem 84.4.6. For a cartesian square of algebraic spaces with proper vertical map,
canonical derived base change is invertible on every locally torsion abelian étale sheaf. -/
@[stacks 0DG2] #check (AlgebraicGeometry.AlgebraicSpace.proper_derivedBaseChange_isIso :
  ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h_cart : IsPullback g' f' f g)
  [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
  [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
  [(smallEtaleInclusion Y').IsCoverDense (spacesEtaleTopology Y')]
  [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
  [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
  [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
  [Abelian (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
  [Abelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
  [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
  [(sheafPushforwardAbelian f).Additive]
  [(sheafPushforwardAbelian f').Additive]
  [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
  [(sheafPushforwardAbelian f').toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}))]
  [(sheafInverseImage AddCommGrpCat.{u + 1} g).Additive]
  [(sheafInverseImage AddCommGrpCat.{u + 1} g').Additive]
  (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
  [Proper f], IsLocallyTorsion F →
    IsIso
      (smallEtaleDerivedBaseChangeHom f g f' g' h_cart
        ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) 0).obj F)))

end
