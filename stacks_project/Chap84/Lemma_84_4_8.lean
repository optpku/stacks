module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Cohomology.ProperStalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open GeometricPoint

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` / `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `smallEtaleDerivedBaseChangeHom` and right-derived comparisons.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
variable (f : X ⟶ Y) (ybar : GeometricPoint Y)
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
variable [(smallEtaleInclusion (ofOver ybar.overObj)).IsCoverDense
    (spacesEtaleTopology (ofOver ybar.overObj))]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2}
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2}
    (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [(sheafPushforwardAbelian f).Additive]
variable [(sheafPushforwardAbelian (geometricFiberToPoint f ybar)).Additive]
variable [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian (geometricFiberToPoint f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}))]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y)).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y)).PreservesHomology]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).PreservesHomology]
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{u + 1}]
variable [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u + 1} AddCommGrpCat.{u + 1}]
variable [InitiallySmall.{u + 1}
    ((etaleBaseChange (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y) ⋙
        (toSpacesEtalePoint (idGeometricPoint ybar)).fiber).Elements)]
variable [((etaleBaseChange (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology Y) (spacesEtaleTopology (ofOver ybar.overObj))).IsRightAdjoint]
variable [(globalSections (ofOver ybar.overObj)).Additive]
variable [(globalSections (ofOver ybar.overObj)).PreservesHomology]
variable [(globalSections (geometricFiber f ybar)).Additive]
variable [(sheafPushforwardAbelian (geometricFiberToPoint f ybar) ⋙
    globalSections (ofOver ybar.overObj)).Additive]
variable [(globalSections (geometricFiber f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}))]
variable [((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
    Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1}).Additive]
variable [((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
    Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1}).PreservesHomology]
variable [PreservesFiniteLimits
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
      Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
        AddCommGrpCat.{u + 1})]
variable [PreservesFiniteColimits
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
      Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
        AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [EnoughInjectives
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [EnoughInjectives
    (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]

/- Lemma 84.4.8. Stalks of higher direct images of locally torsion abelian sheaves
along proper morphisms identify with étale cohomology of the geometric fibre,
with coefficients given by geometric inverse image. -/
@[stacks 0DG4] #check
  (AlgebraicGeometry.AlgebraicSpace.higherDirectImage_stalk_eq_geometricFiberCohomology f ybar :
    ∀ [Proper f] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
      IsLocallyTorsion F → ∀ (n : ℕ),
        IsIso (higherDirectImageStalkToGeometricFiberCohomology f ybar F n))

/- The bounded-below conclusion holds in every integer degree for coefficients
with locally torsion cohomology sheaves. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.derivedHigherDirectImage_stalk_eq_geometricFiberCohomology f ybar :
    ∀ [Proper f] (E : DerivedCategory.Plus
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
      DerivedCategory.Plus.cohomologyIn
        (IsLocallyTorsion :
          ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E →
      ∀ (n : ℤ),
        IsIso (derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar E n))

end AlgebraicGeometry.AlgebraicSpace
