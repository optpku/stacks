module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap84.Lemma_84_4_8_Pullback
public import stacks_project.Chap84.Lemma_84_4_8_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.4.8

Stalks of higher direct images along a proper morphism of algebraic spaces identify
with étale cohomology of the geometric fibre.
-/

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
variable [(sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).PreservesHomology]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).PreservesHomology]
variable [(sheafInverseImage AddCommGrpCat.{u + 1}
    (geometricFiberToX f ybar)).PreservesInjectiveObjects]
variable [(smallEtaleInverseExact (geometricFiberToX f ybar)).obj.PreservesInjectiveObjects]
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{u + 1}]
variable [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u + 1} AddCommGrpCat.{u + 1}]
variable [InitiallySmall
    ((etaleBaseChange ybar.hom ⋙
        (toSpacesEtalePoint (idGeometricPoint ybar)).fiber).Elements)]
variable [((etaleBaseChange ybar.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology Y) (spacesEtaleTopology (ofOver ybar.overObj))).IsRightAdjoint]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).PreservesInjectiveObjects]
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

/-- Lemma 84.4.8 (1): if `f : X ⟶ Y` is a proper morphism of algebraic spaces over a
scheme `S` and `ȳ → Y` is a geometric point, then for a torsion abelian sheaf `F` on
`X_étale` the stalk `(R^n f_* F)_ȳ` is canonically isomorphic to étale cohomology
`H^n_étale(X_ȳ, F_ȳ)` of the geometric fibre `X_ȳ = ȳ ×_Y X`, where `F_ȳ` is the
inverse image of `F` to that fibre. -/
@[stacks 0DG4]
theorem higherDirectImage_stalk_eq_geometricFiberCohomology
    [Proper f] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F) (n : ℕ) :
    IsIso (higherDirectImageStalkToGeometricFiberCohomology f ybar F n) :=
  sorry

/-- Lemma 84.4.8 (2): if `f : X ⟶ Y` is a proper morphism of algebraic spaces over a
scheme `S` and `ȳ → Y` is a geometric point, then for `E ∈ D⁺(X_étale)` with torsion
cohomology sheaves the stalk `(R^n f_* E)_ȳ` is canonically isomorphic to étale
cohomology `H^n_étale(X_ȳ, E_ȳ)` of the geometric fibre, where `E_ȳ` is the inverse
image of `E` to `X_ȳ = ȳ ×_Y X`. -/
@[stacks 0DG4]
theorem derivedHigherDirectImage_stalk_eq_geometricFiberCohomology
    [Proper f] (E : DerivedCategory.Plus
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E)
    (n : ℤ) :
    IsIso (derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar E n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
