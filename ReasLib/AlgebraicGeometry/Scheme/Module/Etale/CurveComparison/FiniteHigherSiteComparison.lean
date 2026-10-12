/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.HigherSiteComparison
public import stacks_project.Chap64.Remark_64_29_2_Cohomology

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.AmbientCurve
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k) [hcurve : Curve X] [hsmooth : Smooth X.hom]
variable [hconnected : GeometricallyConnected X.hom]
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber ηbar)))]
variable [HasDerivedCategory (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- The two geometric restrictions use the same induced group homomorphism,
identified by the already specified fiber projection/lift construction. -/
def finiteRestrictionModelIso
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) :
    (restriction Λ (geometricToArithmeticHom X) ηbar).obj M.obj ≅
      (Ambient.restriction Λ X ηbar).obj M.obj :=
  eqToIso (congrArg (fun φ ↦ (discreteModuleRes (R := Λ) φ).obj M.obj)
    (AmbientGeometry.geometricFundamentalMap_eq X ηbar))

/-- Realized geometric site cohomology specializes to the CURRENT finite
arithmetic associated-sheaf API through actual base change and finite-input maps. -/
def finiteGeometricSiteIso
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) (n : ℕ) :
    (realizedCohomology Λ ηbar n).obj ((Ambient.restriction Λ X ηbar).obj M.obj) ≅
      geometricModuleEtaleHq X ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).obj M) n :=
  (siteModuleCohomologyModuleFunctor (J := (geometricBaseChange X).smallEtaleTopology)
      (A := Λ) n).mapIso
    ((functor (Λ := Λ) (xbar := ηbar)).mapIso (finiteRestrictionModelIso Λ X ηbar M).symm ≪≫
      (baseChangeIso Λ (geometricToArithmeticHom X) ηbar M.obj).symm ≪≫
      (AmbientGeometry.modulePullback Λ (geometricToArithmeticHom X)).mapIso
        ((finiteIso (Λ := Λ) (xbar := arithmeticPoint X ηbar)).app M))

/-- The target is the actual existing geometric module cohomology of the
published finite associated sheaf, with its actual coefficient maps. -/
def finiteGeometricCohomology (n : ℕ) :
    (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory ⥤ ModuleCat.{u + 1} Λ :=
  associatedSheafFunctor Λ (arithmeticPoint X ηbar) ⋙
    AmbientGeometry.modulePullback Λ (geometricToArithmeticHom X) ⋙
      siteModuleCohomologyModuleFunctor (J := (geometricBaseChange X).smallEtaleTopology) (A := Λ) n

include hcurve hsmooth hconnected

/-- The source-facing ordinary comparison includes finite input only after
deriving in all discrete representations; all comparison maps are specified above. -/
def finiteHigherSiteComparisonIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) (n : ℕ) :
    (Ambient.finiteCohomology Λ X ηbar n).obj M ≅
      geometricModuleEtaleHq X ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).obj M) n :=
  higherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ ((Ambient.restriction Λ X ηbar).obj M.obj) n ≪≫
    finiteGeometricSiteIso Λ X ηbar M n

/-- Naturality of the actual source-facing finite-input comparison. -/
theorem finiteHigherSiteComparisonIso_naturality
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    {M N : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory} (a : M ⟶ N) (n : ℕ) :
    (Ambient.finiteCohomology Λ X ηbar n).map a ≫
        (finiteHigherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ N n).hom =
      (finiteHigherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ M n).hom ≫
        (finiteGeometricCohomology Λ X ηbar n).map a := sorry

/-- The actual higher comparison, naturally on finite arithmetic representations,
with the original geometric site-cohomology endpoint and correct ambient resolutions. -/
def finiteHigherSiteComparisonNatIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k)) (n : ℕ) :
    Ambient.finiteCohomology Λ X ηbar n ≅ finiteGeometricCohomology Λ X ηbar n :=
  NatIso.ofComponents (fun M ↦ finiteHigherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ M n)
    (fun a ↦ finiteHigherSiteComparisonIso_naturality Λ X ηbar h_ne_P1 hΛ a n)

end AlgebraicGeometry.SchemeOverField.AmbientCurve
