module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualDerivedComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommFiniteCompactDualInput
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricFiniteModel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommReversedCharacterComplex
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCharacterDegreeComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommSignedSourceTarget

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open NoncommResidualSectionsComparison
noncomputable section
universe u

namespace NoncommGeometricDualCochainComparison
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable [X.left.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules R)]
variable [X.left.smallEtaleTopology.HasSheafCompose (NoncommIntrinsicDualTransport.modules R)]
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [HasWeakSheafify X.left.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U)
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ))]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable (hR : IsUnit (Nat.card R : k))
variable (M : (finiteTypeDiscreteModule R (Γ X η)).FullSubcategory)

abbrev input := NoncommFiniteCompactDualInput.finiteInput R X η hR M

/-- Same finite coefficient as the compact tensor's chosen resolution, then
the actual published associated-sheaf map and intrinsic character/Tate comparison. -/
def sheafIso : (associatedSheafFunctor Rᵐᵒᵖ (arithmeticPoint X η)).obj (input R X η hR M) ≅
    NoncommArithmeticDualSheaf.intrinsic R X η M :=
  (associatedSheafFunctor Rᵐᵒᵖ (arithmeticPoint X η)).mapIso
    (NoncommFiniteCompactDualInput.finiteIso R X η hR M) ≪≫
  (NoncommArithmeticDualSheaf.iso R X η hR M).symm

def resolutionMap := InjectiveResolution.desc (sheafIso R X η hR M).hom
  (injectiveResolution (NoncommArithmeticDualSheaf.intrinsic R X η M))
  (injectiveResolution ((associatedSheafFunctor Rᵐᵒᵖ (arithmeticPoint X η)).obj (input R X η hR M)))

abbrev groupComplex := NoncommResidualDerivedComparison.groupIntegerComplex Rᵐᵒᵖ X η (input R X η hR M)

def residualOrdinary := ((toResidual Rᵐᵒᵖ X η).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (NoncommGeometricFiniteModel.ordinary R X η M)

/-- Actual ambient invariant resolution → geometric intrinsic-dual resolution,
including the coefficient iso and canonical section/extension compositor. -/
def groupToOrdinary : groupComplex R X η hR M ⟶ residualOrdinary R X η M :=
  NoncommResidualDerivedComparison.cochainComparison Rᵐᵒᵖ X η (input R X η hR M) ≫
  HomologicalComplex.extendMap
    (((sheafSections Rᵐᵒᵖ X η).mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionMap R X η hR M))
    ComplexShape.embeddingUpNat ≫
  (ComplexShape.embeddingUpNat.mapAppIso (toResidual Rᵐᵒᵖ X η)
    (((NoncommGeometricSource.discreteSections Rᵐᵒᵖ X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (NoncommArithmeticDualSheaf.intrinsic R X η M)).cocomplex)).inv

variable [hcurve : Curve X] [hsmooth : Smooth X.hom] [hconnected : GeometricallyConnected X.hom]
variable (hne : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))

include hcurve hsmooth hconnected hne in
theorem groupToOrdinary_quasiIso : QuasiIso (groupToOrdinary R X η hR M) := by sorry

def finiteComplex := ((toResidual Rᵐᵒᵖ X η).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (NoncommGeometricFiniteModel.projectiveCochain R X η hR M)

def finiteToOrdinary : finiteComplex R X η hR M ⟶ residualOrdinary R X η M :=
  ((toResidual Rᵐᵒᵖ X η).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (NoncommGeometricFiniteModel.projectiveMap R X η hR M)

theorem finiteToOrdinary_quasiIso : QuasiIso (finiteToOrdinary R X η hR M) := by sorry

variable [HasDerivedCategory (ModuleCat.{u + 1} (NoncommCompletedRing.Obj Rᵐᵒᵖᵐᵒᵖ (Q X η)))]

/-- Dualize the concrete quasi-isomorphism span, including the fixed Hom signs.
This directly relates the finite geometric model to the SAME group resolution
used in the compact tensor endpoint, without an arbitrary derived iso choice. -/
def signedDualIso :
    DerivedCategory.Q.obj (NoncommReversedCharacterComplex.signed Rᵐᵒᵖ (Q X η) (finiteComplex R X η hR M)) ≅
    DerivedCategory.Q.obj (NoncommReversedCharacterComplex.signed Rᵐᵒᵖ (Q X η) (groupComplex R X η hR M)) :=
  -- Local instance justification (proof-local temporary data): the actual finite-model map is a quasi-isomorphism.
  letI := finiteToOrdinary_quasiIso R X η hR M
  -- Local instance justification (proof-local temporary data): the actual group comparison has the stated curve hypotheses.
  letI := groupToOrdinary_quasiIso R X η hR M hne
  (NoncommReversedCharacterComplex.isoOfQuasiIso Rᵐᵒᵖ (Q X η) (finiteToOrdinary R X η hR M)).symm ≪≫
    NoncommReversedCharacterComplex.isoOfQuasiIso Rᵐᵒᵖ (Q X η) (groupToOrdinary R X η hR M)

/-- The concrete group complex is the nonnegative invariant resolution already
used by the compact target, so only the canonical degree-extension comparison remains. -/
def groupDegreeIso :
    NoncommReversedCharacterComplex.signed Rᵐᵒᵖ (Q X η) (groupComplex R X η hR M) ≅
    NoncommSignedSourceTarget.residualCochain R X η hR M :=
  NoncommCharacterDegreeComparison.signedIso Rᵐᵒᵖ (Q X η)
    (NoncommResidualDerivedComparison.groupComplex Rᵐᵒᵖ X η (input R X η hR M))

def normalize := NoncommCompletedTransport.doubleOppositeModules R (G := Q X η) ⋙
  NoncommSourceTarget.toGaloisModules R X η

instance normalize_additive : (normalize R X η).Additive :=
  inferInstanceAs ((NoncommCompletedTransport.doubleOppositeModules R (G := Q X η) ⋙
    NoncommSourceTarget.toGaloisModules R X η).Additive)
instance normalize_preservesFiniteLimits : PreservesFiniteLimits (normalize R X η) := by sorry
instance normalize_preservesFiniteColimits : PreservesFiniteColimits (normalize R X η) := by sorry

/-- The finite geometric signed-character endpoint, with original left R
coefficients and actual field-Galois completed action. -/
def finiteCharacterCochain := ((normalize R X η).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (NoncommReversedCharacterComplex.signed Rᵐᵒᵖ (Q X η) (finiteComplex R X η hR M))

variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))]

/-- Complete target-side assembly: finite geometric signed characters,
actual residual resolution span, compact character restriction, signs and
the independently constructed completed tensor, all in D(R[[Gal]]). -/
def derivedTargetIso : DerivedCategory.Q.obj (finiteCharacterCochain R X η hR M) ≅
    NoncommSourceTarget.derivedTarget R X η hR M :=
  ((normalize R X η).mapDerivedCategoryFactors.app
    (NoncommReversedCharacterComplex.signed Rᵐᵒᵖ (Q X η) (finiteComplex R X η hR M))).symm ≪≫
  (normalize R X η).mapDerivedCategory.mapIso
    (signedDualIso R X η hR M hne ≪≫ DerivedCategory.Q.mapIso (groupDegreeIso R X η hR M)) ≪≫
  (normalize R X η).mapDerivedCategoryFactors.app (NoncommSignedSourceTarget.residualCochain R X η hR M) ≪≫
  NoncommSignedSourceTarget.derivedIso R X η hR M

end NoncommGeometricDualCochainComparison
