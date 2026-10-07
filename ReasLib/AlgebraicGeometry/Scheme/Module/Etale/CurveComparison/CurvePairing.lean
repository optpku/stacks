module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CurveDuality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommIdentityCompactification

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace SourceFaithful03VN
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom] [GeometricallyConnected X.hom]
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U)
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules R)]
variable [X.left.smallEtaleTopology.HasSheafCompose (NoncommIntrinsicDualTransport.modules R)]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ))]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R))))]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
  (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R))),
  (etaleRestriction j).op.HasLeftKanExtension F]
variable (hR : IsUnit (Nat.card R : k))
variable (M : (finiteTypeDiscreteModule R
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X η)))).FullSubcategory)
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
  (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R), (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose
  (NoncommLocalHom.modules (NoncommLocalHom.opScalarHom
    (NoncommFiniteCoefficient.scalarHom R) (NoncommFiniteCoefficient.scalarHom_commute R)))]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom)]
variable [HasDerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [EnoughInjectives (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖᵐᵒᵖ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖᵐᵒᵖ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z)
  (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R))),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
  (F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}), (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ Y : Scheme.{u}, HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R))))]
variable [HasDerivedCategory (DiscreteModuleCat (ActualRootsModule.Coeff.{u} (Nat.card R)) Gal(AlgebraicClosure k/k))]
variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj Rᵐᵒᵖᵐᵒᵖ Gal(AlgebraicClosure k/k)))]
variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj Rᵐᵒᵖᵐᵒᵖ (NoncommResidualSectionsComparison.Q X η)))]
variable (hne : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
variable [∀ Y : Scheme.{u}, HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [HasDerivedCategory (DiscreteModuleCat R (NoncommResidualSectionsComparison.Γ X η))]
variable [HasDerivedCategory (DiscreteModuleCat R (NoncommResidualSectionsComparison.Q X η))]

/-- The actual trace pairing on the published finite sheaf and its intrinsic
right dual (canonically identified with the finite character/Tate coefficient). -/
def compactSupportPairing (i : ℤ) := CompactIntrinsicHomComparison.tracePairing R X η P hR M i

/-- Perfection belongs to the explicitly constructed geometric trace pairing,
with opposite handedness retained throughout the noncommutative coefficient chain. -/
@[stacks 03VN]
theorem compactSupportPairing_bijective (i : ℤ) :
    Function.Bijective (compactSupportPairing R X η P hR M i) :=
  CompactIntrinsicHomComparison.tracePairing_bijective R X η P hR M i

variable [Projective X.hom]

/-- Ordinary and compact cohomology are compared by the actual identity
extension counit and its resolution map, not by a chosen cohomology iso. -/
def identityHomologyIso (i : ℤ) :
    (CompactIntrinsicHomComparison.geometricSource R X η
      (NoncommIdentityCompactification.object X) M).homology i ≅
    (NoncommGeometricSource.arithmeticCochain R X
      ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)).homology i :=
  ((DerivedCategory.homologyFunctorFactors _ i).app
    (CompactIntrinsicHomComparison.geometricSource R X η
      (NoncommIdentityCompactification.object X) M)).symm ≪≫
  (DerivedCategory.homologyFunctor _ i).mapIso
    (NoncommIdentityCompactification.derivedIso R X
      ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)) ≪≫
  (DerivedCategory.homologyFunctorFactors _ i).app
    (NoncommGeometricSource.arithmeticCochain R X
      ((associatedSheafFunctor R (arithmeticPoint X η)).obj M))

/-- Actual projective Poincare pairing, via identity compactification and the
same normalized enhanced geometric trace. -/
def projectivePairing (i : ℤ) :
    (NoncommGeometricSource.arithmeticCochain R X
      ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)).homology (2 - i) →+
    CharacterModule (((NoncommGeometricFiniteModel.ordinary R X η M).homology i).obj.V) :=
  (CompactIntrinsicHomComparison.tracePairing R X η
    (NoncommIdentityCompactification.object X) hR M i).comp
      (identityHomologyIso R X η M (2 - i)).inv.hom.toAddMonoidHom

/-- Source 03VN's projective corollary for the specified ordinary pairing. -/
@[stacks 03VN]
theorem projectivePairing_bijective (i : ℤ) :
    Function.Bijective (projectivePairing R X η hR M i) := by sorry

end SourceFaithful03VN
