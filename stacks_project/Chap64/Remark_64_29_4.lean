module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CurvePairing
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
universe u

section
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
  (completedGroupRing R Gal(AlgebraicClosure k/k)))]
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
  (completedGroupRing Rᵐᵒᵖᵐᵒᵖ Gal(AlgebraicClosure k/k)))]
variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [HasDerivedCategory (ModuleCat.{u + 1}
  (completedGroupRing Rᵐᵒᵖᵐᵒᵖ (NoncommResidualSectionsComparison.Q X η)))]
variable [∀ Y : Scheme.{u}, HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [HasDerivedCategory (DiscreteModuleCat R (NoncommResidualSectionsComparison.Γ X η))]
variable [HasDerivedCategory (DiscreteModuleCat R (NoncommResidualSectionsComparison.Q X η))]
variable (hne : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
variable (i : ℤ)

/- Remark 64.29.4 (1). The specified geometric evaluation and normalized
trace give the perfect compact-support pairing with ordinary cohomology of
the intrinsic right dual, canonically the character/Tate coefficient. -/
@[stacks 03VN]
#check (AlgebraicGeometry.SchemeOverField.CurveDuality.compactSupportPairing_bijective
  R X η P hR M hne i :
  Function.Bijective
    (CompactIntrinsicHomComparison.tracePairing R X η P hR M i))

variable [Projective X.hom]

/- Remark 64.29.4 (2). For projective curves the actual identity-extension
counit identifies compact and ordinary cohomology, giving Poincare duality. -/
@[stacks 03VN]
#check (AlgebraicGeometry.SchemeOverField.CurveDuality.projectivePairing_bijective
  R X η hR M hne i :
  Function.Bijective
    (AlgebraicGeometry.SchemeOverField.CurveDuality.projectivePairing
      R X η hR M i))

end
