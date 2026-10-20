module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CurveDuality
import StacksCheckRecall

/-!
The residual group over an arbitrary field is its absolute Galois group.
Compact homological degree i is placed in cohomological degree 2-i,
equivalently by shifting the usual homological realization by [-2].
Over a finite field the residual action specializes to the profinite integers.
For left coefficients the tensor order is Lambda tensor M(-1).
-/

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
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory)
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
variable (hne : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
variable [∀ Y : Scheme.{u}, HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]

variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [HasDerivedCategory (DiscreteModuleCat R (NoncommResidualSectionsComparison.Γ X η))]
variable [HasDerivedCategory (DiscreteModuleCat R (NoncommResidualSectionsComparison.Q X η))]

variable (i : ℕ)

/- Proposition 64.29.3 (1). The actual compact-support evaluation and trace
give a natural derived isomorphism to completed tensor, for arbitrary finite rings. -/
@[stacks 03VM]
#check (SourceFaithful03VM.compactNaturalIso R X η P hR hne :
  SourceFaithful03VM.geometricFunctor R X η P ≅
    NoncommTensorNaturality.derivedFunctor R X η hR)

/- Proposition 64.29.3 (2). Taking degree 2-i gives compact group homology
with the inverse Tate twist and the same residual action. -/
@[stacks 03VM]
#check (SourceFaithful03VM.compactDegreeIso R X η P hR M hne i :
  (CompactIntrinsicHomComparison.geometricSource R X η P M).homology (2 - (i : ℤ)) ≅
    (NoncommSourceTarget.galoisCochain R X η hR M).homology (2 - (i : ℤ)))

/- Proposition 64.29.3 (3). Geometric sections identify naturally with
geometric invariants in the all-discrete ambient category. -/
@[stacks 03VM]
#check (SourceFaithful03VM.ordinaryZeroIso R X η :
  NoncommResidualSectionsComparison.realizedSections R X η ≅
    NoncommResidualSectionsComparison.invariants R X η)

/- Proposition 64.29.3 (4). The higher comparison is the canonical natural
derived-invariants comparison under curve-specific effacement. -/
@[stacks 03VM]
#check (SourceFaithful03VM.ordinaryDegreeIso R X η hR hne i :
  (NoncommResidualSectionsComparison.invariants R X η).rightDerived i ≅
    AlgebraicGeometry.Scheme.AmbientAssociatedSheaf.functor
      (Λ := R) (xbar := arithmeticPoint X η) ⋙
        (NoncommResidualSectionsComparison.sheafSections R X η).rightDerived i)

/- Proposition 64.29.3 (5). The ordinary comparison retains the completed
residual Galois action on the actual published associated sheaf. -/
@[stacks 03VM]
#check (SourceFaithful03VM.ordinaryDerivedIso R X η hR M hne :
  DerivedCategory.Q.obj (NoncommResidualDerivedComparison.completedGroupComplex R X η M) ≅
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R X
      ((AlgebraicGeometry.Scheme.associatedSheafFunctor R (arithmeticPoint X η)).obj M)))

section FiniteField

variable [Finite k]
variable [HasDerivedCategory (ModuleCat.{u + 1}
  (completedGroupRing R (ProfiniteGrp.hatZ.{u} : Type u)))]

/- Proposition 64.29.3 (6). For finite ground fields only, arithmetic Frobenius
transports the same derived comparison to the profinite-integer residual group. -/
@[stacks 03VM]
#check (SourceFaithful03VM.finiteFieldIso R X η P hR M hne :
  (NoncommFiniteFieldTransport.modules k R).mapDerivedCategory.obj
    (DerivedCategory.Q.obj (CompactIntrinsicHomComparison.geometricSource R X η P M)) ≅
  (NoncommFiniteFieldTransport.modules k R).mapDerivedCategory.obj
    (DerivedCategory.Q.obj (NoncommSourceTarget.galoisCochain R X η hR M)))

end FiniteField

end
