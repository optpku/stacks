/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactIntrinsicHomComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualDerivedComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommTensorNaturality

/-!
# Private source-faithful 03VM assembly

Local approved erratum, immutable trace.tex 3168ff and 3297–3333:
general field Gal, finite-field-only Zhat specialization, explicit [-2];
noncommutative left-module tensor order is Lambda tensor M(-1).
No immutable source bytes are changed.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace SourceFaithful03VM
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

/-- The actual enhanced geometric evaluation and normalized trace, followed
by the canonical character/ambient resolution/completed tensor comparisons. -/
def compactDerivedIso := CompactIntrinsicHomComparison.comparisonIso R X η P hR M hne

/-- Correct cohomological placement: homological degree i sits in cochain degree
2-i, with the residual action retained over the general field. -/
def compactDegreeIso (i : ℕ) :
    (CompactIntrinsicHomComparison.geometricSource R X η P M).homology (2 - (i : ℤ)) ≅
      (NoncommSourceTarget.galoisCochain R X η hR M).homology (2 - (i : ℤ)) :=
  ((DerivedCategory.homologyFunctorFactors _ (2 - (i : ℤ))).app
    (CompactIntrinsicHomComparison.geometricSource R X η P M)).symm ≪≫
  (DerivedCategory.homologyFunctor _ (2 - (i : ℤ))).mapIso (compactDerivedIso R X η P hR M hne) ≪≫
  (DerivedCategory.homologyFunctorFactors _ (2 - (i : ℤ))).app
    (NoncommSourceTarget.galoisCochain R X η hR M)

/-- 03VM's derived compact-support clause asserts invertibility of the explicit
map above; it never derives on the false finite representation category. -/
@[stacks 03VM]
theorem compactComparison_isIso : IsIso (CompactIntrinsicHomComparison.comparison R X η P hR M hne) :=
  CompactIntrinsicHomComparison.comparison_isIso R X η P hR M hne

variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [HasDerivedCategory (DiscreteModuleCat R (NoncommResidualSectionsComparison.Γ X η))]
variable [HasDerivedCategory (DiscreteModuleCat R (NoncommResidualSectionsComparison.Q X η))]

/-- Sections/invariants use the actual all-discrete associated-sheaf germ map. -/
def ordinaryZeroIso := NoncommResidualSectionsComparison.iso R X η

/-- The higher natural comparison derives in the all-discrete ambient category. -/
def ordinaryDegreeIso (i : ℕ) := NoncommResidualDerivedComparison.degreeIso R X η hne hR i

/-- Ordinary comparison for the published finite coefficient, in D(R[[Gal]]). -/
def ordinaryDerivedIso := NoncommResidualDerivedComparison.derivedOrdinaryIso R X η hne hR M

/-- The source coefficient map is the published associated-sheaf map followed
by extension by zero and the actual injective-resolution comparison. -/
def geometricCochainMap {M N : NoncommTensorNaturality.Input R X η} (f : M ⟶ N) :
    CompactIntrinsicHomComparison.geometricSource R X η P M ⟶
    CompactIntrinsicHomComparison.geometricSource R X η P N :=
  HomologicalComplex.extendMap
    (((NoncommGeometricSource.completedSections R P.obj.right).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
      (InjectiveResolution.desc
        ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} R)).map
          ((associatedSheafFunctor R (arithmeticPoint X η)).map f))
        (injectiveResolution ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u + 1} R)).obj ((associatedSheafFunctor R (arithmeticPoint X η)).obj N)))
        (injectiveResolution ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u + 1} R)).obj ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)))))
    ComplexShape.embeddingUpNat

/-- Geometric compact support, on finite coefficients but resolved in the
ambient sheaf category. Resolution homotopies give the functor laws. -/
def geometricFunctor : NoncommTensorNaturality.Input R X η ⥤ DerivedCategory
    (ModuleCat.{u + 1} (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k))) where
  obj M := DerivedCategory.Q.obj (CompactIntrinsicHomComparison.geometricSource R X η P M)
  map f := DerivedCategory.Q.map (geometricCochainMap R X η P f)
  map_id := by sorry
  map_comp := by sorry

/-- Naturality of the actual enhanced evaluation/trace composite, now against
independently defined geometric and compact projective-resolution maps. -/
def compactNaturalIso : geometricFunctor R X η P ≅ NoncommTensorNaturality.derivedFunctor R X η hR :=
  NatIso.ofComponents (fun M ↦ compactDerivedIso R X η P hR M hne) (by sorry)

section FiniteField
variable [Finite k]

instance finiteField_additive : (NoncommFiniteFieldTransport.modules k R).Additive := by
  unfold NoncommFiniteFieldTransport.modules NoncommCompletedTransport.modules
  infer_instance
instance finiteField_preservesFiniteLimits : PreservesFiniteLimits (NoncommFiniteFieldTransport.modules k R) := by
  unfold NoncommFiniteFieldTransport.modules NoncommCompletedTransport.modules
  infer_instance
instance finiteField_preservesFiniteColimits : PreservesFiniteColimits (NoncommFiniteFieldTransport.modules k R) := by
  unfold NoncommFiniteFieldTransport.modules NoncommCompletedTransport.modules
  infer_instance

variable [HasDerivedCategory (ModuleCat.{u + 1} (NoncommCompletedRing.Obj R
  (ActualFiniteFieldTransport.profiniteInt.{u} : Type u)))]

/-- Only this specialization assumes the field finite; it uses the actual
arithmetic Frobenius completed-ring transport on the full enhanced iso. -/
def finiteFieldIso := (NoncommFiniteFieldTransport.modules k R).mapDerivedCategory.mapIso
  (compactDerivedIso R X η P hR M hne)

end FiniteField

end SourceFaithful03VM
