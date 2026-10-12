/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricFiniteModel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.IntrinsicDualInjectiveResolution
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricProjectiveChain
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.OpenHomCochainComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomDerivedTranspose
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.BoundedInjectiveSectionsMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldHomNormalizedTrace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricScalarRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExactDerivedCochainTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCharacterEndpoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCharacterPairing

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace CompactIntrinsicHomComparison
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

/-- The explicit Hom resolution on the open curve obtained from the chosen compactification. -/
abbrev openHom := IntrinsicDualInjectiveResolution.complex R X (arithmeticPoint X η) P M

/-- Direct image of the Hom resolution, representing Rj_* of the dual. -/
def compactHom := ((ResidualDirectImageSections.pushforward Rᵐᵒᵖ P.obj.hom).mapHomologicalComplex
  (ComplexShape.up ℤ)).obj ((openHom R X η P M).extend ComplexShape.embeddingUpNat)

/-- Apply actual direct image to the recursive injective comparison and its
degree extension. This is a specified cochain map, with no concentration assumption. -/
def resolutionMap : NoncommGeometricFiniteModel.compactDualComplex R X η M P ⟶
    compactHom R X η P M :=
  ((ResidualDirectImageSections.pushforward Rᵐᵒᵖ P.obj.hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap
        (IntrinsicDualInjectiveResolution.comparison R X (arithmeticPoint X η) P M hR).hom
        ComplexShape.embeddingUpNat)

/-- The connected arithmetic global arrow from the finite-term Galois model
into the Hom-based direct-image model. -/
def map := NoncommGeometricFiniteModel.compactArithmeticSheafMap R X η hR M P ≫
  resolutionMap R X η P hR M

variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
  (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R), (etaleRestriction j).op.HasLeftKanExtension F]

/-- The finite locally projective resolution after extension by zero to the compactification. -/
abbrev compactSourceResolution := FiniteAssociatedResolution.compactComplex R (arithmeticPoint X η) M (Compactification.Of.ι P)
/-- The injective resolution of the roots-of-unity coefficient sheaf on the compactification. -/
abbrev compactRootsResolution := OpenExtensionInjectiveResolution.compactResolution
  (ActualRootsModule.Coeff.{u} (Nat.card R)) (Compactification.Of.ι P)
    (ActualRootsModule.liftedSheaf X.left (Nat.card R))

/-- The connected global map into the compactification Hom complex using the
specified source and roots resolutions. -/
def evaluationInput :
    (GeometricProjectiveChain.pulledChain R X η hR M P).extend CompactRepresentation.curveDegreeEmbedding ⟶
    NoncommLocalHomComplex.integerComplex (NoncommFiniteCoefficient.scalarHom R)
      (NoncommFiniteCoefficient.scalarHom_commute R) P.obj.right.left
      (compactSourceResolution R X η P M) (compactRootsResolution R X P).cocomplex :=
  (GeometricProjectiveChain.pulledIso R X η hR M P).hom ≫ map R X η P hR M ≫
  (OpenHomCochainComparison.integerIso (NoncommFiniteCoefficient.scalarHom R)
    (NoncommFiniteCoefficient.scalarHom_commute R) (Compactification.Of.ι P)
    (FiniteAssociatedResolution.complex R (arithmeticPoint X η) M)
    (compactRootsResolution R X P).cocomplex).inv

variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose
  (NoncommLocalHom.modules (NoncommLocalHom.opScalarHom
    (NoncommFiniteCoefficient.scalarHom R) (NoncommFiniteCoefficient.scalarHom_commute R)))]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom)]

/-- The local-Hom transpose of the compact-support evaluation map. -/
def transpose := LocalHomCurveTranspose.map (NoncommFiniteCoefficient.scalarHom R)
  (NoncommFiniteCoefficient.scalarHom_commute R) P.obj.right.left (compactSourceResolution R X η P M)
  (GeometricProjectiveChain.pulledChain R X η hR M P) (compactRootsResolution R X P).cocomplex
  (evaluationInput R X η P hR M)

variable [HasDerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u + 1} R))]

/-- Actual bounded-derived evaluation roof on the compactification, with the
source augmentation and Koszul transpose fixed before localization. -/
def derivedEvaluation :=
  -- Local instance justification (proof-local temporary data): the actual j! source-resolution augmentation is a quasi-isomorphism.
  letI := FiniteAssociatedResolution.compactAugmentation_quasiIso R (arithmeticPoint X η) M (Compactification.Of.ι P)
  LocalHomDerivedTranspose.plusMap (NoncommFiniteCoefficient.scalarHom R)
    (NoncommFiniteCoefficient.scalarHom_commute R) P.obj.right.left (compactSourceResolution R X η P M)
    (GeometricProjectiveChain.pulledChain R X η hR M P) (compactRootsResolution R X P).cocomplex
    (evaluationInput R X η P hR M)
    (FiniteAssociatedResolution.compactAugmentation R (arithmeticPoint X η) M (Compactification.Of.ι P))

/-- Injectivity of the local-Hom transpose target in each degree. -/
theorem transposeTarget_injective (i : ℤ) : Injective
    ((LocalHomCurveTranspose.target (NoncommFiniteCoefficient.scalarHom R)
      (NoncommFiniteCoefficient.scalarHom_commute R) P.obj.right.left
      (GeometricProjectiveChain.pulledChain R X η hR M P) (compactRootsResolution R X P).cocomplex).X i) := sorry

variable [EnoughInjectives (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))]

/-- Apply actual derived geometric completed sections to the fixed evaluation
roof. This is an R[[Gal]]-linear derived morphism from the genuine compact-support
source; normalized trace and finite character identification are composed next. -/
def geometricEvaluation :
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R P.obj.right
      ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} R)).obj
        ((associatedSheafFunctor R (arithmeticPoint X η)).obj M))) ⟶
    DerivedCategory.Q.obj
      (((NoncommGeometricSource.completedSections R P.obj.right).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (LocalHomCurveTranspose.target (NoncommFiniteCoefficient.scalarHom R)
          (NoncommFiniteCoefficient.scalarHom_commute R) P.obj.right.left
          (GeometricProjectiveChain.pulledChain R X η hR M P) (compactRootsResolution R X P).cocomplex)) :=
  -- Local instance justification (proof-local temporary data): the concrete Hom target has the preceding injectivity criterion.
  letI : ∀ i : ℤ, Injective
      ((LocalHomDerivedTranspose.targetPlus (NoncommFiniteCoefficient.scalarHom R)
        (NoncommFiniteCoefficient.scalarHom_commute R) P.obj.right.left
        (GeometricProjectiveChain.pulledChain R X η hR M P) (compactRootsResolution R X P).cocomplex).obj.X i) :=
    fun i ↦ transposeTarget_injective R X η P hR M i
  BoundedInjectiveSectionsMap.map (NoncommGeometricSource.completedSections R P.obj.right)
    (LocalHomDerivedTranspose.targetPlus (NoncommFiniteCoefficient.scalarHom R)
      (NoncommFiniteCoefficient.scalarHom_commute R) P.obj.right.left
      (GeometricProjectiveChain.pulledChain R X η hR M P) (compactRootsResolution R X P).cocomplex)
    ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} R)).obj
      ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)) (derivedEvaluation R X η P hR M)

/-- The coefficient cardinality is nonzero. -/
instance card_neZero : NeZero (Nat.card R) := ⟨Nat.ne_of_gt (NoncommFiniteCoefficient.card_pos R)⟩

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

/-- The right scalar map used by the local-Hom complex. -/
abbrev rightScalar := NoncommLocalHom.opScalarHom (NoncommFiniteCoefficient.scalarHom R)
  (NoncommFiniteCoefficient.scalarHom_commute R)
/-- The centrality witness for the right scalar map. -/
abbrev rightCentral := NoncommLocalHom.opScalarHom_central (NoncommFiniteCoefficient.scalarHom R)
  (NoncommFiniteCoefficient.scalarHom_commute R)

/-- The shifted local-Hom complex before scalar normalization. -/
abbrev rawHom := NoncommLocalHomComplex.shiftedComplex (rightScalar R) (rightCentral R) P.obj.right.left
  (GeometricProjectiveChain.pulledChain R X η hR M P) (compactRootsResolution R X P).cocomplex

/-- The double-opposite scalar normalization functor. -/
def normalize := (NoncommCompletedTransport.doubleOppositeModules R (G := Gal(AlgebraicClosure k/k)) :
  ModuleCat.{u + 1} (NoncommCompletedRing.Obj Rᵐᵒᵖᵐᵒᵖ Gal(AlgebraicClosure k/k)) ⥤
    ModuleCat.{u + 1} (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))

/-- Double-opposite scalar normalization preserves addition of morphisms. -/
instance normalize_additive : (normalize (k := k) R).Additive :=
  inferInstanceAs ((NoncommCompletedTransport.doubleOppositeModules R (G := Gal(AlgebraicClosure k/k))).Additive)
/-- Double-opposite scalar normalization preserves finite limits. -/
instance normalize_preservesFiniteLimits : PreservesFiniteLimits (normalize (k := k) R) := by
  unfold normalize NoncommCompletedTransport.doubleOppositeModules
  infer_instance
/-- Double-opposite scalar normalization preserves finite colimits. -/
instance normalize_preservesFiniteColimits : PreservesFiniteColimits (normalize (k := k) R) := by
  unfold normalize NoncommCompletedTransport.doubleOppositeModules
  infer_instance

/-- The actual finite field-Hom character model after returning double-opposite
scalars to the original R; this is the next input to the completed tensor comparison. -/
def traceCharacterModel := ((normalize (k := k) R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (NoncommCompletedCochainTransport.cochain Rᵐᵒᵖᵐᵒᵖ Gal(AlgebraicClosure k/k)
    (FieldHomNormalizedTrace.characterModel (Nat.card R) (rightScalar R) (rightCentral R)
      (GeometricProjectiveChain.chain R X η hR M)))

/-- The completed field-Hom trace source after double-opposite scalar normalization. -/
def traceSource := ((normalize (k := k) R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (NoncommCompletedCochainTransport.cochain Rᵐᵒᵖᵐᵒᵖ Gal(AlgebraicClosure k/k)
    (FieldHomNormalizedTrace.source (Nat.card R) (rightScalar R) (rightCentral R) X P
      (GeometricProjectiveChain.chain R X η hR M)))

/-- Normalize the specified completed trace by the exact coefficient functor. -/
def normalizedTrace : DerivedCategory.Q.obj (traceSource R X η P hR M) ⟶
    DerivedCategory.Q.obj (traceCharacterModel R X η hR M) :=
  ExactDerivedCochainTransport.map (normalize (k := k) R) _ _
    (FieldHomNormalizedTrace.completedTrace (Nat.card R) (rightScalar R) (rightCentral R) X P hR
      (GeometricProjectiveChain.chain R X η hR M) (GeometricProjectiveChain.term_finite R X η hR M))

/-- The geometric evaluation followed by the normalized character trace. -/
def geometricEvaluationTrace :
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R P.obj.right
      ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} R)).obj
        ((associatedSheafFunctor R (arithmeticPoint X η)).obj M))) ⟶
    DerivedCategory.Q.obj (traceCharacterModel R X η hR M) := by
  refine geometricEvaluation R X η P hR M ≫ ?_
  refine DerivedCategory.Q.map (GeometricScalarRestriction.cochainIso (RingEquiv.opOp R).toRingHom
    P.obj.right (rawHom R X η P hR M)).hom ≫ ?_
  refine DerivedCategory.Q.map
    (((normalize (k := k) R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (GeometricCompletedComposition.iso Rᵐᵒᵖᵐᵒᵖ P.obj.right (rawHom R X η P hR M)).hom) ≫ ?_
  exact normalizedTrace R X η P hR M

/-- The actual field-Hom character identification, followed by the signed
degree comparison already connected to compact group homology. -/
def traceCharacterIso : traceCharacterModel R X η hR M ≅
    GeometricCharacterEndpoint.source R X η hR M := by
  -- Local instance justification (proof-local temporary data): these specific geometric chain terms are finite.
  letI := GeometricProjectiveChain.term_finite R X η hR M
  exact ((normalize (k := k) R).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    (FieldCharacterCochain.completedIso k (GeometricProjectiveChain.chain R X η hR M)
      (Nat.card R) (rightScalar R) (rightCentral R))

variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj Rᵐᵒᵖᵐᵒᵖ (NoncommResidualSectionsComparison.Q X η)))]
variable (hne : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))

/-- Full enhanced derived geometric evaluation/trace into the completed
tensor target. The source is the actual published associated sheaf on this
compactification. All arrows are R[[Gal]]-linear, with noncommutative R. -/
def comparison :
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R P.obj.right
      ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} R)).obj
        ((associatedSheafFunctor R (arithmeticPoint X η)).obj M))) ⟶
    NoncommSourceTarget.derivedTarget R X η hR M :=
  geometricEvaluationTrace R X η P hR M ≫
    DerivedCategory.Q.map (traceCharacterIso R X η hR M).hom ≫
    (GeometricCharacterEndpoint.derivedTargetIso R X η hR M hne).hom

/-- Curve Poincare duality for the enhanced evaluation and normalized trace.
After forgetting coefficients it is the geometric evaluation with Picard-degree
trace, so it is a quasi-isomorphism. Faithful exact forgetting reflects this
property; no arbitrary enhancement or new comparison is assumed. -/
theorem geometricEvaluationTrace_isIso : IsIso (geometricEvaluationTrace R X η P hR M) := sorry

/-- Invertibility of the actual full composite, not existence of a desired iso. -/
theorem comparison_isIso : IsIso (comparison R X η P hR M hne) := by
  -- Local instance justification (proof-local temporary data): curve duality applies to this specified enhanced trace.
  letI := geometricEvaluationTrace_isIso R X η P hR M
  unfold comparison
  infer_instance

/-- The complete noncommutative geometric-to-completed-tensor isomorphism. -/
def comparisonIso := @asIso _ _ _ _ (comparison R X η P hR M hne)
  (comparison_isIso R X η P hR M hne)

/-- The completed geometric cochain complex of the associated sheaf extended by zero. -/
abbrev geometricSource := NoncommGeometricSource.arithmeticCochain R P.obj.right
  ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} R)).obj
    ((associatedSheafFunctor R (arithmeticPoint X η)).obj M))

/-- The geometric trace into the signed dual cochain model before the
group-theoretic tensor comparison. -/
def signedGeometricTrace : DerivedCategory.Q.obj (geometricSource R X η P M) ⟶
    DerivedCategory.Q.obj (GeometricCharacterEndpoint.target R X η hR M) :=
  geometricEvaluationTrace R X η P hR M ≫
    DerivedCategory.Q.map ((traceCharacterIso R X η hR M).hom ≫
      (GeometricCharacterEndpoint.iso R X η hR M).hom)

/-- Take actual derived cohomology of the specified enhanced trace. -/
def signedHomologyMap (i : ℤ) : (geometricSource R X η P M).homology i ⟶
    (GeometricCharacterEndpoint.target R X η hR M).homology i :=
  (DerivedCategory.homologyFunctorFactors _ i).inv.app (geometricSource R X η P M) ≫
    (DerivedCategory.homologyFunctor _ i).map (signedGeometricTrace R X η P hR M) ≫
    (DerivedCategory.homologyFunctorFactors _ i).hom.app (GeometricCharacterEndpoint.target R X η hR M)

/-- The character-valued pairing obtained from geometric evaluation and trace. -/
def tracePairing (i : ℤ) : (geometricSource R X η P M).homology (2 - i) →+
    CharacterModule (((NoncommGeometricFiniteModel.ordinary R X η M).homology i).obj.V) :=
  (GeometricCharacterPairing.characterMap R X η hR M i).comp
    (signedHomologyMap R X η P hR M (2 - i)).hom.toAddMonoidHom

/-- Perfection of the displayed pairing follows from curve trace duality and
exact finite-character cohomology, with no arbitrary pairing input. -/
theorem tracePairing_bijective
    (hne : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (i : ℤ) : Function.Bijective (tracePairing R X η P hR M i) := sorry

variable [∀ Y : Scheme.{u}, HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable (P' : Compactification.Of (Spec (CommRingCat.of k)) X)
variable (f : P'.obj.right ⟶ P.obj.right) [IsProper f.left]
variable (hcart : IsPullback (𝟙 X.left) (Compactification.Of.ι P') (Compactification.Of.ι P) f.left)

/-- Compatibility with the actual proper-refinement/extension-by-zero mate.
The transport is defined independently from the trace and tensor comparison;
this equation does not define transport by conjugating the desired result. -/
theorem refinement_compatibility :
    DerivedCategory.Q.map (NoncommCompactificationTransport.completedMap R X P P' f hcart
      ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)) ≫
        comparison R X η P' hR M hne = comparison R X η P hR M hne := sorry

end CompactIntrinsicHomComparison
