/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldCharacterCochain
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricProjectiveChain
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricDualCochainComparison

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace GeometricCharacterEndpoint
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom] [GeometricallyConnected X.hom]
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
variable [HasWeakSheafify X.left.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U)
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ))]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable (hR : IsUnit (Nat.card R : k))
variable (M : (finiteTypeDiscreteModule R
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory)

abbrev B := GeometricProjectiveChain.chain R X η hR M

/-- Characters of exactly the same finite chain used in the geometric Hom
construction, with pointwise completed action and original left coefficients. -/
def source : CochainComplex (ModuleCat.{u + 1}
    (completedGroupRing R Gal(AlgebraicClosure k/k))) ℤ :=
  -- Local instance justification (proof-local temporary data): these particular terms are finite.
  letI := GeometricProjectiveChain.term_finite R X η hR M
  ((NoncommCompletedTransport.doubleOppositeModules R (G := Gal(AlgebraicClosure k/k))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
      (NoncommCompletedCochainTransport.cochain Rᵐᵒᵖᵐᵒᵖ Gal(AlgebraicClosure k/k)
        ((FieldCharacterCochain.complex k (B R X η hR M)).extend ComplexShape.embeddingUpNat))

abbrev target := NoncommGeometricDualCochainComparison.finiteCharacterCochain R X η hR M

/-- The actual degree placement equality, followed by its canonical component
iso. This identifies coefficient vectors before any character dualization. -/
def inputIso (i : ℕ) :
    (NoncommGeometricFiniteModel.projectiveCochain R X η hR M).X (2 - (i : ℤ)) ≅
      (B R X η hR M).X i :=
  (HomologicalComplex.eval _ _ (2 - (i : ℤ))).mapIso
    (eqToIso (GeometricProjectiveChain.extend_eq R X η hR M).symm) ≪≫
  (B R X η hR M).extendXIso CompactRepresentation.curveDegreeEmbedding
    (i := i) (i' := 2 - (i : ℤ)) rfl

/-- Before extension, finite pointwise characters and compact characters have
the same actual functions. The completed scalar law uses the finite action,
including the specified residual-group naming transport. -/
def positiveEquiv (i : ℕ) :
    (source R X η hR M).X (i : ℤ) ≃ₗ[completedGroupRing R Gal(AlgebraicClosure k/k)]
      (target R X η hR M).X (i : ℤ) := by
  -- Local instance justification (proof-local temporary data): the actual geometric chain terms are finite.
  letI := GeometricProjectiveChain.term_finite R X η hR M
  let e := (FieldCharacterCochain.complex k (B R X η hR M)).extendXIso
    ComplexShape.embeddingUpNat (i := i) (i' := (i : ℤ)) rfl
  let completion := (NoncommPointwiseCompletedAction.functor Rᵐᵒᵖᵐᵒᵖ Gal(AlgebraicClosure k/k)) ⋙
    NoncommCompletedTransport.doubleOppositeModules R (G := Gal(AlgebraicClosure k/k))
  let ep := completion.mapIso e
  exact ep.toLinearEquiv.trans
    { toFun := fun χ ↦ ActualOppositeCharacter.map Rᵐᵒᵖ _ (inputIso R X η hR M i).hom.hom.hom.hom χ
      invFun := fun χ ↦ ActualOppositeCharacter.map Rᵐᵒᵖ _ (inputIso R X η hR M i).inv.hom.hom.hom χ
      left_inv := by sorry
      right_inv := by sorry
      map_add' := by sorry
      map_smul' := by sorry }

theorem source_negative_zero (i : ℤ) (hi : i < 0) : IsZero ((source R X η hR M).X i) := by sorry
theorem target_negative_zero (i : ℤ) (hi : i < 0) : IsZero ((target R X η hR M).X i) := by sorry

/-- Positive degrees use character precomposition through the actual degree
iso. Only genuinely out-of-support degrees use zero-object comparisons. -/
def componentIso (i : ℤ) : (source R X η hR M).X i ≅ (target R X η hR M).X i :=
  if hi : 0 ≤ i then
    ((source R X η hR M).XIsoOfEq (Int.toNat_of_nonneg hi).symm) ≪≫
    (positiveEquiv R X η hR M i.toNat).toModuleIso ≪≫
    (target R X η hR M).XIsoOfEq (Int.toNat_of_nonneg hi)
  else (source_negative_zero R X η hR M i (by omega)).iso
    (target_negative_zero R X η hR M i (by omega))

/-- End-to-end signed character endpoint comparison, retaining completed
residual action. Naturality checks the same (-1)^(i+1) sign on both sides. -/
def iso : source R X η hR M ≅ target R X η hR M :=
  HomologicalComplex.Hom.isoOfComponents (componentIso R X η hR M) (by sorry)

variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [HasDerivedCategory (ModuleCat.{u + 1}
  (completedGroupRing Rᵐᵒᵖᵐᵒᵖ (NoncommResidualSectionsComparison.Q X η)))]
variable [HasDerivedCategory (ModuleCat.{u + 1}
  (completedGroupRing R Gal(AlgebraicClosure k/k)))]
variable (hne : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))

/-- The signed finite field characters now reach the full tensor target via
the already fixed ambient-resolution comparison, without choosing a new iso. -/
def derivedTargetIso : DerivedCategory.Q.obj (source R X η hR M) ≅
    NoncommSourceTarget.derivedTarget R X η hR M :=
  DerivedCategory.Q.mapIso (iso R X η hR M) ≪≫
    NoncommGeometricDualCochainComparison.derivedTargetIso R X η hR M hne

end GeometricCharacterEndpoint
