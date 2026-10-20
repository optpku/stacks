module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomCurveTranspose
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExactDerivedUnit

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace LocalHomDerivedTranspose
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [Y.smallEtaleTopology.HasSheafCompose
  (NoncommLocalHom.modules (NoncommLocalHom.opScalarHom h hc))]
variable [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable (L : ChainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
variable (B : ChainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)) ℕ)
variable (J : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℕ)
variable (e : B.extend CompactRepresentation.curveDegreeEmbedding ⟶
  NoncommLocalHomComplex.integerComplex h hc Y L J)
variable {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
variable (α : L ⟶ (ChainComplex.single₀ _).obj F) [QuasiIso α]

/-- Extend the specified source augmentation to negative cochain degrees,
then use the canonical single-complex extension identification. -/
def sourceMap : L.extend ComplexShape.embeddingDownNat ⟶
    (CochainComplex.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) 0).obj F :=
  HomologicalComplex.extendMap α ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat F 0 0 rfl).hom

instance sourceMap_quasiIso : QuasiIso (sourceMap Y L α) := by sorry

instance target_bounded : CochainComplex.IsStrictlyGE (LocalHomCurveTranspose.target h hc Y B J) (-2) := by sorry

/-- A concrete bounded-below target, since its Hom source lies in degrees 2-i. -/
def targetPlus : CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  ⟨LocalHomCurveTranspose.target h hc Y B J, ⟨-2, target_bounded h hc Y B J⟩⟩

variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]

/-- Actual derived roof: invert ONLY the concrete source-resolution augmentation,
then apply the explicit Koszul-transposed cochain map. -/
def map :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) 0).obj F) ⟶
    DerivedCategory.Q.obj (LocalHomCurveTranspose.target h hc Y B J) :=
  inv (DerivedCategory.Q.map (sourceMap Y L α)) ≫
    DerivedCategory.Q.map (LocalHomCurveTranspose.map h hc Y L B J e)

/-- The actual single-model inclusion/extension isomorphism. -/
def sourceFactor :
    (DerivedCategory.Plus.ι : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤ _).obj
      (ActualResolutionComparison.singleModel F) ≅
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) 0).obj F) :=
  (DerivedCategory.Plus.Qh.compInclusionIso (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))).app
    ((CochainComplex.Plus.extendNat _).obj ((CochainComplex.single₀ _).obj F)) ≪≫
  DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl)

/-- Lift this specified roof through the fully faithful bounded-below inclusion.
No arbitrary extension of a D(Ab) map to residual coefficients is involved. -/
def plusMap : ActualResolutionComparison.singleModel F ⟶ DerivedCategory.Plus.Q.obj (targetPlus h hc Y B J) :=
  (DerivedCategory.Plus.ι : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤ _).preimage
    ((sourceFactor Y (F := F)).hom ≫ map h hc Y L B J e α ≫
      ((DerivedCategory.Plus.Qh.compInclusionIso (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))).app
        (targetPlus h hc Y B J)).inv)

end LocalHomDerivedTranspose
