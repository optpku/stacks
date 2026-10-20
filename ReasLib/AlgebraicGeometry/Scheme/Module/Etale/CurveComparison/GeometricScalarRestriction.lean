module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldScalarStalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldGeometricAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedCochainTransport

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace GeometricScalarRestriction
variable {k : Type u} [Field k]
variable {S T : Type (u + 1)} [Ring S] [Ring T] (h : S →+* T)
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} S)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} T)]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars.{u + 1} h)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} S),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} T),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable (P : SchemeOverField k) [CompactSpace P.left] [QuasiSeparatedSpace P.left]

abbrev sheaves (Y : Scheme.{u}) := sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} h)

/-- Precomposition of etale sections and restriction of their scalars commute
by the identity on each module; no geometric inverse-image preservation claim is assumed. -/
def directImageIso (F : Sheaf P.left.smallEtaleTopology (ModuleCat.{u + 1} T)) :
    (FieldGeometricAdjunction.directImage S P).obj ((sheaves h P.left).obj F) ≅
    (sheaves h (Spec (CommRingCat.of k))).obj ((FieldGeometricAdjunction.directImage T P).obj F) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by sorry))

/-- Actual geometric scalar comparison through field direct images and the
canonical scalar/stalk map, retaining the independently constructed residual action. -/
def discreteIso (F : Sheaf P.left.smallEtaleTopology (ModuleCat.{u + 1} T)) :
    (NoncommGeometricSource.discreteSections S P).obj ((sheaves h P.left).obj F) ≅
    (DiscreteScalarRestriction.functor h Gal(AlgebraicClosure k/k)).obj
      ((NoncommGeometricSource.discreteSections T P).obj F) :=
  ((@asIso _ _ _ _ (FieldGeometricAdjunction.comparison S P)
    (FieldGeometricAdjunction.comparison_isIso S P)).app ((sheaves h P.left).obj F)).symm ≪≫
  (FieldModuleDescent.forward k S).mapIso (directImageIso h P F) ≪≫
  FieldScalarStalk.discreteIso k h ((FieldGeometricAdjunction.directImage T P).obj F) ≪≫
  (DiscreteScalarRestriction.functor h Gal(AlgebraicClosure k/k)).mapIso
    ((@asIso _ _ _ _ (FieldGeometricAdjunction.comparison T P)
      (FieldGeometricAdjunction.comparison_isIso T P)).app F)

/-- Coefficient restriction also commutes with the actual completed action by
identity on vectors and the finite-level scalar formula. -/
def completedIso (F : Sheaf P.left.smallEtaleTopology (ModuleCat.{u + 1} T)) :
    (NoncommGeometricSource.completedSections S P).obj ((sheaves h P.left).obj F) ≅
    (ModuleCat.restrictScalars
      (NoncommCompletedTransport.coefficientHom S (G := Gal(AlgebraicClosure k/k)) h)).obj
      ((NoncommGeometricSource.completedSections T P).obj F) :=
  (NoncommPointwiseCompletedAction.functor S Gal(AlgebraicClosure k/k)).mapIso (discreteIso h P F) ≪≫
    DiscreteScalarRestriction.completionIso h Gal(AlgebraicClosure k/k)
      ((NoncommGeometricSource.discreteSections T P).obj F)

instance sheaves_additive : (sheaves h P.left).Additive := by sorry

/-- Degreewise the same scalar comparison, compatible with all specified differentials. -/
def cochainIso (K : CochainComplex (Sheaf P.left.smallEtaleTopology (ModuleCat.{u + 1} T)) ℤ) :
    ((NoncommGeometricSource.completedSections S P).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((sheaves h P.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
    ((ModuleCat.restrictScalars
      (NoncommCompletedTransport.coefficientHom S (G := Gal(AlgebraicClosure k/k)) h)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((NoncommGeometricSource.completedSections T P).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ completedIso h P (K.X i)) (by sorry)

end GeometricScalarRestriction

namespace GeometricCompletedComposition
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable (P : SchemeOverField k) [CompactSpace P.left] [QuasiSeparatedSpace P.left]

/-- The canonical functor compositor, made explicit to avoid unfolding the
geometric section action when joining the completed trace endpoint. -/
def iso (K : CochainComplex (Sheaf P.left.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ) :
    ((NoncommGeometricSource.completedSections R P).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
    NoncommCompletedCochainTransport.cochain R Gal(AlgebraicClosure k/k)
      (((NoncommGeometricSource.discreteSections R P).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  ((Functor.mapHomologicalComplexCompIso
    (Iso.refl (NoncommGeometricSource.completedSections R P)) (ComplexShape.up ℤ)).app K).symm

end GeometricCompletedComposition
