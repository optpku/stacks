module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricCochainPullback

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ResidualDirectImageSections
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ {Y Z : Scheme.{u}} (g : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback g).op.HasLeftKanExtension F]
variable {X P : SchemeOverField k} (j : X ⟶ P)
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace P.left] [QuasiSeparatedSpace P.left]

/-- Actual arithmetic direct image; no geometric base-change of j_* is assumed. -/
def pushforward := (smallEtalePullback j.left).sheafPushforwardContinuous
  (ModuleCat.{u + 1} R) P.left.smallEtaleTopology X.left.smallEtaleTopology

instance pushforward_additive : (pushforward R j).Additive := by sorry

/-- Restrict an actual geometric section, then use the arithmetic pullback/direct-image counit. -/
def comparison : pushforward R j ⋙ NoncommGeometricSource.discreteSections R P ⟶
    NoncommGeometricSource.discreteSections R X where
  app F := (NoncommGeometricCochainPullback.sectionsComparison R j).app ((pushforward R j).obj F) ≫
    (NoncommGeometricSource.discreteSections R X).map
      ((smallEtalePullback_sheafAdjunction j.left (ModuleCat.{u + 1} R)).counit.app F)
  naturality := by sorry

/-- On each finite field neighborhood sections of direct image are sections
upstairs; qcqs continuity identifies their actual geometric stalk colimits. -/
instance comparison_isIso : IsIso (comparison R j) := by sorry

/-- Invert only the displayed section restriction/counit map. -/
def iso : pushforward R j ⋙ NoncommGeometricSource.discreteSections R P ≅
    NoncommGeometricSource.discreteSections R X :=
  @asIso _ _ _ _ (comparison R j) (comparison_isIso R j)

/-- Direct image preserves injectives because its module-sheaf inverse image
is exact. This does not assert exactness of the direct-image functor. -/
theorem pushforward_injective (I : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))
    [Injective I] : Injective ((pushforward R j).obj I) := by sorry

/-- Apply the specified section comparison to a whole arithmetic sheaf complex.
Taking J injective represents Rj_*; no concentration of Rj_* is asserted. -/
def cochainIso (J : CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ) :
    ((NoncommGeometricSource.discreteSections R P).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((pushforward R j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≅
    ((NoncommGeometricSource.discreteSections R X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ (iso R j).app (J.X i)) (by sorry)

end ResidualDirectImageSections
