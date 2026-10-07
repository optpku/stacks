module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExtensionBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricSections
public import stacks_project.Chap64.Remark_64_29_2_Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ActualGeometricCompactSupport
variable {k : Type u} [Field k]
variable (X : SchemeOverField k) (P : Compactification.Of (Spec (CommRingCat.of k)) X)

/-- The geometric open immersion is the actual map between the two base-change pullbacks. -/
def interior : geometricBaseChange X ⟶ geometricBaseChange P.obj.right :=
  pullback.map X.hom (FieldExtension.specMap k (AlgebraicClosure k))
    P.obj.right.hom (FieldExtension.specMap k (AlgebraicClosure k))
    (Compactification.Of.ι P) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id, Compactification.Of.ι] using P.obj.hom.w.symm) (by simp)

instance interior_open : IsOpenImmersion (interior X P) := sorry

/-- The actual geometric/arithmetic compactification square is cartesian. -/
theorem cartesian : IsPullback (geometricToArithmeticHom X) (interior X P)
    (Compactification.Of.ι P) (geometricToArithmeticHom P.obj.right) := sorry

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : (geometricBaseChange X).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleRestriction (interior X P)).op.HasLeftKanExtension F]

/-- The source endpoint's coefficient object maps to geometric extension by
zero through the actual base-change mate. -/
def coefficientIso (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    geometricModuleRestrictionCompactSupport X P F ≅
    (etaleExtensionByZero (interior X P) (ModuleCat.{u + 1} Λ)).obj
      ((AmbientGeometry.modulePullback Λ (geometricToArithmeticHom X)).obj F) :=
  (ActualExtensionBaseChange.extensionIso (Compactification.Of.ι P) (interior X P)
    (geometricToArithmeticHom X) (geometricToArithmeticHom P.obj.right)
    (cartesian X P) (ModuleCat.{u + 1} Λ)).app F

variable [HasSheafify (geometricBaseChange P.obj.right).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf (geometricBaseChange P.obj.right).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [(geometricBaseChange P.obj.right).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- The CURRENT production compact-support endpoint is compared to the
geometric-open model by applying its actual site cohomology functor. -/
def cohomologyIso (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (i : ℕ) :
    geometricModuleEtaleHqCompactSupport X P F i ≅
    (siteModuleCohomologyModuleFunctor
      (J := (geometricBaseChange P.obj.right).smallEtaleTopology) (A := Λ) i).obj
      ((etaleExtensionByZero (interior X P) (ModuleCat.{u + 1} Λ)).obj
        ((AmbientGeometry.modulePullback Λ (geometricToArithmeticHom X)).obj F)) :=
  (siteModuleCohomologyModuleFunctor
    (J := (geometricBaseChange P.obj.right).smallEtaleTopology) (A := Λ) i).mapIso
      (coefficientIso X P Λ F)

end ActualGeometricCompactSupport
