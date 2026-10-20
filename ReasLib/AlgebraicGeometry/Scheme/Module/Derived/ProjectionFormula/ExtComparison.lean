module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.CohomologyComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Transport

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalClosed
open DerivedTensor.Right.Monoidal
open RingedSite.Hom
open RingedSpace.Module.Derived
open RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace ProjectionFormula

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsNoetherian S] [LocallyOfFiniteType f]
variable (E : RingedSpace.ModuleDerived X.toRingedSpace)
variable (hE : RingedSpace.ModuleDerived.IsPerfect E)
variable (G : CochainComplex X.Modules ℤ)
variable (hG_bounded : CochainComplex.bounded X.Modules G)
variable [∀ n : ℤ, (G.X n).IsCoherent]
variable [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
variable [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f
  (RingedSpace.ModuleDerived.cohomologySheaf (DerivedCategory.Q.obj G) n)]
variable [h_homotopy_tensor_X : KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [h_tensor_X : KFlat.TensorDescends X.toRingedSpace]
variable [h_localization_X : KFlat.IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [KFlat.TensorDescends S.toRingedSpace]
variable [KFlat.IsLocalization S.toRingedSpace]
variable [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]

/-- Degree-`i` cohomology of the projection-formula source specialized to the canonical
dual of `E`, restricted to quasicoherent coefficients. -/
noncomputable def dualSourceCohomology (i : ℤ) :
    Scheme.QCoh S ⥤ AddCommGrpCat.{u} :=
  Scheme.QCoh.inclusion S ⋙ (source f (MonoidalClosed.dual E) G).toFunctor ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} i

/-- Evaluating `dualSourceCohomology` at a quasicoherent module gives the degree-`i`
cohomology of the canonical dual-tensor source. -/
theorem dualSourceCohomology_obj (i : ℤ) (F : Scheme.QCoh S) :
    (dualSourceCohomology f E G i).obj F =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((GlobalSections.toAbelian S.toRingedSpace).obj
          (DerivedTensor.Right.obj
            ((DerivedCategory.singleFunctor S.Modules 0).obj F.obj)
            (kernel f (MonoidalClosed.dual E) G))) := sorry

/-- Degree-`i` cohomology of the projection-formula target specialized to the canonical
dual of `E`, restricted to quasicoherent coefficients. -/
noncomputable def dualTargetCohomology (i : ℤ) :
    Scheme.QCoh S ⥤ AddCommGrpCat.{u} :=
  Scheme.QCoh.inclusion S ⋙ (target f (MonoidalClosed.dual E) G).toFunctor ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} i

/-- Evaluating `dualTargetCohomology` at a quasicoherent module gives the degree-`i`
cohomology of the canonical dual-tensor target. -/
theorem dualTargetCohomology_obj (i : ℤ) (F : Scheme.QCoh S) :
    (dualTargetCohomology f E G i).obj F =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((GlobalSections.toAbelian X.toRingedSpace).obj
          (DerivedTensor.Right.obj
            (DerivedCategory.Q.obj (coefficientComplex f G F.obj))
            (MonoidalClosed.dual E))) := sorry

/-- The derived internal-Hom target sending `F` to derived global sections of
`RHom(E, Q(G ⊗ f^*F))`. -/
noncomputable def internalHomTarget :
    S.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  coefficientComplexFunctor f G ⋙
    (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤
      RingedSpace.ModuleDerived X.toRingedSpace) ⋙
    (ihom E : RingedSpace.ModuleDerived X.toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace) ⋙
    GlobalSections.toAbelian X.toRingedSpace

/-- Evaluation of `internalHomTarget` gives the derived-global-sections model of Ext. -/
theorem internalHomTarget_obj (F : S.Modules) :
    (internalHomTarget f E G).obj F =
      (GlobalSections.toAbelian X.toRingedSpace).obj
        ((ihom E).obj (DerivedCategory.Q.obj (coefficientComplex f G F))) := sorry

/-- The dual-tensor target is canonically isomorphic to the derived internal-Hom target. -/
noncomputable def dualTargetInternalHomIso :
    (target f (MonoidalClosed.dual E) G).toFunctor ≅ internalHomTarget f E G :=
  NatIso.ofComponents
    (fun F ↦
      eqToIso (target_obj f (MonoidalClosed.dual E) G F) ≪≫
        (GlobalSections.toAbelian X.toRingedSpace).mapIso
          ((@Model.functorIsoTensorRight
              (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _
              (monoidalCategory X.toRingedSpace)
              (@kFlatTensorModel X (hasKFlatResolutions X) h_homotopy_tensor_X
                h_tensor_X h_tensor_X h_localization_X h_localization_X
                (homotopyLocalization_isLocalization X))
              (MonoidalClosed.dual E) _).app
                (DerivedCategory.Q.obj (coefficientComplex f G F)) ≪≫
            (@MonoidalClosed.Dual.tensorIsoIhom _ _ _ _ _ E
              hE.isRightDualizable.isIso_tensorIhomUnitToEnd).app
                (DerivedCategory.Q.obj (coefficientComplex f G F))) ≪≫
        (eqToIso (internalHomTarget_obj f E G F)).symm)
    (fun φ ↦ sorry)

/-- The component of `dualTargetInternalHomIso` is the canonical fixed-right tensor
comparison followed by the tensor-dual/internal-Hom comparison. -/
theorem dualTargetInternalHomIso_app (F : S.Modules) :
    (dualTargetInternalHomIso f E hE G).hom.app F =
      (eqToIso (target_obj f (MonoidalClosed.dual E) G F)).hom ≫
        (GlobalSections.toAbelian X.toRingedSpace).map
          ((@Model.functorIsoTensorRight
              (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _
              (monoidalCategory X.toRingedSpace)
              (@kFlatTensorModel X (hasKFlatResolutions X) h_homotopy_tensor_X
                h_tensor_X h_tensor_X h_localization_X h_localization_X
                (homotopyLocalization_isLocalization X))
              (MonoidalClosed.dual E) _).hom.app
                (DerivedCategory.Q.obj (coefficientComplex f G F)) ≫
            (@MonoidalClosed.Dual.tensorIsoIhom _ _ _ _ _ E
              hE.isRightDualizable.isIso_tensorIhomUnitToEnd).hom.app
                (DerivedCategory.Q.obj (coefficientComplex f G F))) ≫
        (eqToIso (internalHomTarget_obj f E G F)).inv := sorry

/-- The internal-Hom target equipped with connecting morphisms transported from the
dual-tensor target. -/
noncomputable def extTarget :
    DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u}) :=
  (target f (MonoidalClosed.dual E) G).transport
    (dualTargetInternalHomIso f E hE G)

/-- The projection-formula comparison with its target transported to derived internal Hom. -/
noncomputable def extComparison :
    source f (MonoidalClosed.dual E) G ⟶ extTarget f E hE G :=
  comparison f (MonoidalClosed.dual E) G ≫
    ((target f (MonoidalClosed.dual E) G).transportIso
      (dualTargetInternalHomIso f E hE G)).hom

/-- The degreewise projection-formula comparison for the canonical dual of `E`, natural in
quasicoherent coefficients. -/
noncomputable def dualCohomologyComparison (i : ℤ) :
    dualSourceCohomology f E G i ⟶ dualTargetCohomology f E G i :=
  Functor.whiskerLeft (Scheme.QCoh.inclusion S)
    (Functor.whiskerRight (comparison f (MonoidalClosed.dual E) G).app
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i))

/-- A component of `dualCohomologyComparison` is the cohomology map induced by the canonical
boundary-compatible projection-formula comparison. -/
theorem dualCohomologyComparison_app (i : ℤ) (F : Scheme.QCoh S) :
    (dualCohomologyComparison f E G i).app F =
      cohomologyMap (comparison f (MonoidalClosed.dual E) G) F.obj i := sorry

include hE hG_bounded

/-- Perfectness of `E` makes the dualized cohomology comparison invertible on every
quasicoherent coefficient. -/
theorem dualCohomologyComparison_isIso (i : ℤ) :
    IsIso (dualCohomologyComparison f E G i) := sorry

omit hG_bounded

/-- Degree-`i` cohomology of the internal-Hom target, restricted to quasicoherent
coefficients. -/
noncomputable def extCohomology (i : ℤ) :
    Scheme.QCoh S ⥤ AddCommGrpCat.{u} :=
  Scheme.QCoh.inclusion S ⋙ (extTarget f E hE G).toFunctor ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} i

/-- Evaluating `extCohomology` gives degree-`i` cohomology of derived global sections of
`RHom(E, Q(G ⊗ f^*F))`. -/
theorem extCohomology_obj (i : ℤ) (F : Scheme.QCoh S) :
    (extCohomology f E hE G i).obj F =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((GlobalSections.toAbelian X.toRingedSpace).obj
          ((ihom E).obj
            (DerivedCategory.Q.obj (coefficientComplex f G F.obj)))) := sorry

/-- The degreewise projection-formula comparison with derived internal-Hom target. -/
noncomputable def extCohomologyComparison (i : ℤ) :
    dualSourceCohomology f E G i ⟶ extCohomology f E hE G i :=
  Functor.whiskerLeft (Scheme.QCoh.inclusion S)
    (Functor.whiskerRight (extComparison f E hE G).app
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i))

include hG_bounded

/-- The degreewise comparison with derived internal-Hom target is invertible. -/
theorem extCohomologyComparison_isIso (i : ℤ) :
    IsIso (extCohomologyComparison f E hE G i) := sorry

/-- The degreewise projection-formula comparison commutes with the connecting maps of a
short exact sequence of quasicoherent modules. -/
theorem extCohomologyComparison_boundary
    (T : ShortComplex S.Modules) (hT : T.ShortExact)
    (hT₁ : T.X₁.IsQuasicoherent) (hT₂ : T.X₂.IsQuasicoherent)
    (hT₃ : T.X₃.IsQuasicoherent) (i : ℤ) :
    CommSq
      ((extCohomologyComparison f E hE G i).app ⟨T.X₃, hT₃⟩)
      (boundaryMap (source f (MonoidalClosed.dual E) G) hT i)
      (boundaryMap (extTarget f E hE G) hT i)
      ((extCohomologyComparison f E hE G (i + 1)).app ⟨T.X₁, hT₁⟩) := sorry

end ProjectionFormula
end ModuleDerived
end Scheme
end AlgebraicGeometry
