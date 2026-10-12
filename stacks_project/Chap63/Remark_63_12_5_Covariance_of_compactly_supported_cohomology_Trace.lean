/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.FiberLength
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.GenericSeparableDegree
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import stacks_project.Chap63.Lemma_63_5_2
public import stacks_project.Chap63.Lemma_63_7_1_Adjunction
public import stacks_project.Chap63.Remark_63_12_5_Covariance_of_compactly_supported_cohomology_Comparison

/-!
# Compactly supported covariance traces

The maps `RΓ_c(X, f⁻¹ K) ⟶ RΓ_c(Y, K)` induced by a weighting trace
`Tr_{f, w, K}`, together with the fibre-weight and constant-coefficient
specializations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ExactFunctor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Compactification
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

-- Local instance justification (search instability): obtain weak sheafification from the existing strong sheafification before matching over-site families.
attribute [local instance 10000] HasSheafify.isRightAdjoint
open etaleDerivedLowerShriek

section CovarianceTrace

variable {k : Type u} [Field k] {Λ : Type u} [CommRing Λ]
variable {X Y : SchemeOverField k} (f : X ⟶ Y)
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsSeparated Y.hom] [Scheme.Hom.FiniteType Y.hom]
variable [IsSeparated f.left] [Scheme.Hom.QuasiFinite f.left]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
variable [CompactSpace (Spec (CommRingCat.of k))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of k))]
variable (C : CompDiagram (Over.mk f.left) Y.hom)
variable [IsFinite
  (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.hom]

variable [IsOpenImmersion (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
variable [Etale (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
variable [IsSeparated (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
variable [LocallyQuasiFinite (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
variable [LocallyOfFiniteType (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
variable [IsSeparated (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
variable [LocallyQuasiFinite (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
variable [LocallyOfFiniteType (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
variable [IsSeparated (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)]
variable [LocallyQuasiFinite (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)]
variable [LocallyOfFiniteType (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)]
variable [IsSeparated
  (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
    CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
variable [LocallyQuasiFinite
  (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
    CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
variable [LocallyOfFiniteType
  (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
    CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]

variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.left.Etale,
  HasWeakSheafify (Y.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [∀ U : (Spec (CommRingCat.of k)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify
  (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
    (ModuleCat.{u} Λ)]
variable [∀ U : (CompDiagram.interior (Over.mk f.left) Y.hom C).Etale,
  HasWeakSheafify
    ((CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
    (ModuleCat.{u} Λ))]
variable [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [∀ U : C.P_bar.obj.right.left.Etale,
  HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : C.P_g.obj.right.left.Etale,
  HasWeakSheafify (C.P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]

variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify
  (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
    AddCommGrpCat.{u}]
variable [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
variable [HasSheafify C.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior (Over.mk f.left) Y.hom C).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
variable [∀ F : Y.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.ιBase (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior (Over.mk f.left) Y.hom C).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
variable [∀ F : Y.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.ιBase (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.ιBase (Over.mk f.left) Y.hom C)).op]

variable [(etaleExtensionByZero (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (CompDiagram.ιBase (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.ιBase (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.ιBase (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]

variable [((smallEtalePullback
    (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback C.P_bar.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
    C.P_bar.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback C.P_bar.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback C.P_g.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
    C.P_g.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback C.P_g.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_g.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback
    (CompDiagram.toComposite (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.toComposite (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [PreservesFiniteLimits
  ((smallEtalePullback
      (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
    (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback
      (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
    (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology)]
variable [(etaleModulePushforward
    (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.hom Λ).Additive]
variable [HasWeakSheafify
  (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
    AddCommGrpCat.{u}]
variable [((@etaleDerivedLowerShriek Y.left (Over.mk f.left) Λ inferInstance
    (CompDiagram.ofInterior (Over.mk f.left) Y.hom C)
    inferInstance inferInstance inferInstance
    (instHasSheafify_ofInterior_Module_cov (Λ := Λ) f C) inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (instHasLeftKanExtension_ofInterior_ι_Module_cov (Λ := Λ) f C)
    (instAdditive_ofInterior_ι_cov (Λ := Λ) f C)
    (instPreservesFiniteLimits_ofInterior_ι_cov (Λ := Λ) f C)
    (instPreservesFiniteColimits_ofInterior_ι_cov (Λ := Λ) f C)
    (instAdditive_ofInterior_hom_cov (Λ := Λ) f C)
    (instHasRightDerived_ofInterior_hom_cov (Λ := Λ) f C) :
      EtaleDerived X.left Λ ⥤ EtaleDerived Y.left Λ)).IsLeftAdjoint]

variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : Y.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f.left).op.HasLeftKanExtension P]
variable [∀ P : Y.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f.left).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f.left).op]
variable [((smallEtalePullback f.left).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
    X.left.smallEtaleTopology).IsRightAdjoint]
variable [(etaleModuleSheafPullback f.left Λ).Additive]
variable [PreservesFiniteLimits (etaleModuleSheafPullback f.left Λ)]
variable [PreservesFiniteColimits (etaleModuleSheafPullback f.left Λ)]

variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
    (ModuleCat.{u} Λ)).obj
    (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} Λ)).obj
      (op (globalEtale (Spec (CommRingCat.of k))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

variable {w : X.left → ℤ} (hw : f.left.IsWeighting w)

/-- Forgotten abelian form of the `Λ`-linear weighting trace, before lifting
coefficients. -/
def gammaCompactSupport_weightingTraceModuleForgetHom
    (F : Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.left.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule f.left Λ).obj
          ((etaleModuleSheafPullback f.left Λ).obj F)) ⟶
      (sheafCompose Y.left.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F :=
  (lowerShriekModule_forget f.left Λ
      ((etaleModuleSheafPullback f.left Λ).obj F)).hom ≫
    (lowerShriek f.left).map
      ((etaleModuleSheafPullback_compSheafComposeIso f.left Λ).hom.app F) ≫
    weightingTrace f.left hw (etaleModuleForget Λ F)

/-- The sheaf-level `Λ`-linear weighting trace at a sheaf of modules. -/
def gammaCompactSupport_weightingTraceModuleHom
    (F : Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule f.left Λ).obj ((etaleModuleSheafPullback f.left Λ).obj F) ⟶
      F :=
  liftModuleSheafHom (gammaCompactSupport_weightingTraceModuleForgetHom f hw F)

/-- The `Λ`-linear weighting trace as a natural transformation
`f_! ∘ f⁻¹ ⟶ 𝟭` on étale sheaves of modules. -/
def gammaCompactSupport_weightingTraceModuleNatTrans :
    etaleModuleSheafPullback f.left Λ ⋙ lowerShriekModule f.left Λ ⟶
      𝟭 (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)) where
  app F := gammaCompactSupport_weightingTraceModuleHom f hw F
  naturality := sorry

/-- Derived natural transformation of the weighting trace, obtained by
`ExactFunctor.MapDerivedCategory.map` of the sheaf-level module trace. -/
def gammaCompactSupport_weightingTraceDerivedNatTrans :
    etaleModuleDerivedInverseImage f.left Λ ⋙ lowerShriekModuleDerived f.left Λ ⟶
      𝟭 (EtaleDerived Y.left Λ) :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of (etaleModuleSheafPullback f.left Λ))
        (ExactFunctor.of (lowerShriekModule f.left Λ))).inv ≫
    ExactFunctor.MapDerivedCategory.map
      (ObjectProperty.homMk (gammaCompactSupport_weightingTraceModuleNatTrans f hw) :
        (ExactFunctor.of (etaleModuleSheafPullback f.left Λ)).comp
            (ExactFunctor.of (lowerShriekModule f.left Λ)) ⟶
          ExactFunctor.id
            (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
    (ExactFunctor.MapDerivedCategory.idFunctorIso
      (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ))).hom

/-- Derived trace `Tr_{f, w, K} : f_! f⁻¹ K ⟶ K` on `D(Y_étale, Λ)`, assembled
from the sheaf-level weighting trace of Lemma 63.5.2. This is the
clash-forced stand-in for `weightingTraceDerived` from Lemma 63.5.3:
importing that lemma beside Comparison duplicates
`sheafCompose_map_liftModuleSheafHom`. It is used only to implement the
covariance maps, not as a new Section 63.5 owner. -/
def gammaCompactSupport_weightingTraceDerived (K : EtaleDerived Y.left Λ) :
    (lowerShriekModuleDerived f.left Λ).obj
        ((etaleModuleDerivedInverseImage f.left Λ).obj K) ⟶ K :=
  (gammaCompactSupport_weightingTraceDerivedNatTrans f hw).app K

/-- The objectwise derived trace is the component of
`gammaCompactSupport_weightingTraceDerivedNatTrans`. -/
theorem gammaCompactSupport_weightingTraceDerived_eq
    (K : EtaleDerived Y.left Λ) :
    gammaCompactSupport_weightingTraceDerived f hw K =
      (gammaCompactSupport_weightingTraceDerivedNatTrans f hw).app K :=
  sorry

/-- The map `RΓ_c(Y, f_! f⁻¹ K) ⟶ RΓ_c(Y, K)` obtained by applying
`RΓ_c(Y, -)` to the derived weighting trace `Tr_{f, w, K}`. -/
def gammaCompactSupportTraceMap (K : EtaleDerived Y.left Λ) :
    (gammaCompactSupport_baseGamma f C).obj
        ((lowerShriekModuleDerived f.left Λ).obj
          ((etaleModuleDerivedInverseImage f.left Λ).obj K)) ⟶
      (gammaCompactSupport_baseGamma f C).obj K :=
  (gammaCompactSupport_baseGamma f C).map
    (gammaCompactSupport_weightingTraceDerived f hw K)

/-- Unfolding `gammaCompactSupportTraceMap` recovers `RΓ_c(Y, -)` of
`weightingTraceDerived`. -/
theorem gammaCompactSupportTraceMap_eq (K : EtaleDerived Y.left Λ) :
    gammaCompactSupportTraceMap f C hw K =
      (gammaCompactSupport_baseGamma f C).map
        (gammaCompactSupport_weightingTraceDerived f hw K) :=
  sorry

/-- Covariance morphism `RΓ_c(X, f⁻¹ K) ⟶ RΓ_c(Y, K)` on a torsion coefficient
ring, obtained as the composite of the identification
`RΓ_c(X, f⁻¹ K) ≅ RΓ_c(Y, f_! f⁻¹ K)` with `RΓ_c(Y, Tr_{f, w, K})`. -/
def gammaCompactSupportTrace (hΛ : AddMonoid.IsTorsion Λ)
    (K : EtaleDerived Y.left Λ) :
    (gammaCompactSupport_compositeGamma f C).obj
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) ⟶
      (gammaCompactSupport_baseGamma f C).obj K :=
  (gammaCompactSupport_pullbackIso f C hΛ K).hom ≫
    gammaCompactSupportTraceMap f C hw K

/-- Unfolding `gammaCompactSupportTrace` recovers the composite of the
pullback identification with `gammaCompactSupportTraceMap`. -/
theorem gammaCompactSupportTrace_eq (hΛ : AddMonoid.IsTorsion Λ)
    (K : EtaleDerived Y.left Λ) :
    gammaCompactSupportTrace f C hw hΛ K =
      (gammaCompactSupport_pullbackIso f C hΛ K).hom ≫
        gammaCompactSupportTraceMap f C hw K :=
  sorry

/-- Covariance morphism `RΓ_c(X, f⁻¹ K) ⟶ RΓ_c(Y, K)` on objects of
`D⁺_tors(Y_étale, Λ)`, using the objectwise composition identification. -/
def gammaCompactSupportTrace_of_isGE_isTorsion (K : EtaleDerived Y.left Λ)
    (h_tors : etaleDerivedIsTorsion
      ((etaleModuleDerivedInverseImage f.left Λ).obj K))
    (n : ℤ)
    (hGE : DerivedCategory.IsGE
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) n) :
    (gammaCompactSupport_compositeGamma f C).obj
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) ⟶
      (gammaCompactSupport_baseGamma f C).obj K :=
  (gammaCompactSupport_pullbackIso_of_isGE_isTorsion f C K h_tors n hGE).hom ≫
    gammaCompactSupportTraceMap f C hw K

/-- Unfolding the `D⁺_tors` covariance map recovers the corresponding
pullback identification composite. -/
theorem gammaCompactSupportTrace_of_isGE_isTorsion_eq (K : EtaleDerived Y.left Λ)
    (h_tors : etaleDerivedIsTorsion
      ((etaleModuleDerivedInverseImage f.left Λ).obj K))
    (n : ℤ)
    (hGE : DerivedCategory.IsGE
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) n) :
    gammaCompactSupportTrace_of_isGE_isTorsion f C hw K h_tors n hGE =
      (gammaCompactSupport_pullbackIso_of_isGE_isTorsion f C K h_tors n hGE).hom ≫
        gammaCompactSupportTraceMap f C hw K :=
  sorry

/-- Functoriality of the torsion-ring covariance morphism in `K`. -/
theorem gammaCompactSupportTrace_natural (hΛ : AddMonoid.IsTorsion Λ)
    {K L : EtaleDerived Y.left Λ} (η : K ⟶ L) :
    (gammaCompactSupport_compositeGamma f C).map
        ((etaleModuleDerivedInverseImage f.left Λ).map η) ≫
      gammaCompactSupportTrace f C hw hΛ L =
    gammaCompactSupportTrace f C hw hΛ K ≫
      (gammaCompactSupport_baseGamma f C).map η :=
  sorry

/-- Fibre-weight specialization of `gammaCompactSupportTrace` for étale or
flat locally quasi-finite locally finitely presented morphisms. -/
def gammaCompactSupportTrace_ofFiberWeight
    [Flat f.left] [LocallyOfFinitePresentation f.left]
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived Y.left Λ) :
    (gammaCompactSupport_compositeGamma f C).obj
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) ⟶
      (gammaCompactSupport_baseGamma f C).obj K :=
  gammaCompactSupportTrace f C
    (fiberWeight_isPositiveWeighting f.left).1 hΛ K

/-- The fibre-weight covariance map is `gammaCompactSupportTrace` at
`f.left.fiberWeight`. -/
theorem gammaCompactSupportTrace_ofFiberWeight_eq
    [Flat f.left] [LocallyOfFinitePresentation f.left]
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived Y.left Λ) :
    gammaCompactSupportTrace_ofFiberWeight f C hΛ K =
      gammaCompactSupportTrace f C
        (fiberWeight_isPositiveWeighting f.left).1 hΛ K :=
  sorry

/-- Comparison `f⁻¹ underline Λ ⟶ underline Λ` of constant étale sheaves of
modules, obtained from sheafification of the constant presheaf and the
small-étale sheaf-pullback adjunction. -/
def etaleConstantModulePullbackHom :
    (etaleModuleSheafPullback f.left Λ).obj
        ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (ModuleCat.of Λ Λ)) ⟶
      (constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ Λ) :=
  (((smallEtalePullback f.left).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
        Y.left.smallEtaleTopology X.left.smallEtaleTopology).homEquiv
      ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ Λ))
      ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ Λ))).symm
    (((sheafificationAdjunction Y.left.smallEtaleTopology
          (ModuleCat.{u} Λ)).homEquiv
        ((Functor.const Y.left.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))
        (((smallEtalePullback f.left).sheafPushforwardContinuous
            (ModuleCat.{u} Λ)
            Y.left.smallEtaleTopology X.left.smallEtaleTopology).obj
          ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (ModuleCat.of Λ Λ)))).symm
      ((Functor.constCompWhiskeringLeftIso (Y.left.Etaleᵒᵖ)
          (C := ModuleCat.{u} Λ)
          (smallEtalePullback f.left).op).inv.app (ModuleCat.of Λ Λ) ≫
        Functor.whiskerLeft (smallEtalePullback f.left).op
          ((sheafificationAdjunction X.left.smallEtaleTopology
              (ModuleCat.{u} Λ)).unit.app
            ((Functor.const X.left.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ)))))

/-- The constant-module comparison is an isomorphism. -/
instance isIso_etaleConstantModulePullbackHom :
    IsIso
      (etaleConstantModulePullbackHom f :
        (etaleModuleSheafPullback f.left Λ).obj
            ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
              (ModuleCat.of Λ Λ)) ⟶
          (constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (ModuleCat.of Λ Λ)) :=
  sorry

/-- Inverse image of the constant sheaf of `Λ`-modules is the constant sheaf. -/
def etaleConstantModulePullbackIso :
    (etaleModuleSheafPullback f.left Λ).obj
        ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (ModuleCat.of Λ Λ)) ≅
      (constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ Λ) :=
  asIso
    (etaleConstantModulePullbackHom f :
      (etaleModuleSheafPullback f.left Λ).obj
          ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (ModuleCat.of Λ Λ)) ⟶
        (constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (ModuleCat.of Λ Λ))

/-- Derived identification `f⁻¹ Λ[0] ≅ Λ[0]`. -/
def etaleConstantModuleDerivedPullbackIso :
    (etaleModuleDerivedInverseImage f.left Λ).obj
        ((DerivedCategory.singleFunctor
            (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
          ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (ModuleCat.of Λ Λ))) ≅
      (DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
        ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (ModuleCat.of Λ Λ)) :=
  ((etaleModuleSheafPullback f.left Λ).mapDerivedCategorySingleFunctor (0 : ℤ)).app
      ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ Λ)) ≪≫
    (DerivedCategory.singleFunctor
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).mapIso
      (etaleConstantModulePullbackIso f)

/-- The derived constant-sheaf comparison is `mapDerivedCategorySingleFunctor`
followed by `singleFunctor` of `etaleConstantModulePullbackIso`. -/
theorem etaleConstantModuleDerivedPullbackIso_hom :
    (etaleConstantModuleDerivedPullbackIso f).hom =
      ((etaleModuleSheafPullback f.left Λ).mapDerivedCategorySingleFunctor
          (0 : ℤ)).hom.app
          ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (ModuleCat.of Λ Λ)) ≫
        (DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).map
          (etaleConstantModulePullbackIso f).hom :=
  sorry

/-- The constant-coefficient covariance arrow
`Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ)` on a torsion coefficient ring. The source
also records that this map is compatible with ground-field extensions, but
does not specify a comparison morphism. -/
def gammaCompactSupportTrace_const (hΛ : AddMonoid.IsTorsion Λ) :
    (gammaCompactSupport_compositeGamma f C).obj
      ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
        ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (ModuleCat.of Λ Λ))) ⟶
      (gammaCompactSupport_baseGamma f C).obj
        ((DerivedCategory.singleFunctor
            (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
          ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (ModuleCat.of Λ Λ))) :=
  (gammaCompactSupport_compositeGamma f C).map
      (etaleConstantModuleDerivedPullbackIso f).inv ≫
    gammaCompactSupportTrace f C hw hΛ
      ((DerivedCategory.singleFunctor
          (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
        ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (ModuleCat.of Λ Λ)))

/-- The constant-coefficient map is the general covariance trace on constants,
transported along `f⁻¹ Λ ≅ Λ`. -/
theorem gammaCompactSupportTrace_const_eq (hΛ : AddMonoid.IsTorsion Λ) :
    gammaCompactSupportTrace_const f C hw hΛ =
      (gammaCompactSupport_compositeGamma f C).map
          (etaleConstantModuleDerivedPullbackIso f).inv ≫
        gammaCompactSupportTrace f C hw hΛ
          ((DerivedCategory.singleFunctor
              (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
            ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
              (ModuleCat.of Λ Λ))) :=
  sorry

end CovarianceTrace

end AlgebraicGeometry.Scheme.Etale

end
