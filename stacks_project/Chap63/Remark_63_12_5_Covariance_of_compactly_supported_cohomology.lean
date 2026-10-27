/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport.Covariance
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Compactification Opposite
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

noncomputable section

universe u

section Covariance

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ]
variable {X Y : SchemeOverField k} (f : X ⟶ Y)
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsSeparated Y.hom] [Scheme.Hom.FiniteType Y.hom]
variable [IsSeparated f.left] [Scheme.Hom.QuasiFinite f.left]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
variable [CompactSpace (Spec (CommRingCat.of k))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of k))]
variable (C : CompDiagram ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom)
variable [IsOpenImmersion (Of.ι C.P_g)]
variable [Etale (Of.ι C.P_g)]
variable [IsSeparated (Of.ι C.P_g)]
variable [LocallyQuasiFinite (Of.ι C.P_g)]
variable [LocallyOfFiniteType (Of.ι C.P_g)]
variable [IsSeparated (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)]
variable [LocallyQuasiFinite (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)]
variable [LocallyOfFiniteType (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)]
variable [IsSeparated (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [LocallyQuasiFinite (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [LocallyOfFiniteType (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [IsSeparated
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [LocallyQuasiFinite
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [LocallyOfFiniteType
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]

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
  (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
    (ModuleCat.{u} Λ)]
variable [∀ U : (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).Etale,
  HasWeakSheafify
    ((CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
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
  (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
    AddCommGrpCat.{u}]
variable [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
variable [HasSheafify C.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).op.HasLeftKanExtension F]
variable [hC_compKanModule : ∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [hC_baseKanModule : ∀ F : Y.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).op.HasLeftKanExtension F]
variable [hC_compKanAdd : ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [hC_baseKanAdd : ∀ F : Y.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).op]
variable [hC_compPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op]
variable [hC_basePreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι C.P_g)).op]

variable [(etaleExtensionByZero (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (Of.ι C.P_g)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι C.P_g)
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι C.P_g)
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ))]

variable [((smallEtalePullback
    (CompDiagram.toBase ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toBase ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
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
    (CompDiagram.toComposite ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.toComposite ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [PreservesFiniteLimits
  ((smallEtalePullback
      (CompDiagram.toBase ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
    (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback
      (CompDiagram.toBase ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
    (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology)]
variable [(etaleModulePushforward
    (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).obj.right.hom Λ).Additive]
variable [HasWeakSheafify
  (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
    AddCommGrpCat.{u}]
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
variable [(Sheaf.smallEtaleInverseImage f.left (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f.left (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f.left (ModuleCat.{u} Λ))]

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

/- Remark 63.12.5 (Covariance of compactly supported cohomology) -/
@[stacks 0GKS] #check
  (AlgebraicGeometry.Scheme.Etale.gammaCompactSupportTrace (Λ := Λ) f C hw :
    ∀ (hΛ : AddMonoid.IsTorsion Λ) (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ))),
    (etaleDerivedGammaCompactSupport (Λ := Λ) (hX := (inferInstance : HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))))
      (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).obj
        ((etaleModuleDerivedInverseImage f.left Λ).obj K) ⟶
      (etaleDerivedGammaCompactSupport (Λ := Λ) (hX := (inferInstance : HasDerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)))) C.P_g).obj K)

/- Bounded-below torsion cohomology on the target is sufficient over any ring. -/
#check
  (AlgebraicGeometry.Scheme.Etale.gammaCompactSupportTrace_of_isGE_isTorsion (Λ := Λ) f C hw :
    ∀ (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K) (n : ℤ) (hGE : K.IsGE n),
    (etaleDerivedGammaCompactSupport (Λ := Λ) (hX := (inferInstance : HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))))
      (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).obj
        ((etaleModuleDerivedInverseImage f.left Λ).obj K) ⟶
      (etaleDerivedGammaCompactSupport (Λ := Λ) (hX := (inferInstance : HasDerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)))) C.P_g).obj K)

/- Constant coefficients give covariance on degree-zero constant module complexes. -/
#check
  (AlgebraicGeometry.Scheme.Etale.gammaCompactSupportTrace_const (Λ := Λ) f C hw :
    ∀ hΛ : AddMonoid.IsTorsion Λ,
    (etaleDerivedGammaCompactSupport (Λ := Λ) (hX := (inferInstance : HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))) (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).obj ((DerivedCategory.singleFunctor (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
      ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ))) ⟶
    (etaleDerivedGammaCompactSupport (Λ := Λ) (hX := (inferInstance : HasDerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)))) C.P_g).obj ((DerivedCategory.singleFunctor (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
      ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ))))

section Etale
variable [Etale f.left]

#check
  (AlgebraicGeometry.Scheme.Hom.fiberWeight_isPositiveWeighting f.left :
    f.left.IsWeighting f.left.fiberWeight ∧ ∀ x : X.left, 0 < f.left.fiberWeight x)

end Etale

section Flat
variable [Flat f.left] [LocallyOfFinitePresentation f.left]

#check
  (AlgebraicGeometry.Scheme.Hom.fiberWeight_isPositiveWeighting f.left :
    f.left.IsWeighting f.left.fiberWeight ∧ ∀ x : X.left, 0 < f.left.fiberWeight x)

end Flat

end Covariance

section Unibranch

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian Y]

/- Geometrically unibranch targets supply a nonnegative generic-separable-degree weighting. -/
#check
  (AlgebraicGeometry.Scheme.Hom.exists_genericSepDegreeWeighting f :
    Y.isGeometricallyUnibranch →
    ∃ w : X → ℕ, f.IsWeighting (fun x ↦ (w x : ℤ)) ∧
      ∀ x : X, RingHom.IsGenericSepDegree (f.stalkMap x).hom
        (LocallyOfFiniteType.stalkMap f x) (f.quasiFiniteAt x) (w x))

end Unibranch

section FieldExtension

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ]
variable {X Y : SchemeOverField k} (f : X ⟶ Y)
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsSeparated Y.hom] [Scheme.Hom.FiniteType Y.hom]
variable [IsSeparated f.left] [Scheme.Hom.QuasiFinite f.left]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
variable [CompactSpace (Spec (CommRingCat.of k))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of k))]
variable (C : CompDiagram ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom)
variable [IsOpenImmersion (Of.ι C.P_g)]
variable [Etale (Of.ι C.P_g)]
variable [IsSeparated (Of.ι C.P_g)]
variable [LocallyQuasiFinite (Of.ι C.P_g)]
variable [LocallyOfFiniteType (Of.ι C.P_g)]
variable [IsSeparated (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)]
variable [LocallyQuasiFinite (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)]
variable [LocallyOfFiniteType (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)]
variable [IsSeparated (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [LocallyQuasiFinite (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [LocallyOfFiniteType (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [IsSeparated
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [LocallyQuasiFinite
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]
variable [LocallyOfFiniteType
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))]

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
  (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
    (ModuleCat.{u} Λ)]
variable [∀ U : (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).Etale,
  HasWeakSheafify
    ((CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
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
  (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
    AddCommGrpCat.{u}]
variable [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
variable [HasSheafify C.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).op.HasLeftKanExtension F]
variable [hC_compKanModule : ∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [hC_baseKanModule : ∀ F : Y.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).op.HasLeftKanExtension F]
variable [hC_compKanAdd : ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [hC_baseKanAdd : ∀ F : Y.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).op]
variable [hC_compPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op]
variable [hC_basePreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι C.P_g)).op]

variable [(etaleExtensionByZero (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (Of.ι C.P_g)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι C.P_g)
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι C.P_g)
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.openImmersion ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))
    (ModuleCat.{u} Λ))]

variable [((smallEtalePullback
    (CompDiagram.toBase ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toBase ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
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
    (CompDiagram.toComposite ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.toComposite ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [PreservesFiniteLimits
  ((smallEtalePullback
      (CompDiagram.toBase ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
    (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback
      (CompDiagram.toBase ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
    (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology)]
variable [(etaleModulePushforward
    (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).obj.right.hom Λ).Additive]
variable [HasWeakSheafify
  (CompDiagram.interior ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).smallEtaleTopology
    AddCommGrpCat.{u}]
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
variable [(Sheaf.smallEtaleInverseImage f.left (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f.left (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f.left (ModuleCat.{u} Λ))]

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


variable {l : Type u} [Field l]
variable {X' Y' : SchemeOverField l} (f' : X' ⟶ Y')
variable [IsSeparated X'.hom] [Scheme.Hom.FiniteType X'.hom]
variable [IsSeparated Y'.hom] [Scheme.Hom.FiniteType Y'.hom]
variable [IsSeparated f'.left] [Scheme.Hom.QuasiFinite f'.left]
variable [CompactSpace X'.left] [QuasiSeparatedSpace X'.left]
variable [CompactSpace Y'.left] [QuasiSeparatedSpace Y'.left]
variable [CompactSpace (Spec (CommRingCat.of l))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of l))]
variable (C' : CompDiagram ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom)
variable [IsOpenImmersion (Of.ι C'.P_g)]
variable [Etale (Of.ι C'.P_g)]
variable [IsSeparated (Of.ι C'.P_g)]
variable [LocallyQuasiFinite (Of.ι C'.P_g)]
variable [LocallyOfFiniteType (Of.ι C'.P_g)]
variable [IsSeparated (CompDiagram.openImmersion ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')]
variable [LocallyQuasiFinite (CompDiagram.openImmersion ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')]
variable [LocallyOfFiniteType (CompDiagram.openImmersion ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')]
variable [IsSeparated (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))]
variable [LocallyQuasiFinite (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))]
variable [LocallyOfFiniteType (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))]
variable [IsSeparated
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))]
variable [LocallyQuasiFinite
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))]
variable [LocallyOfFiniteType
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))]

variable [HasSheafify X'.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X'.left.Etale,
  HasWeakSheafify (X'.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X'.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y'.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y'.left.Etale,
  HasWeakSheafify (Y'.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y'.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Spec (CommRingCat.of l)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [∀ U : (Spec (CommRingCat.of l)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of l)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of l)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify
  (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology
    (ModuleCat.{u} Λ)]
variable [∀ U : (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').Etale,
  HasWeakSheafify
    ((CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology
    (ModuleCat.{u} Λ))]
variable [HasSheafify C'.P_bar.obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [∀ U : C'.P_bar.obj.right.left.Etale,
  HasWeakSheafify (C'.P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf C'.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify C'.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : C'.P_g.obj.right.left.Etale,
  HasWeakSheafify (C'.P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf C'.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]

variable [HasSheafify X'.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify
  (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology
    AddCommGrpCat.{u}]
variable [HasSheafify C'.P_bar.obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
variable [HasSheafify C'.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [X'.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C'.P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C'.P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C'.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C'.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

variable [∀ F : X'.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).op.HasLeftKanExtension F]
variable [hCprime_compKanModule : ∀ F : X'.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))).op.HasLeftKanExtension F]
variable [hCprime_baseKanModule : ∀ F : Y'.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι C'.P_g)).op.HasLeftKanExtension F]
variable [∀ F : X'.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).op.HasLeftKanExtension F]
variable [hCprime_compKanAdd : ∀ F : X'.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))).op.HasLeftKanExtension F]
variable [hCprime_baseKanAdd : ∀ F : Y'.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι C'.P_g)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).op]
variable [hCprime_compPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))).op]
variable [hCprime_basePreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι C'.P_g)).op]

variable [(etaleExtensionByZero (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (Of.ι C'.P_g)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι C'.P_g)
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι C'.P_g)
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (CompDiagram.openImmersion ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.openImmersion ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.openImmersion ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))
    (ModuleCat.{u} Λ))]

variable [((smallEtalePullback
    (CompDiagram.toBase ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.left.smallEtaleTopology
      (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toBase ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.left.smallEtaleTopology
      (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback C'.P_bar.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) C'.P_g.obj.right.left.smallEtaleTopology
    C'.P_bar.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback C'.P_bar.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) C'.P_g.obj.right.left.smallEtaleTopology
      C'.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C'.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback C'.P_g.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (Spec (CommRingCat.of l)).smallEtaleTopology
    C'.P_g.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback C'.P_g.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of l)).smallEtaleTopology
      C'.P_g.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C'.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback
    (CompDiagram.toComposite ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of l)).smallEtaleTopology
      C'.P_bar.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.toComposite ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of l)).smallEtaleTopology
      C'.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C'.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [PreservesFiniteLimits
  ((smallEtalePullback
      (CompDiagram.toBase ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.left.smallEtaleTopology
    (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback
      (CompDiagram.toBase ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.left.smallEtaleTopology
    (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology)]
variable [(etaleModulePushforward
    (CompDiagram.ofInterior (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').obj.right.hom Λ).Additive]
variable [HasWeakSheafify
  (CompDiagram.interior ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').smallEtaleTopology
    AddCommGrpCat.{u}]
variable [HasWeakSheafify X'.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : Y'.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f'.left).op.HasLeftKanExtension P]
variable [∀ P : Y'.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f'.left).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f'.left).op]
variable [((smallEtalePullback f'.left).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.left.smallEtaleTopology
    X'.left.smallEtaleTopology).IsRightAdjoint]
variable [(Sheaf.smallEtaleInverseImage f'.left (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f'.left (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f'.left (ModuleCat.{u} Λ))]

variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections (Spec (CommRingCat.of l)).smallEtaleTopology
    (ModuleCat.{u} Λ)).obj
    (op (globalEtale (Spec (CommRingCat.of l))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of l)).smallEtaleTopology
        (ModuleCat.{u} Λ)).obj
      (op (globalEtale (Spec (CommRingCat.of l))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of l)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]


variable (s : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k))
variable (a : X'.left ⟶ X.left) (b : Y'.left ⟶ Y.left)
variable (hcart : IsPullback a f'.left f.left b)
variable (c : C'.P_bar.obj.right.left ⟶ C.P_bar.obj.right.left)
variable (d : C'.P_g.obj.right.left ⟶ C.P_g.obj.right.left)
variable (hpX : IsPullback c (CompDiagram.toComposite ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')
  (CompDiagram.toComposite ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C) s)
variable (hjX : IsPullback a (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))
  (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)) c)
variable (hpY : IsPullback d C'.P_g.obj.right.hom C.P_g.obj.right.hom s)
variable (hjY : IsPullback b (Of.ι C'.P_g) (Of.ι C.P_g) d)
variable [∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback s).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a).op.HasLeftKanExtension F]
variable [∀ F : Y.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b).op.HasLeftKanExtension F]
variable [∀ F : C.P_bar.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback c).op.HasLeftKanExtension F]
variable [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback d).op.HasLeftKanExtension F]
variable [∀ F : Y.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f'.left ≫ b)).op.HasLeftKanExtension F]
variable [∀ F : Y.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a ≫ f.left)).op.HasLeftKanExtension F]
variable [hcomp_structLeftKan : ∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (CompDiagram.toComposite ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C' ≫ s)).op.HasLeftKanExtension F]
variable [hcomp_structRightKan : ∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (c ≫ CompDiagram.toComposite ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C)).op.HasLeftKanExtension F]
variable [hbase_structLeftKan : ∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (C'.P_g.obj.right.hom ≫ s)).op.HasLeftKanExtension F]
variable [hbase_structRightKan : ∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (d ≫ C.P_g.obj.right.hom)).op.HasLeftKanExtension F]
variable [hcomp_openLeftKan : ∀ F : C.P_bar.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C') ≫ c)).op.HasLeftKanExtension F]
variable [hcomp_openRightKan : ∀ F : C.P_bar.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a ≫ Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [hbase_openLeftKan : ∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι C'.P_g ≫ d)).op.HasLeftKanExtension F]
variable [hbase_openRightKan : ∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (b ≫ Of.ι C.P_g)).op.HasLeftKanExtension F]
variable [haKanAdd : ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a).op.HasLeftKanExtension F]
variable [haPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a).op]
variable [hbKanAdd : ∀ F : Y.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b).op.HasLeftKanExtension F]
variable [hbPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b).op]
variable [hcKanAdd : ∀ F : C.P_bar.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback c).op.HasLeftKanExtension F]
variable [hcPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback c).op]
variable [hdKanAdd : ∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback d).op.HasLeftKanExtension F]
variable [hdPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback d).op]

variable [hC_basestructKan : ∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback C.P_g.obj.right.hom).op.HasLeftKanExtension F]
variable [hC_baseopenKan : ∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι C.P_g)).op.HasLeftKanExtension F]
variable [hCprime_basestructKan : ∀ F : (Spec (CommRingCat.of l)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback C'.P_g.obj.right.hom).op.HasLeftKanExtension F]
variable [hCprime_baseopenKan : ∀ F : C'.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι C'.P_g)).op.HasLeftKanExtension F]
variable [hC_compstructKan : ∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).obj.right.hom).op.HasLeftKanExtension F]
variable [hC_compopenKan : ∀ F : (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C))).op.HasLeftKanExtension F]
variable [hCprime_compstructKan : ∀ F : (Spec (CommRingCat.of l)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').obj.right.hom).op.HasLeftKanExtension F]
variable [hCprime_compopenKan : ∀ F : (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C').obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C'))).op.HasLeftKanExtension F]

variable {w : X.left → ℤ} (hw : f.left.IsWeighting w)
variable (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ)))

set_option maxHeartbeats 800000 in
/- Covariance commutes with ground-field extension in both coefficient domains. -/
#check
  (AlgebraicGeometry.Scheme.Etale.gammaCompactSupportTrace_baseChange
    (Λ := Λ) f C f' C' s a b hcart c d hpX hjX hpY hjY hw K :
    let baseChangeTarget := etaleDerivedGammaCompactSupportBaseChange
      (hP_structKan := hC_basestructKan)
      (hP_extensionKanModule := hC_baseKanModule)
      (hP_extensionKanAdd := hC_baseKanAdd)
      (hP_extensionPreservesKan := hC_basePreservesKan)
      (hQ_extensionKanModule := hCprime_baseKanModule)
      (hQ_extensionKanAdd := hCprime_baseKanAdd)
      (hQ_extensionPreservesKan := hCprime_basePreservesKan)
      (hsourceKanAdd := hbKanAdd)
      (hsourcePreservesKan := hbPreservesKan)
      (hambientKanAdd := hdKanAdd)
      (hambientPreservesKan := hdPreservesKan)
      (hopenLeftKan := hbase_openLeftKan)
      (hopenRightKan := hbase_openRightKan)
      (hstructLeftKan := hbase_structLeftKan)
      (hstructRightKan := hbase_structRightKan)
      (hP_openKan := hC_baseopenKan)
      (hQ_structKan := hCprime_basestructKan)
      (hQ_openKan := hCprime_baseopenKan)
      (X := Y) (X' := Y')
        (hX := (inferInstance : HasDerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ))))
        (hXprime := (inferInstance : HasDerivedCategory (Sheaf Y'.left.smallEtaleTopology (ModuleCat.{u} Λ)))) Λ C.P_g C'.P_g s b d hpY hjY K
    let baseChangeSource := etaleDerivedGammaCompactSupportBaseChange
      (hP_structKan := hC_compstructKan)
      (hP_extensionKanModule := hC_compKanModule)
      (hP_extensionKanAdd := hC_compKanAdd)
      (hP_extensionPreservesKan := hC_compPreservesKan)
      (hQ_extensionKanModule := hCprime_compKanModule)
      (hQ_extensionKanAdd := hCprime_compKanAdd)
      (hQ_extensionPreservesKan := hCprime_compPreservesKan)
      (hsourceKanAdd := haKanAdd)
      (hsourcePreservesKan := haPreservesKan)
      (hambientKanAdd := hcKanAdd)
      (hambientPreservesKan := hcPreservesKan)
      (hopenLeftKan := hcomp_openLeftKan)
      (hopenRightKan := hcomp_openRightKan)
      (hstructLeftKan := hcomp_structLeftKan)
      (hstructRightKan := hcomp_structRightKan)
      (hP_openKan := hC_compopenKan)
      (hQ_structKan := hCprime_compstructKan)
      (hQ_openKan := hCprime_compopenKan)
      (X := ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left ≫ Y.hom } : SchemeOverField k)) (X' := ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left ≫ Y'.hom } : SchemeOverField l))
      (hX := (inferInstance : HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))))
      (hXprime := (inferInstance : HasDerivedCategory (Sheaf X'.left.smallEtaleTopology (ModuleCat.{u} Λ)))) Λ (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f.left)) ({ left := X.left, right := ⟨⟨⟩⟩, hom := f.left } : Over Y.left) Y.hom C) (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C') s a c hpX hjX
      ((etaleModuleDerivedInverseImage f.left Λ).obj K)
    let inverseImageComparison := (etaleDerivedGammaCompactSupport (Λ := Λ) (hX := (inferInstance : HasDerivedCategory (Sheaf X'.left.smallEtaleTopology (ModuleCat.{u} Λ)))) (CompDiagram.ofComposite (h_f_separated := (inferInstance : IsSeparated f'.left)) (h_f_finiteType := (inferInstance : Scheme.Hom.FiniteType f'.left)) ({ left := X'.left, right := ⟨⟨⟩⟩, hom := f'.left } : Over Y'.left) Y'.hom C')).map
        ((etaleModuleDerivedInverseImage_square f.left b f'.left a hcart Λ).inv.app K)
    (∀ hΛ : AddMonoid.IsTorsion Λ,
    gammaCompactSupportTrace (Λ := Λ) f C hw hΛ K ≫
      baseChangeTarget =
    baseChangeSource ≫
    inverseImageComparison ≫
    gammaCompactSupportTrace (Λ := Λ) f' C' (w := fun x' ↦ w (a x')) (IsWeighting.of_isPullback (w := w) hw hcart) hΛ
      ((etaleModuleDerivedInverseImage b Λ).obj K)) ∧
    (∀ (hT : etaleDerivedIsTorsion K) (n : ℤ) (hGE : K.IsGE n),
    gammaCompactSupportTrace_of_isGE_isTorsion (Λ := Λ) f C hw K hT n hGE ≫
      baseChangeTarget =
    baseChangeSource ≫
    inverseImageComparison ≫
    gammaCompactSupportTrace_of_isGE_isTorsion (Λ := Λ) f' C' (w := fun x' ↦ w (a x')) (IsWeighting.of_isPullback (w := w) hw hcart)
      ((etaleModuleDerivedInverseImage b Λ).obj K)
      (etaleModuleDerivedInverseImage_isTorsion b Λ K hT) n
      (etaleModuleDerivedInverseImage_isGE b Λ K n (hK := hGE))))

end FieldExtension

end
