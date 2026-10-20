/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Lemma_63_8_5_Comparison
public import stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_9_4_Cartesian
public import stacks_project.Chap63.Lemma_63_9_4_Transport
public import stacks_project.Chap63.Lemma_63_9_4_DerivedSites
public import stacks_project.Chap63.Lemma_63_9_4_StackedTransport

/-!
# Derived étale lower shriek base change

Canonical comparison `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of compactification
models attached to a cartesian square, assembled from proper base change of
`R f̄_*` and compact-support base change of `j_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

-- Prefer the canonical projection while elaborating the concrete diagram context.
-- Local instance justification (search instability): Use the given strong sheafification projection ahead of slice-site search in this diagram context.
attribute [local instance 10000] HasSheafify.isRightAdjoint

section Stacked

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g)
  {X' Y' Z' : Scheme.{u}}
  (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
  (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X.left)
  (h_upper : IsPullback c f' X.hom b) (h_lower : IsPullback b g' g a)
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [IsSeparated g'] [Scheme.Hom.FiniteType g']
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  [CompactSpace Z'] [QuasiSeparatedSpace Z']
  (Λ : Type u) [CommRing Λ]

  [IsOpenImmersion (CompDiagram.ιBase X g C)]
  [Etale (CompDiagram.ιBase X g C)]
  [IsSeparated (CompDiagram.ιBase X g C)]
  [LocallyQuasiFinite (CompDiagram.ιBase X g C)]
  [LocallyOfFiniteType (CompDiagram.ιBase X g C)]
  [IsSeparated (CompDiagram.openImmersion X g C)]
  [LocallyQuasiFinite (CompDiagram.openImmersion X g C)]
  [LocallyOfFiniteType (CompDiagram.openImmersion X g C)]
  [IsSeparated (CompDiagram.ιInterior X g C)]
  [LocallyQuasiFinite (CompDiagram.ιInterior X g C)]
  [LocallyOfFiniteType (CompDiagram.ιInterior X g C)]
  [IsSeparated (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)]
  [LocallyQuasiFinite
  (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)]
  [LocallyOfFiniteType
  (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)]

  [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Z'.Etale,
  HasWeakSheafify (Z'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.interior X g C).Etale,
  HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : C.P_bar.obj.right.left.Etale,
  HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : C.P_g.obj.right.left.Etale,
  HasWeakSheafify (C.P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]

  [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify C.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (CompDiagram.interior X g C).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose C.P_bar.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose C.P_g.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.interior X g C).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.ιInterior X g C)).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior X g C).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.ιBase X g C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.ιInterior X g C)).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior X g C).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.ιBase X g C)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.ιInterior X g C)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion X g C)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.ιBase X g C)).op]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a).op.HasLeftKanExtension F]

  [(etaleExtensionByZero (CompDiagram.ιInterior X g C)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.ιInterior X g C) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.ιInterior X g C) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (CompDiagram.openImmersion X g C)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.openImmersion X g C) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.openImmersion X g C) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero
    (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero
    (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)
    (ModuleCat.{u} Λ))]

  [((smallEtalePullback (CompDiagram.toBase X g C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    (CompDiagram.interior X g C).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toBase X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (CompDiagram.interior X g C).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback C.P_bar.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
    C.P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback C.P_bar.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback C.P_g.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z.smallEtaleTopology
    C.P_g.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback C.P_g.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      C.P_g.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback (CompDiagram.toComposite X g C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z.smallEtaleTopology
    C.P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toComposite X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

  [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafCompose X'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Z'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Z'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback c).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback c).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback c).op]

  [(etaleModulePushforward (CompDiagram.toBase X g C) Λ).Additive]
  [(etaleModulePushforward C.P_bar.obj.right.hom Λ).Additive]
  [(etaleModulePushforward C.P_g.obj.right.hom Λ).Additive]
  [(etaleModulePushforward (CompDiagram.toComposite X g C) Λ).Additive]
  [(etaleModulePushforward C.P_bar.obj.right.hom Λ ⋙
    etaleModulePushforward C.P_g.obj.right.hom Λ).Additive]
  [(etaleModulePushforward (CompDiagram.toBase X g C) Λ ⋙
    lowerShriekModule (CompDiagram.ιBase X g C) Λ).Additive]
  [(lowerShriekModule (CompDiagram.openImmersion X g C) Λ ⋙
    etaleModulePushforward C.P_bar.obj.right.hom Λ).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward (CompDiagram.toBase X g C) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward C.P_bar.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward C.P_g.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (CompDiagram.toComposite X g C) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward C.P_bar.obj.right.hom Λ ⋙
      etaleModulePushforward C.P_g.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (CompDiagram.toBase X g C) Λ ⋙
      lowerShriekModule (CompDiagram.ιBase X g C) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (lowerShriekModule (CompDiagram.openImmersion X g C) Λ ⋙
      etaleModulePushforward C.P_bar.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]


variable [HasSheafify
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).Etale,
  HasWeakSheafify
    ((ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)).smallEtaleTopology
    (ModuleCat.{u} Λ))]
  [HasSheafify
  (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify
  (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (ambient g a g' b h_lower C.P_g).Etale,
  HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).Etale,
  HasWeakSheafify
    ((ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
    (ModuleCat.{u} Λ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (CompDiagram.ofComposite X g C).obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [(etaleModulePushforward
    (CompDiagram.ofComposite X g C).obj.right.hom Λ).Additive]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (interiorLift g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (interiorLift g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk X.hom).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk X.hom).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [(CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient g a g' b h_lower C.P_g).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.ofComposite X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
          (CompDiagram.ofComposite X g C))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)).smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (ambientToBase g a g' b h_lower C.P_g)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (ambient g a g' b h_lower C.P_g).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [(etaleExtensionByZero
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (interiorLift g a g' b h_lower C.P_g)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (interiorLift g a g' b h_lower C.P_g) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (interiorLift g a g' b h_lower C.P_g) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (Of.ι (ofInteriorHom X g C)) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι (ofInteriorHom X g C)) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι (ofInteriorHom X g C)) (ModuleCat.{u} Λ))]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (interiorLift g a g' b h_lower C.P_g)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (ofInteriorHom X g C))).op]

  [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafCompose Z.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose (ambient g a g' b h_lower C.P_g).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafify
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafify
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [((smallEtalePullback (ambientToBase g a g' b h_lower C.P_g)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z'.smallEtaleTopology
    (ambient g a g' b h_lower C.P_g).smallEtaleTopology).Additive]
  [((smallEtalePullback
        (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology).Additive]
  [((smallEtalePullback
        (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
          (CompDiagram.ofComposite X g C))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)).smallEtaleTopology).Additive]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback C.P_g.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToSource g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase g a g' b h_lower C.P_g ≫ a)).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource g a g' b h_lower C.P_g ≫ C.P_g.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι C.P_g)).op.HasLeftKanExtension F]
  [∀ F : (ambient g a g' b h_lower C.P_g).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (interiorLift g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift g a g' b h_lower C.P_g ≫
      ambientToSource g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (b ≫ Of.ι C.P_g)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk g).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (b : Y' ⟶ (Over.mk g).left)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (CompDiagram.toBase X g C)).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C) ≫ b)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C) ≫
      (ofInteriorHom X g C).obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C) ≫
      ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (c ≫ Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk X.hom).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (c : X' ⟶ (Over.mk X.hom).left)).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (CompDiagram.ofComposite X g C).obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C) ≫ a)).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C) ≫
      (CompDiagram.ofComposite X g C).obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C) ≫
      ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback
    (c ≫ Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (c : X' ⟶ (Over.mk (X.hom ≫ g)).left)).op.HasLeftKanExtension F]
  [(etaleModulePushforward C.P_g.obj.right.hom Λ ⋙
    etaleModuleSheafPullback a Λ).Additive]
  [(etaleModuleSheafPullback (ambientToSource g a g' b h_lower C.P_g) Λ ⋙
    etaleModulePushforward (ambientToBase g a g' b h_lower C.P_g) Λ).Additive]
  [(etaleModulePushforward (ambientToBase g a g' b h_lower C.P_g) Λ).Additive]
  [(etaleModulePushforward (ofInteriorHom X g C).obj.right.hom Λ ⋙
    etaleModuleSheafPullback b Λ).Additive]
  [(etaleModuleSheafPullback
      (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C)) Λ ⋙
    etaleModulePushforward
      (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C)) Λ).Additive]
  [(etaleModulePushforward
    (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C)) Λ).Additive]
  [(etaleModulePushforward (CompDiagram.ofComposite X g C).obj.right.hom Λ ⋙
    etaleModuleSheafPullback a Λ).Additive]
  [(etaleModuleSheafPullback
      (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)) Λ ⋙
    etaleModulePushforward
      (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)) Λ).Additive]
  [(etaleModulePushforward
    (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)) Λ).Additive]

  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (ambientToSource g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk g).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (b : Y' ⟶ (Over.mk g).left)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (ambientToSource g a g' b h_lower C.P_g)).op]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback
    (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk X.hom).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (c : X' ⟶ (Over.mk X.hom).left)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback
    (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C))).op]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    AddCommGrpCat.{u},
  (smallEtalePullback
    (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (c : X' ⟶ (Over.mk (X.hom ≫ g)).left)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback
    (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op]

  [HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ofInteriorHom X g C).obj.right.left.Etale,
  HasWeakSheafify
    ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  
  [HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ofInteriorHom X g C).obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [((smallEtalePullback (ofInteriorHom X g C).obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    (ofInteriorHom X g C).obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (ofInteriorHom X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (ofInteriorHom X g C).obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale,
  HasWeakSheafify
    ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  
  [((smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

variable [IsOpenImmersion
  (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [Etale
  (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [IsSeparated
  (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [LocallyQuasiFinite
  (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [LocallyOfFiniteType
  (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [IsSeparated
  (CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [LocallyQuasiFinite
  (CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [LocallyOfFiniteType
  (CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [IsSeparated
  (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [LocallyQuasiFinite
  (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [LocallyOfFiniteType
  (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower))]
  [IsSeparated
  (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower) ≫
    CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))]
  [LocallyQuasiFinite
  (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower) ≫
    CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))]
  [LocallyOfFiniteType
  (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower) ≫
    CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))]
  [HasSheafify
  (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower)).Etale,
  HasWeakSheafify
    ((CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower)).smallEtaleTopology
    (ModuleCat.{u} Λ))]
  [HasSheafify
  (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.Etale,
  HasWeakSheafify
    ((stackedCompPullback X g C f' g' a b c
        h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (stackedCompPullback X g C f' g' a b c
        h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
    (ModuleCat.{u} Λ))]
  [HasSheafify
  (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale,
  HasWeakSheafify
    ((stackedCompPullback X g C f' g' a b c
        h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  
  [HasSheafify
  (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower)).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify
  (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafify
  (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose
  (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower)).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose
  (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose
  (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(stackedCompPullback X g C f' g' a b c
    h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(stackedCompPullback X g C f' g' a b c
    h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower) ≫
      CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower))).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
    h_upper h_lower)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower) ≫
      CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower))).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower) ≫
      CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))).op]
  [(etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (CompDiagram.ιBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower) ≫
      CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower) ≫
      CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower) ≫
      CompDiagram.openImmersion (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [((smallEtalePullback
      (CompDiagram.toBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower))).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology
    (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower)).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.toBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
          h_upper h_lower))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower)).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower)).smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback
      (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ)
    (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
    (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ)
      (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
      (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (stackedCompPullback X g C f' g' a b c
          h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback
      (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z'.smallEtaleTopology
    (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (stackedCompPullback X g C f' g' a b c
          h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback
      (CompDiagram.toComposite (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
        h_upper h_lower))).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z'.smallEtaleTopology
    (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.toComposite (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
          h_upper h_lower))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (stackedCompPullback X g C f' g' a b c
        h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (stackedCompPullback X g C f' g' a b c
          h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [(etaleModulePushforward
    (CompDiagram.toBase (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower)) Λ).Additive]
  [(etaleModulePushforward
    (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.hom Λ).Additive]
  [(etaleModulePushforward
    (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.hom Λ).Additive]
  [(etaleModulePushforward
    (CompDiagram.toComposite (Over.mk f') g' (stackedCompPullback X g C f' g' a b c
      h_upper h_lower)) Λ).Additive]

  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι C.P_g)).op]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ofInteriorHom X g C).obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (ofInteriorHom X g C).obj.right.hom).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (ofInteriorHom X g C).obj.right.hom).op]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).op]
  [∀ F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (CompDiagram.ofComposite X g C).obj.right.hom).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (CompDiagram.ofComposite X g C).obj.right.hom).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (Of.ι C.P_g)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (Of.ι (ofInteriorHom X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (Of.ι (CompDiagram.ofComposite X g C))).op]

/-- Whiskering the pasted compactification model by `c⁻¹` recovers the stacked
compatibility codomain. -/
theorem stacked_pasteShriek_whisker_eq :
    (etaleModuleDerivedInverseImage c Λ ⋙
      stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ) =
      baseChange_compCodomain X g C f' g' a b c h_upper h_lower Λ := by
  rw [stacked_pasteShriek_def, baseChange_compCodomain_def]

/-- Outer stacked-square path: Lemma 63.9.2 comparison of `C`, then pasted base
change of `g ∘ f`. -/
@[irreducible]
def baseChange_comp_outer :
    baseChange_compDomain X g C a Λ ⟶
      baseChange_compCodomain X g C f' g' a b c h_upper h_lower Λ :=
  eqToHom (baseChange_compDomain_def X g C a Λ) ≫
    whiskerRight (comp X g C Λ) (etaleModuleDerivedInverseImage a Λ) ≫
    whiskerRight (eqToHom (compCodomain_def X g C Λ))
      (etaleModuleDerivedInverseImage a Λ) ≫
    stacked_pasteBaseChange X g C f' g' a b c h_upper h_lower Λ ≫
    eqToHom (baseChange_compCodomain_def X g C f' g' a b c h_upper h_lower Λ).symm

/-- Inner stacked-square path: factor base changes of the lower and upper
squares, then the Lemma 63.9.2 comparison of the pulled-back diagram. -/
@[irreducible]
def baseChange_comp_inner :
    baseChange_compDomain X g C a Λ ⟶
      baseChange_compCodomain X g C f' g' a b c h_upper h_lower Λ :=
  let F : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ :=
    etaleDerivedLowerShriek X (Λ := Λ) (CompDiagram.ofInterior X g C)
  let G : EtaleDerived Y Λ ⥤ EtaleDerived Z Λ :=
    etaleDerivedLowerShriek (Over.mk g) (Λ := Λ) C.P_g
  let A := etaleModuleDerivedInverseImage a Λ
  let B := etaleModuleDerivedInverseImage b Λ
  let Cinv := etaleModuleDerivedInverseImage c Λ
  let F' : EtaleDerived X' Λ ⥤ EtaleDerived Y' Λ :=
    lowerShriekPullback X.hom b f' c h_upper (ofInteriorHom X g C) Λ
  let G' : EtaleDerived Y' Λ ⥤ EtaleDerived Z' Λ :=
    lowerShriekPullback g a g' b h_lower C.P_g Λ
  let lower : ((F ⋙ G) ⋙ A) ⟶ ((F ⋙ B) ⋙ G') :=
    (Functor.associator F G A).hom ≫
      whiskerLeft F (stacked_lowerBaseChange X g C g' a b h_lower Λ) ≫
      (Functor.associator F B G').inv
  let upper : ((F ⋙ B) ⋙ G') ⟶ (Cinv ⋙ (F' ⋙ G')) :=
    whiskerRight (whiskerRight (eqToHom (ofInteriorHom_derived_eq X g C Λ)) B) G' ≫
      whiskerRight (stacked_upperBaseChange X g C f' b c h_upper Λ) G' ≫
      (Functor.associator Cinv F' G').hom
  let paste : (Cinv ⋙ (F' ⋙ G')) ⟶
      (Cinv ⋙ stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ) :=
    whiskerLeft Cinv
      (eqToHom (stacked_factorShriek_def X g C f' g' a b c h_upper h_lower Λ).symm ≫
        stacked_pullbackComp X g C f' g' a b c h_upper h_lower Λ)
  let unfolded : (compDomain X g C Λ ⋙ A) ⟶
      (Cinv ⋙ stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ) :=
    whiskerRight (eqToHom (compDomain_def X g C Λ)) A ≫ lower ≫ upper ≫ paste
  eqToHom (baseChange_compDomain_def X g C a Λ) ≫ unfolded ≫
    eqToHom (stacked_pasteShriek_whisker_eq X g C f' g' a b c h_upper h_lower Λ)

/-- The outer pasted base-change path equals the inner path through the
factor base-change mates and the Lemma 63.9.2 comparison of `C`. -/
theorem baseChange_comp :
    baseChange_comp_outer X g C f' g' a b c h_upper h_lower Λ =
      baseChange_comp_inner X g C f' g' a b c h_upper h_lower Λ :=
  sorry

end Stacked

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale

end
