module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Lemma_63_8_5_Comparison
public import stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_9_4_Cartesian
public import stacks_project.Chap63.Lemma_63_9_4_Transport
public import stacks_project.Chap63.Lemma_63_9_4_DerivedSites

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
-- Local instance justification (search instability): Use the given strong sheafification projection before generic over-site search in this diagram context.
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

/-- Domain of the stacked-square compatibility: `(Rf_! ⋙ Rg_!) ⋙ a⁻¹`. -/
irreducible_def baseChange_compDomain :
    EtaleDerived X.left Λ ⥤ EtaleDerived Z' Λ :=
  compDomain X g C Λ ⋙ etaleModuleDerivedInverseImage a Λ

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


/-- Codomain of the stacked-square compatibility: `c⁻¹ ⋙ R(g' ∘ f')_!` of the
pasted compactification of `g ∘ f`. -/
irreducible_def baseChange_compCodomain :
    EtaleDerived X.left Λ ⥤ EtaleDerived Z' Λ :=
  etaleModuleDerivedInverseImage c Λ ⋙
    lowerShriekPullback (X.hom ≫ g) a (f' ≫ g') c
      (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C) Λ

/-- Lower stacked comparison `Rg_! ⋙ a⁻¹ ⟶ b⁻¹ ⋙ Rg'_!`, the compactification
model `baseChange` of the lower cartesian square. -/
@[irreducible]
def stacked_lowerBaseChange :
    (etaleDerivedLowerShriek (Over.mk g) C.P_g ⋙
      etaleModuleDerivedInverseImage a Λ) ⟶
    (etaleModuleDerivedInverseImage b Λ ⋙
      lowerShriekPullback g a g' b h_lower C.P_g Λ) :=
  -- The local proof pins the existing restriction spelling; it adds no premise.
  -- Local instance justification (defeq pin): The lower mate uses C.P_g.ι; reuse the given Kan-preservation proof stated for CompDiagram.ιBase.
  letI : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι C.P_g)).op :=
    inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (CompDiagram.ιBase X g C)).op)
  eqToHom (baseChangeDomain_def g a C.P_g Λ).symm ≫
    baseChange g a g' b h_lower C.P_g Λ ≫
    eqToHom (baseChangeCodomain_def g a g' b h_lower C.P_g Λ)

/-- Upper stacked comparison `Rf_! ⋙ b⁻¹ ⟶ c⁻¹ ⋙ Rf'_!`, the compactification
model `baseChange` of the upper cartesian square. -/
@[irreducible]
def stacked_upperBaseChange :
    (etaleDerivedLowerShriek (Over.mk X.hom) (ofInteriorHom X g C) ⋙
      etaleModuleDerivedInverseImage b Λ) ⟶
    (etaleModuleDerivedInverseImage c Λ ⋙
      lowerShriekPullback X.hom b f' c h_upper (ofInteriorHom X g C) Λ) :=
  eqToHom (baseChangeDomain_def X.hom b (ofInteriorHom X g C) Λ).symm ≫
    baseChange X.hom b f' c h_upper (ofInteriorHom X g C) Λ ≫
    eqToHom (baseChangeCodomain_def X.hom b f' c h_upper (ofInteriorHom X g C) Λ)

/-- Pasted stacked comparison `R(g ∘ f)_! ⋙ a⁻¹ ⟶ c⁻¹ ⋙ R(g' ∘ f')_!`, the
compactification model `baseChange` of the outer rectangle. -/
@[irreducible]
def stacked_pasteBaseChange :
    (etaleDerivedLowerShriek (Over.mk (X.hom ≫ g)) (CompDiagram.ofComposite X g C) ⋙
      etaleModuleDerivedInverseImage a Λ) ⟶
    (etaleModuleDerivedInverseImage c Λ ⋙
      lowerShriekPullback (X.hom ≫ g) a (f' ≫ g') c
        (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C) Λ) :=
  -- Use the supplied composite-interior restriction proof at its compactification alias.
  -- Local instance justification (defeq pin): Reuse the supplied Kan-extension property of the composite interior at its identical Of.ι spelling.
  letI : ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse the supplied Kan-extension property of the composite interior at its identical Of.ι spelling.
  letI : ∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse C.P_bar's given sheaf-composition proof at the identical ambient of CompDiagram.ofComposite.
  letI : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op :=
    inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).op)
  -- This is the same ambient as C.P_bar; reuse its given sheaf-composition proof.
  -- Local instance justification (defeq pin): Reuse C.P_bar's given sheaf-composition proof at the identical ambient of CompDiagram.ofComposite.
  letI : (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs (C.P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  baseChangeUnfolded (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C) Λ

/-- The compactification model of `X.hom` from `CompDiagram.ofInterior` agrees
with `ofInteriorHom`. -/
theorem ofInteriorHom_derived_eq :
    (etaleDerivedLowerShriek X (CompDiagram.ofInterior X g C) :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) =
      (etaleDerivedLowerShriek (Over.mk X.hom) (ofInteriorHom X g C) :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) := by
  rfl

/-- Opaque composite of the upper and lower pullback compactification models. -/
irreducible_def stacked_factorShriek :
    EtaleDerived X' Λ ⥤ EtaleDerived Z' Λ :=
  lowerShriekPullback X.hom b f' c h_upper (ofInteriorHom X g C) Λ ⋙
    lowerShriekPullback g a g' b h_lower C.P_g Λ

/-- Opaque pasted compactification model of `g' ∘ f'`. -/
irreducible_def stacked_pasteShriek :
    EtaleDerived X' Λ ⥤ EtaleDerived Z' Λ :=
  lowerShriekPullback (X.hom ≫ g) a (f' ≫ g') c
    (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C) Λ


end Stacked

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale

end
