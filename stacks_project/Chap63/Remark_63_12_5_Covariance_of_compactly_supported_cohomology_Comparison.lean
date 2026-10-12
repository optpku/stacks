/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap63.Definition_63_12_1_Gamma
public import stacks_project.Chap63.Lemma_63_8_5_Pullback
public import stacks_project.Chap63.Lemma_63_9_2
public import stacks_project.Chap63.Lemma_63_11_2_Comparison

/-!
# Compactly supported composition comparison

Canonical identification `Rq_! ∘ f_! ≅ Rp_!` on a morphism of separated
finite-type schemes over a field, assembled from the finite-compactification
agreement `Rf_! ≅ f_!`, independence of compactification, and the composition
comparison of compactification models.
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
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Compactification
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
open etaleDerivedLowerShriek

section CovarianceComparison

-- Local instance justification (search instability): prefer the supplied sheafification proof before repeatedly searching the section's over-site families.
attribute [local instance 10000] HasSheafify.isRightAdjoint

variable {k : Type u} [Field k] {Λ : Type u} [CommRing Λ]
  {X Y : SchemeOverField k} (f : X ⟶ Y)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated Y.hom] [Scheme.Hom.FiniteType Y.hom]
  [IsSeparated f.left] [Scheme.Hom.QuasiFinite f.left]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
  [CompactSpace (Spec (CommRingCat.of k))]
  [QuasiSeparatedSpace (Spec (CommRingCat.of k))]
  (C : CompDiagram (Over.mk f.left) Y.hom)
  [IsFinite
  (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.hom]

  [IsOpenImmersion (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
  [Etale (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
  [IsSeparated (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
  [LocallyQuasiFinite (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
  [LocallyOfFiniteType (CompDiagram.ιBase (Over.mk f.left) Y.hom C)]
  [IsSeparated (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
  [LocallyQuasiFinite (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
  [LocallyOfFiniteType (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
  [IsSeparated (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)]
  [LocallyQuasiFinite (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)]
  [LocallyOfFiniteType (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)]
  [IsSeparated
  (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
    CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
  [LocallyQuasiFinite
  (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
    CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]
  [LocallyOfFiniteType
  (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
    CompDiagram.openImmersion (Over.mk f.left) Y.hom C)]

  [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.left.Etale,
  HasWeakSheafify (Y.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (Spec (CommRingCat.of k)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify
  (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
    (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.interior (Over.mk f.left) Y.hom C).Etale,
  HasWeakSheafify
    ((CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
    (ModuleCat.{u} Λ))]
  [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
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
  [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify
  (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
    AddCommGrpCat.{u}]
  [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafify C.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior (Over.mk f.left) Y.hom C).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (Compactification.Of.ι
      (CompDiagram.ofComposite (Over.mk f.left) Y.hom C))).op.HasLeftKanExtension F]
  [∀ F : Y.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.ιBase (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior (Over.mk f.left) Y.hom C).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
  [∀ F : Y.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.ιBase (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.ιBase (Over.mk f.left) Y.hom C)).op]

  [(etaleExtensionByZero (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (CompDiagram.ιBase (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.ιBase (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.ιBase (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
      CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
    (ModuleCat.{u} Λ))]

  [((smallEtalePullback
    (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
      (ModuleCat.{u} Λ))
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
    (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
    C.P_g.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback C.P_g.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_g.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback
    (CompDiagram.toComposite (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.toComposite (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [PreservesFiniteLimits
  ((smallEtalePullback
      (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
    (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology)]
  [PreservesFiniteColimits
  ((smallEtalePullback
      (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
    (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology)]
  [(etaleModulePushforward
    (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.hom Λ).Additive]
  [HasWeakSheafify
  (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
    AddCommGrpCat.{u}]
  [IsGrothendieckAbelian (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} Λ))]
/-- Quasi-finiteness of `f` transfers to `Over.mk f.left`. -/
instance instQuasiFinite_overMk_left :
    Scheme.Hom.QuasiFinite (Over.mk f.left).hom :=
  inferInstanceAs (Scheme.Hom.QuasiFinite f.left)

/-- Right-derivability of the interior compactification structure map. -/
instance instHasRightDerived_ofInterior_hom_cov :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
          (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology
          (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
          (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
          (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Finite-limit preservation along the interior compactification structure
map. -/
instance instPreservesFiniteLimits_ofInterior_hom_cov :
    PreservesFiniteLimits
      ((smallEtalePullback
          (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
        (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology) :=
  inferInstanceAs
    (PreservesFiniteLimits
      ((smallEtalePullback
          (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
        (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology))

/-- Finite-colimit preservation along the interior compactification structure
map. -/
instance instPreservesFiniteColimits_ofInterior_hom_cov :
    PreservesFiniteColimits
      ((smallEtalePullback
          (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
        (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology) :=
  inferInstanceAs
    (PreservesFiniteColimits
      ((smallEtalePullback
          (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
        (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology))

/-- Additivity of continuous pushforward along the interior structure map. -/
instance instAdditive_ofInterior_hom_cov :
    ((smallEtalePullback
        (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback
        (CompDiagram.toBase (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.left.smallEtaleTopology
      (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology).Additive)

/-- Right-derivability of the composite compactification structure map. -/
instance instHasRightDerived_ofComposite_hom_cov :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            (CompDiagram.ofComposite (Over.mk f.left) Y.hom C).obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
          (CompDiagram.ofComposite (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (CompDiagram.ofComposite (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology
          (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            (CompDiagram.toComposite (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
          C.P_bar.obj.right.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Additivity of continuous pushforward along the composite structure map. -/
instance instAdditive_ofComposite_hom_cov :
    ((smallEtalePullback
        (CompDiagram.ofComposite (Over.mk f.left) Y.hom C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      (CompDiagram.ofComposite (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback
        (CompDiagram.toComposite (Over.mk f.left) Y.hom C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology).Additive)

/-- Sheafification preservation on the ambient of `ofInterior`. -/
instance instPreservesSheafification_ofInterior_cov :
    (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  inferInstanceAs
    ((CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

/-- Module sheaf composition on the ambient of `ofInterior`. -/
instance instHasSheafCompose_ofInterior_cov :
    (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  inferInstanceAs
    ((CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

/-- Additivity of extension by zero along the interior of `ofComposite`. -/
instance instAdditive_ofComposite_ι_cov :
    (etaleExtensionByZero
        (Compactification.Of.ι
          (CompDiagram.ofComposite (Over.mk f.left) Y.hom C))
        (ModuleCat.{u} Λ)).Additive :=
  inferInstanceAs
    ((etaleExtensionByZero
        (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
          CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
        (ModuleCat.{u} Λ)).Additive)

/-- Finite-limit preservation along the interior of `ofComposite`. -/
instance instPreservesFiniteLimits_ofComposite_ι_cov :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (Compactification.Of.ι
          (CompDiagram.ofComposite (Over.mk f.left) Y.hom C))
        (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteLimits
      (etaleExtensionByZero
        (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
          CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
        (ModuleCat.{u} Λ)))

/-- Finite-colimit preservation along the interior of `ofComposite`. -/
instance instPreservesFiniteColimits_ofComposite_ι_cov :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (Compactification.Of.ι
          (CompDiagram.ofComposite (Over.mk f.left) Y.hom C))
        (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteColimits
      (etaleExtensionByZero
        (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
          CompDiagram.openImmersion (Over.mk f.left) Y.hom C)
        (ModuleCat.{u} Λ)))

/-- Sheafification preservation on the ambient of `ofComposite`. -/
instance instPreservesSheafification_ofComposite_cov :
    (CompDiagram.ofComposite (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  inferInstanceAs
    (C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

/-- Module sheaf composition on the ambient of `ofComposite`. -/
instance instHasSheafCompose_ofComposite_cov :
    (CompDiagram.ofComposite (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  inferInstanceAs
    (C.P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

/-- Weak sheafification of abelian sheaves on the ambient of `ofInterior`. -/
instance instHasWeakSheafify_ofInterior_AddCommGrp_cov :
    HasWeakSheafify
      (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u} :=
  inferInstanceAs
    (HasWeakSheafify
      (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
      AddCommGrpCat.{u})

/-- Sheafification of abelian sheaves on the ambient of `ofInterior`. -/
instance instHasSheafify_ofInterior_AddCommGrp_cov :
    HasSheafify
      (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u} :=
  inferInstanceAs
    (HasSheafify
      (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology
      AddCommGrpCat.{u})

/-- Left Kan extensions of abelian sheaves along the interior of `ofInterior`. -/
instance instHasLeftKanExtension_ofInterior_ι_AddCommGrp_cov
    (F : (Over.mk f.left).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (etaleRestriction
        (Compactification.Of.ι
          (CompDiagram.ofInterior (Over.mk f.left) Y.hom C))).op.HasLeftKanExtension F :=
  inferInstanceAs
    ((etaleRestriction
        (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F)

/-- The module-to-abelian forgetful functor preserves left Kan extensions along
the interior of `ofInterior`. -/
instance instPreservesLeftKanExtensions_ofInterior_ι_cov :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
        (Compactification.Of.ι
          (CompDiagram.ofInterior (Over.mk f.left) Y.hom C))).op :=
  inferInstanceAs
    ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)).op)

/-- Weak sheafification of abelian sheaves on the ambient of `ofComposite`. -/
instance instHasWeakSheafify_ofComposite_AddCommGrp_cov :
    HasWeakSheafify
      (CompDiagram.ofComposite (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u} :=
  inferInstanceAs
    (HasWeakSheafify C.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})

/-- Sheafification of abelian sheaves on the ambient of `ofComposite`. -/
instance instHasSheafify_ofComposite_AddCommGrp_cov :
    HasSheafify
      (CompDiagram.ofComposite (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u} :=
  inferInstanceAs
    (HasSheafify C.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})

/-- Left Kan extensions of module sheaves along the interior of `ofComposite`. -/
instance instHasLeftKanExtension_ofComposite_ι_cov
    (F : (Over.mk (f.left ≫ Y.hom)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) :
    (etaleRestriction
        (Compactification.Of.ι
          (CompDiagram.ofComposite (Over.mk f.left) Y.hom C))).op.HasLeftKanExtension F :=
  inferInstanceAs
    ((etaleRestriction
        (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
          CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F)

/-- Left Kan extensions of abelian sheaves along the interior of `ofComposite`. -/
instance instHasLeftKanExtension_ofComposite_ι_AddCommGrp_cov
    (F : (Over.mk (f.left ≫ Y.hom)).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (etaleRestriction
        (Compactification.Of.ι
          (CompDiagram.ofComposite (Over.mk f.left) Y.hom C))).op.HasLeftKanExtension F :=
  inferInstanceAs
    ((etaleRestriction
        (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
          CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F)

/-- The module-to-abelian forgetful functor preserves left Kan extensions along
the interior of `ofComposite`. -/
instance instPreservesLeftKanExtensions_ofComposite_ι_cov :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
        (Compactification.Of.ι
          (CompDiagram.ofComposite (Over.mk f.left) Y.hom C))).op :=
  inferInstanceAs
    ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
        (CompDiagram.ιInterior (Over.mk f.left) Y.hom C ≫
          CompDiagram.openImmersion (Over.mk f.left) Y.hom C)).op)

/-- Module sheafification on the interior compactification ambient. -/
instance instHasSheafify_ofInterior_Module_cov :
    HasSheafify
      (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasSheafify
    (CompDiagram.interior (Over.mk f.left) Y.hom C).smallEtaleTopology (ModuleCat.{u} Λ))

/-- Weak sheafification on the same interior compactification ambient. -/
instance instHasWeakSheafify_ofInterior_Module_cov :
    HasWeakSheafify
      (CompDiagram.ofInterior (Over.mk f.left) Y.hom C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) :=
  HasSheafify.isRightAdjoint

/-- Additivity along the interior immersion, in compactification notation. -/
instance instAdditive_ofInterior_ι_cov :
    (etaleExtensionByZero
      (Compactification.Of.ι (CompDiagram.ofInterior (Over.mk f.left) Y.hom C))
      (ModuleCat.{u} Λ)).Additive :=
  inferInstanceAs ((etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C) (ModuleCat.{u} Λ)).Additive)

/-- Finite-limit preservation along the same interior immersion. -/
instance instPreservesFiniteLimits_ofInterior_ι_cov :
    PreservesFiniteLimits (etaleExtensionByZero
      (Compactification.Of.ι (CompDiagram.ofInterior (Over.mk f.left) Y.hom C))
      (ModuleCat.{u} Λ)) :=
  inferInstanceAs (PreservesFiniteLimits (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C) (ModuleCat.{u} Λ)))

/-- Finite-colimit preservation along the same interior immersion. -/
instance instPreservesFiniteColimits_ofInterior_ι_cov :
    PreservesFiniteColimits (etaleExtensionByZero
      (Compactification.Of.ι (CompDiagram.ofInterior (Over.mk f.left) Y.hom C))
      (ModuleCat.{u} Λ)) :=
  inferInstanceAs (PreservesFiniteColimits (etaleExtensionByZero
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C) (ModuleCat.{u} Λ)))

/-- Module-valued left Kan extensions along the same interior immersion. -/
instance instHasLeftKanExtension_ofInterior_ι_Module_cov
    (F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) :
    (etaleRestriction
      (Compactification.Of.ι (CompDiagram.ofInterior (Over.mk f.left) Y.hom C))).op.HasLeftKanExtension F :=
  inferInstanceAs ((etaleRestriction
    (CompDiagram.ιInterior (Over.mk f.left) Y.hom C)).op.HasLeftKanExtension F)

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

  [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ P : Y.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f.left).op.HasLeftKanExtension P]

  [HasDerivedCategory (ModuleCat.{u} Λ)]
  [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
    (ModuleCat.{u} Λ)).obj
    (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} Λ)).obj
      (op (globalEtale (Spec (CommRingCat.of k))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

/-- Finite interior compactification comparison `f_! ≅ Rf_!` whiskered with
`Rq_!`. -/
def gammaCompactSupport_finiteShriekIso :
    lowerShriekModuleDerived f.left Λ ⋙
        etaleDerivedLowerShriek (Λ := Λ) (Over.mk Y.hom) C.P_g ≅
      etaleDerivedLowerShriek (Λ := Λ) (Over.mk f.left)
          (CompDiagram.ofInterior (Over.mk f.left) Y.hom C) ⋙
        etaleDerivedLowerShriek (Λ := Λ) (Over.mk Y.hom) C.P_g :=
  isoWhiskerRight
    (etaleDerivedLowerShriekIsoModuleDerived (Over.mk f.left) Λ
      (CompDiagram.ofInterior (Over.mk f.left) Y.hom C)).symm
    (etaleDerivedLowerShriek (Λ := Λ) (Over.mk Y.hom) C.P_g)

/-- The finite-compactification whiskering is `isoWhiskerRight` of
`etaleDerivedLowerShriekIsoModuleDerived.symm`. -/
theorem gammaCompactSupport_finiteShriekIso_hom :
    (gammaCompactSupport_finiteShriekIso (Λ := Λ) f C).hom =
      whiskerRight
        (etaleDerivedLowerShriekIsoModuleDerived (Over.mk f.left) Λ
          (CompDiagram.ofInterior (Over.mk f.left) Y.hom C)).inv
        (etaleDerivedLowerShriek (Λ := Λ) (Over.mk Y.hom) C.P_g) :=
  sorry

/-- Packed composition comparison `Rf_! ⋙ Rq_! ≅ Rp_!` on a torsion
coefficient ring. -/
def gammaCompactSupport_packedCompIso (hΛ : AddMonoid.IsTorsion Λ) :
    compDomain (Over.mk f.left) Y.hom C Λ ≅
      compCodomain (Over.mk f.left) Y.hom C Λ :=
  compIso (Over.mk f.left) Y.hom C Λ hΛ

/-- Compactly supported sections through the packed composite shriek `Rp_!`.
Using the irreducible packed model avoids re-elaborating
`etaleDerivedLowerShriek` along `ofComposite`. -/
def gammaCompactSupport_compositeGamma :
    EtaleDerived X.left Λ ⥤ DerivedCategory (ModuleCat.{u} Λ) :=
  compCodomain (Over.mk f.left) Y.hom C Λ ⋙
    etaleDerivedGamma (Spec (CommRingCat.of k)) Λ

/-- Unfolding recovers `RΓ` of the packed composite shriek. -/
theorem gammaCompactSupport_compositeGamma_eq :
    gammaCompactSupport_compositeGamma (Λ := Λ) f C =
      compCodomain (Over.mk f.left) Y.hom C Λ ⋙
        etaleDerivedGamma (Spec (CommRingCat.of k)) Λ :=
  sorry

/-- Compactly supported sections `RΓ_c(Y, -)` of the compactification `C.P_g`. -/
def gammaCompactSupport_baseGamma :
    EtaleDerived Y.left Λ ⥤ DerivedCategory (ModuleCat.{u} Λ) :=
  etaleDerivedGammaCompactSupport (Λ := Λ) C.P_g

/-- Unfolding recovers `etaleDerivedGammaCompactSupport` of `C.P_g`. -/
theorem gammaCompactSupport_baseGamma_eq :
    gammaCompactSupport_baseGamma (Λ := Λ) f C =
      etaleDerivedGammaCompactSupport (Λ := Λ) C.P_g :=
  sorry

/-- Identification of packed `RΓ(Spec k, Rp_! -)` with `RΓ` of the unfolded
composite compactification model `R(p)_!`, using `compCodomain_def`. The
compactification is of `Over.mk (f.left ≫ Y.hom)`, hence of `X` via
`f.left ≫ Y.hom = X.hom`. -/
def gammaCompactSupport_compositeGamma_iso :=
  isoWhiskerRight
    (eqToIso (compCodomain_def (Over.mk f.left) Y.hom C Λ))
    (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ)

/-- The composite identification is `isoWhiskerRight` of `compCodomain_def`. -/
theorem gammaCompactSupport_compositeGamma_iso_hom :
    (gammaCompactSupport_compositeGamma_iso (Λ := Λ) f C).hom =
      whiskerRight (eqToHom (compCodomain_def (Over.mk f.left) Y.hom C Λ))
        (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ) :=
  sorry

/-- Canonical identification `Rq_! ∘ f_! ≅ Rp_!` of compactification models
on a torsion coefficient ring, obtained by comparing the exact lower shriek
with the finite interior compactification and applying the packed composition
comparison of Lemma 63.9.2. -/
def gammaCompactSupport_compIso (hΛ : AddMonoid.IsTorsion Λ) :
    lowerShriekModuleDerived f.left Λ ⋙
        etaleDerivedLowerShriek (Λ := Λ) (Over.mk Y.hom) C.P_g ≅
      compCodomain (Over.mk f.left) Y.hom C Λ :=
  gammaCompactSupport_finiteShriekIso (Λ := Λ) f C ≪≫
    eqToIso (compDomain_def (Over.mk f.left) Y.hom C Λ).symm ≪≫
    gammaCompactSupport_packedCompIso (Λ := Λ) f C hΛ

/-- The underlying morphism of `gammaCompactSupport_compIso` is the whiskered
finite comparison followed by the packed composition comparison. -/
theorem gammaCompactSupport_compIso_hom (hΛ : AddMonoid.IsTorsion Λ) :
    (gammaCompactSupport_compIso (Λ := Λ) f C hΛ).hom =
      (gammaCompactSupport_finiteShriekIso (Λ := Λ) f C).hom ≫
        (eqToIso (compDomain_def (Over.mk f.left) Y.hom C Λ).symm).hom ≫
          (gammaCompactSupport_packedCompIso (Λ := Λ) f C hΛ).hom :=
  sorry

/-- Objectwise identification `Rq_! (f_! K) ≅ Rp_! K` on a torsion coefficient
ring. -/
def gammaCompactSupport_compIso_app (hΛ : AddMonoid.IsTorsion Λ)
    (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriek (Λ := Λ) (Over.mk Y.hom) C.P_g).obj
        ((lowerShriekModuleDerived f.left Λ).obj K) ≅
      (compCodomain (Over.mk f.left) Y.hom C Λ).obj K :=
  (gammaCompactSupport_compIso (Λ := Λ) f C hΛ).app K

/-- Evaluating `gammaCompactSupport_compIso` recovers
`gammaCompactSupport_compIso_app`. -/
theorem gammaCompactSupport_compIso_app_eq (hΛ : AddMonoid.IsTorsion Λ)
    (K : EtaleDerived X.left Λ) :
    gammaCompactSupport_compIso_app (Λ := Λ) f C hΛ K =
      (gammaCompactSupport_compIso (Λ := Λ) f C hΛ).app K :=
  sorry

/-- The packed composition comparison is an isomorphism on objects of
`D⁺_tors(X_étale, Λ)`. -/
theorem gammaCompactSupport_comp_app_isIso (K : EtaleDerived X.left Λ)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    (hGE : DerivedCategory.IsGE K n) :
    IsIso (comp_app (Over.mk f.left) Y.hom C Λ K) :=
  sorry

/-- Underlying morphism of the objectwise identification
`Rq_! ∘ f_! ≅ Rp_!` on objects of `D⁺_tors(X_étale, Λ)`. -/
def gammaCompactSupport_compIso_of_isGE_isTorsion_hom
    (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriek (Λ := Λ) (Over.mk Y.hom) C.P_g).obj
        ((lowerShriekModuleDerived f.left Λ).obj K) ⟶
      (compCodomain (Over.mk f.left) Y.hom C Λ).obj K :=
  (gammaCompactSupport_finiteShriekIso (Λ := Λ) f C).hom.app K ≫
    (eqToIso (compDomain_def (Over.mk f.left) Y.hom C Λ).symm).hom.app K ≫
    comp_app (Over.mk f.left) Y.hom C Λ K

/-- Unfolding recovers the whiskered finite comparison followed by
`comp_app`. -/
theorem gammaCompactSupport_compIso_of_isGE_isTorsion_hom_eq
    (K : EtaleDerived X.left Λ) :
    gammaCompactSupport_compIso_of_isGE_isTorsion_hom (Λ := Λ) f C K =
      (gammaCompactSupport_finiteShriekIso (Λ := Λ) f C).hom.app K ≫
        (eqToIso (compDomain_def (Over.mk f.left) Y.hom C Λ).symm).hom.app K ≫
          comp_app (Over.mk f.left) Y.hom C Λ K :=
  sorry

/-- The objectwise comparison morphism is invertible on `D⁺_tors`. -/
theorem gammaCompactSupport_compIso_of_isGE_isTorsion_hom_isIso
    (K : EtaleDerived X.left Λ)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    (hGE : DerivedCategory.IsGE K n) :
    IsIso (gammaCompactSupport_compIso_of_isGE_isTorsion_hom (Λ := Λ) f C K) :=
  sorry

/-- Objectwise identification `Rq_! ∘ f_! ≅ Rp_!` on objects of
`D⁺_tors(X_étale, Λ)`. The inverse is `CategoryTheory.inv` of the already
written hom; invertibility is deferred. -/
def gammaCompactSupport_compIso_of_isGE_isTorsion (K : EtaleDerived X.left Λ)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    (hGE : DerivedCategory.IsGE K n) :
    (etaleDerivedLowerShriek (Λ := Λ) (Over.mk Y.hom) C.P_g).obj
        ((lowerShriekModuleDerived f.left Λ).obj K) ≅
      (compCodomain (Over.mk f.left) Y.hom C Λ).obj K :=
  -- Local instance justification (proof-local temporary data): invertibility of the fixed comparison hom on D⁺_tors supplies CategoryTheory.inv of that same hom.
  haveI : IsIso (gammaCompactSupport_compIso_of_isGE_isTorsion_hom (Λ := Λ) f C K) :=
    gammaCompactSupport_compIso_of_isGE_isTorsion_hom_isIso (Λ := Λ) f C K h_tors n hGE
  asIso (gammaCompactSupport_compIso_of_isGE_isTorsion_hom (Λ := Λ) f C K)

/-- Compactly supported identification `RΓ_c(X, f⁻¹ K) ≅ RΓ_c(Y, f_! f⁻¹ K)`
on a torsion coefficient ring. -/
def gammaCompactSupport_pullbackIso (hΛ : AddMonoid.IsTorsion Λ)
    (K : EtaleDerived Y.left Λ) :
    (gammaCompactSupport_compositeGamma (Λ := Λ) f C).obj
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) ≅
      (gammaCompactSupport_baseGamma (Λ := Λ) f C).obj
        ((lowerShriekModuleDerived f.left Λ).obj
          ((etaleModuleDerivedInverseImage f.left Λ).obj K)) :=
  (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ).mapIso
    (gammaCompactSupport_compIso_app (Λ := Λ) f C hΛ
      ((etaleModuleDerivedInverseImage f.left Λ).obj K)).symm

/-- The underlying morphism of `gammaCompactSupport_pullbackIso` conjugates
`RΓ` of the inverse composition identification by the packed-to-`RΓ_c`
comparisons. -/
theorem gammaCompactSupport_pullbackIso_hom (hΛ : AddMonoid.IsTorsion Λ)
    (K : EtaleDerived Y.left Λ) :
    (gammaCompactSupport_pullbackIso (Λ := Λ) f C hΛ K).hom =
      (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ).map
        (gammaCompactSupport_compIso_app (Λ := Λ) f C hΛ
          ((etaleModuleDerivedInverseImage f.left Λ).obj K)).inv :=
  sorry

/-- Compactly supported identification `RΓ_c(X, f⁻¹ K) ≅ RΓ_c(Y, f_! f⁻¹ K)`
on objects of `D⁺_tors`. -/
def gammaCompactSupport_pullbackIso_of_isGE_isTorsion (K : EtaleDerived Y.left Λ)
    (h_tors : etaleDerivedIsTorsion
      ((etaleModuleDerivedInverseImage f.left Λ).obj K))
    (n : ℤ)
    (hGE : DerivedCategory.IsGE
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) n) :
    (gammaCompactSupport_compositeGamma (Λ := Λ) f C).obj
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) ≅
      (gammaCompactSupport_baseGamma (Λ := Λ) f C).obj
        ((lowerShriekModuleDerived f.left Λ).obj
          ((etaleModuleDerivedInverseImage f.left Λ).obj K)) :=
  (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ).mapIso
    (gammaCompactSupport_compIso_of_isGE_isTorsion (Λ := Λ) f C
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) h_tors n hGE).symm

/-- The underlying morphism of the `D⁺_tors` pullback identification conjugates
`RΓ` of the inverse objectwise composition identification by the
packed-to-`RΓ_c` comparisons. -/
theorem gammaCompactSupport_pullbackIso_of_isGE_isTorsion_hom
    (K : EtaleDerived Y.left Λ)
    (h_tors : etaleDerivedIsTorsion
      ((etaleModuleDerivedInverseImage f.left Λ).obj K))
    (n : ℤ)
    (hGE : DerivedCategory.IsGE
      ((etaleModuleDerivedInverseImage f.left Λ).obj K) n) :
    (gammaCompactSupport_pullbackIso_of_isGE_isTorsion (Λ := Λ) f C K h_tors n hGE).hom =
      (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ).map
        (gammaCompactSupport_compIso_of_isGE_isTorsion (Λ := Λ) f C
          ((etaleModuleDerivedInverseImage f.left Λ).obj K) h_tors n hGE).inv :=
  sorry

end CovarianceComparison

end AlgebraicGeometry.Scheme.Etale

end
