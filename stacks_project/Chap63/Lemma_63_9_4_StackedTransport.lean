/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Lemma_63_8_5_Comparison
public import stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_9_4_Cartesian
public import stacks_project.Chap63.Lemma_63_9_4_Transport
public import stacks_project.Chap63.Lemma_63_9_4_DerivedSites
public import stacks_project.Chap63.Lemma_63_9_4_StackedModels
public import stacks_project.Chap63.Lemma_63_9_4_StackedComposition
public import stacks_project.Chap63.Lemma_63_9_4_SiteTransport
public import stacks_project.Chap63.Lemma_63_9_4_LowerModel

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
-- Local instance justification (search instability): Use the given strong sheafification projection before generic over-site search.
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

  [HasSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Z'.Etale,
  HasWeakSheafify (Z'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))]
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
  [HasSheafify
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
  [(ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient g a g' b h_lower C.P_g).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
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
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (interiorLift g a g' b h_lower C.P_g)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op]
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
  [∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : (ambient g a g' b h_lower C.P_g).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (interiorLift g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [(etaleModulePushforward (ambientToBase g a g' b h_lower C.P_g) Λ).Additive]
  [(etaleModulePushforward
    (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C)) Λ).Additive]
  [(etaleModulePushforward
    (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)) Λ).Additive]
  [IsOpenImmersion
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

/-- Isomorphisms from the two pulled-back factor models to the specified composition-domain model. -/
def stacked_pullbackCompDomainIsoType : Type _ :=
    @Iso (EtaleDerived X' Λ ⥤ EtaleDerived Z' Λ) _
      (stacked_factorShriek X g C f' g' a b c h_upper h_lower Λ)
      (stacked_diagramDomain X g C f' g' a b c h_upper h_lower Λ)

/-- The fixed codomain comparison type for the iterated and direct ambients. -/
def stacked_pullbackCompCodomainIsoType : Type _ :=
    @Iso (EtaleDerived X' Λ ⥤ EtaleDerived Z' Λ) _
      (stacked_diagramCodomain X g C f' g' a b c h_upper h_lower Λ)
      (stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ)

/-- Transport the two factor models by the actual upper compactification isomorphism. -/
def stacked_pullbackCompDomainIso :
    stacked_pullbackCompDomainIsoType X g C f' g' a b c h_upper h_lower Λ := by
  let D := stackedCompPullback X g C f' g' a b c h_upper h_lower
  let P := CompDiagram.ofInterior (Over.mk f') g' D
  let Q := compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)
  let e : P ≅ Q :=
    eqToIso (congrArg (fun D => CompDiagram.ofInterior (Over.mk f') g' D)
      (stackedCompPullback_def X g C f' g' a b c h_upper h_lower)) ≪≫
        interiorCompactificationIso X g C f' g' a b c h_upper h_lower
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (CompDiagram.interior (Over.mk f') g' D).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (CompDiagram.interior (Over.mk f') g' D).smallEtaleTopology AddCommGrpCat.{u})
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : ∀ U : P.obj.right.left.Etale,
      HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior (Over.mk f') g' D).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : P.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((CompDiagram.interior (Over.mk f') g' D).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : P.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((CompDiagram.interior (Over.mk f') g' D).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology AddCommGrpCat.{u})
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : ∀ U : Q.obj.right.left.Etale,
      HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : Q.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : Q.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : ∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (CompDiagram.ιInterior (Over.mk f') g' D)).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι P)).op :=
    inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (CompDiagram.ιInterior (Over.mk f') g' D)).op)
  -- Local instance justification (defeq pin): Reuse the supplied Kan extensions of ambientToBase at Q.obj.right.hom, the identical fixed map.
  letI : ∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback Q.obj.right.hom).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((smallEtalePullback (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer Q's given Kan extensions through this fixed ambient equivalence e to P's proper map.
  letI : ∀ F : Q.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (Of.ι Q)).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((smallEtalePullback (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer Q's given Kan extensions through this fixed ambient equivalence e to P's proper map.
  letI : ∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F :=
    fun F => smallEtaleAmbient_hasLeftKanExtension Q.obj.right.hom P.obj.right.hom
      (Of.ambientIso e) (Of.ambientIso_over e) F
  let v :
      etaleDerivedLowerShriek (Over.mk f') (Λ := Λ) Q ≅
        etaleDerivedLowerShriek (Over.mk f') (Λ := Λ) P :=
    CompactificationTransport.modelIso (Of.ι Q) Q.obj.right.hom
    (Of.ι P) P.obj.right.hom (Of.ambientIso e)
    (Of.ambientIso_interior e) (Of.ambientIso_over e) Λ
  have lowerModel := stacked_lowerModel_eq X g C f' g' a b c h_upper h_lower Λ
  exact eqToIso (stacked_factorShriek_def X g C f' g' a b c h_upper h_lower Λ) ≪≫
    isoWhiskerRight v (lowerShriekPullback g a g' b h_lower C.P_g Λ) ≪≫
      isoWhiskerLeft (etaleDerivedLowerShriek (Over.mk f') (Λ := Λ) P)
        (eqToIso lowerModel) ≪≫
      (eqToIso (compDomain_def (Over.mk f') g' D Λ)).symm ≪≫
        (eqToIso (stacked_diagramDomain_def X g C f' g' a b c h_upper h_lower Λ)).symm

/-- Transport the composite model by the actual iterated/direct ambient isomorphism. -/
def stacked_pullbackCompCodomainIso :
    stacked_pullbackCompCodomainIsoType X g C f' g' a b c h_upper h_lower Λ := by
  let D := stackedCompPullback X g C f' g' a b c h_upper h_lower
  let P : Of Z' (Over.mk (f' ≫ g')) := CompDiagram.ofComposite (Over.mk f') g' D
  let Q := compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)
  -- Local instance justification (defeq pin): Use the open-immersion proof stored in the fixed compactification P at its interior-map spelling.
  letI : IsOpenImmersion (Of.ι P) := Of.instIsOpenImmersion Z' (Over.mk (f' ≫ g')) P
  let e : P ≅ Q :=
    eqToIso (congrArg (fun D => CompDiagram.ofComposite (Over.mk f') g' D)
      (stackedCompPullback_def X g C f' g' a b c h_upper h_lower)) ≪≫
        compositeCompactificationIso X g C f' g' a b c h_upper h_lower
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (D.P_bar.obj.right.left).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (D.P_bar.obj.right.left).smallEtaleTopology AddCommGrpCat.{u})
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : ∀ U : P.obj.right.left.Etale,
      HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((D.P_bar.obj.right.left).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : P.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((D.P_bar.obj.right.left).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : P.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((D.P_bar.obj.right.left).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology AddCommGrpCat.{u})
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : ∀ U : Q.obj.right.left.Etale,
      HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : Q.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : Q.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : ∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (CompDiagram.ιInterior (Over.mk f') g' D ≫
        CompDiagram.openImmersion (Over.mk f') g' D)).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : ∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (CompDiagram.ιInterior (Over.mk f') g' D ≫
        CompDiagram.openImmersion (Over.mk f') g' D)).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι P)).op :=
    inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (CompDiagram.ιInterior (Over.mk f') g' D ≫
        CompDiagram.openImmersion (Over.mk f') g' D)).op)
  -- Local instance justification (defeq pin): Reuse the supplied Kan extensions of ambientToBase at Q.obj.right.hom, the identical fixed map.
  letI : ∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback Q.obj.right.hom).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((smallEtalePullback (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer Q's given Kan extensions through this fixed ambient equivalence e to P's proper map.
  letI : ∀ F : Q.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (Of.ι Q)).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((smallEtalePullback (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer Q's given Kan extensions through this fixed ambient equivalence e to P's proper map.
  letI : ∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F :=
    fun F => smallEtaleAmbient_hasLeftKanExtension Q.obj.right.hom P.obj.right.hom
      (Of.ambientIso e) (Of.ambientIso_over e) F
  -- Local instance justification (defeq pin): Reuse the exactness property of the specified composite interior at the identical map P.ι.
  letI : (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive :=
    inferInstanceAs ((etaleExtensionByZero
      (CompDiagram.ιInterior (Over.mk f') g' D ≫ CompDiagram.openImmersion (Over.mk f') g' D)
      (ModuleCat.{u} Λ)).Additive)
  -- Local instance justification (defeq pin): Reuse the exactness property of the specified composite interior at the identical map P.ι.
  letI : PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)) :=
    inferInstanceAs (PreservesFiniteLimits (etaleExtensionByZero
      (CompDiagram.ιInterior (Over.mk f') g' D ≫ CompDiagram.openImmersion (Over.mk f') g' D)
      (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Reuse the exactness property of the specified composite interior at the identical map P.ι.
  letI : PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)) :=
    inferInstanceAs (PreservesFiniteColimits (etaleExtensionByZero
      (CompDiagram.ιInterior (Over.mk f') g' D ≫ CompDiagram.openImmersion (Over.mk f') g' D)
      (ModuleCat.{u} Λ)))
  let v :
      etaleDerivedLowerShriek (Over.mk (f' ≫ g')) (Λ := Λ) Q ≅
        etaleDerivedLowerShriek (Over.mk (f' ≫ g')) (Λ := Λ) P :=
    CompactificationTransport.modelIso (Of.ι Q) Q.obj.right.hom
      (Of.ι P) P.obj.right.hom (Of.ambientIso e)
      (Of.ambientIso_interior e) (Of.ambientIso_over e) Λ
  exact eqToIso (stacked_diagramCodomain_def X g C f' g' a b c h_upper h_lower Λ) ≪≫
    eqToIso (compCodomain_def (Over.mk f') g' D Λ) ≪≫ v.symm ≪≫
    (eqToIso (stacked_pasteShriek_def X g C f' g' a b c h_upper h_lower Λ)).symm

/-- Lemma 63.9.2 comparison of the base-changed compactification diagram of
`f'` and `g'`. -/
@[irreducible]
def stacked_pullbackComp :
    stacked_factorShriek X g C f' g' a b c h_upper h_lower Λ ⟶
      stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ :=
  (stacked_pullbackCompDomainIso X g C f' g' a b c h_upper h_lower Λ).hom ≫
    stacked_diagramComp X g C f' g' a b c h_upper h_lower Λ ≫
    (stacked_pullbackCompCodomainIso X g C f' g' a b c h_upper h_lower Λ).hom

end Stacked
end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale
end
