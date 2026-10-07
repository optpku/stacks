module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Lemma_63_8_5_Comparison
public import stacks_project.Chap63.Lemma_63_9_2_Comparison
import all stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_9_4_Cartesian
import all stacks_project.Chap63.Lemma_63_9_4_Cartesian
public import stacks_project.Chap63.Lemma_63_9_4_Transport
public import stacks_project.Chap63.Lemma_63_9_4_DerivedSites
import all stacks_project.Chap63.Lemma_63_9_4_DerivedSites

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


/-- The lower compactification is the identical constructed base model. -/
theorem stacked_lowerModel_eq :
    lowerShriekPullback g a g' b h_lower C.P_g Λ =
      (etaleDerivedLowerShriek (Over.mk g')
        (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g :
          EtaleDerived Y' Λ ⥤ EtaleDerived Z' Λ) := by
  unfold stackedCompPullback etaleDerivedLowerShriek lowerShriekPullback
  unfold instHasDerivedCategory_overMk instHasDerivedCategory_compactificationPullback
    instHasDerivedCategory_stacked_P_g
  unfold instHasDerivedCategory_overMk._aux_1
    instHasDerivedCategory_compactificationPullback._aux_1
  unfold stackedCompPullback
  rfl

end Stacked
end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale
end
