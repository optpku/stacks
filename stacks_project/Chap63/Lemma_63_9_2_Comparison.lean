/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap63.Lemma_63_4_3
public import stacks_project.Chap63.Lemma_63_8_2_Comparison
public import stacks_project.Chap63.Lemma_63_8_3_Comp
public import stacks_project.Chap63.Lemma_63_9_2_Compactification

/-!
# Derived étale lower shriek composition

Canonical comparison `Rf_! ⋙ Rg_! ⟶ R(g ∘ f)_!` of compactification models,
assembled from the Lemma 63.8.1 square map, derived pushforward composition,
and derived lower-shriek composition.
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

/-- Étale module direct image is additive. -/
instance instAdditive_etaleModulePushforward
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [CommRing Λ] :
    (etaleModulePushforward f Λ).Additive :=
  sorry

/-- Unfolding `etaleModulePushforward` recovers additivity of continuous
small-étale module pushforward. -/
instance instAdditive_sheafPushforwardContinuous
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [CommRing Λ] :
    ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) T.smallEtaleTopology S.smallEtaleTopology).Additive :=
  instAdditive_etaleModulePushforward f Λ

/-- Functor composition of étale module pushforwards is additive. -/
instance instAdditive_etaleModulePushforward_functorComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (Λ : Type u) [CommRing Λ] :
    (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ).Additive :=
  sorry

/-- Small-étale module sheaves admit K-injective resolutions, giving total
right derivation of étale module pushforward. -/
instance instHasRightDerived_etaleModulePushforward
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [CommRing Λ]
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasRightDerivedFunctor (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  sorry

/-- Unfolding `etaleModulePushforward` recovers right-derivability of continuous
small-étale module pushforward. -/
instance instHasRightDerived_sheafPushforwardContinuous
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [CommRing Λ]
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) T.smallEtaleTopology S.smallEtaleTopology))
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  instHasRightDerived_etaleModulePushforward f Λ

/-- The underived composite `f_* ⋙ g_*` admits a total right derived functor. -/
instance instHasRightDerived_etaleModulePushforward_functorComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (Λ : Type u) [CommRing Λ]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : Z.Etale, HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  sorry

/-- Pin the universal-property witness to the étale derived pushforward. -/
instance instIsRightDerived_etaleDerivedPushforward
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [CommRing Λ]
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))] :
    (etaleDerivedPushforward f : EtaleDerived S Λ ⥤ EtaleDerived T Λ).IsRightDerivedFunctor
      (RightDerived.Cochain.unit (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  RightDerived.Cochain.isRightDerived (etaleModulePushforward f Λ)


section ExtensionIso

variable {U T : Scheme.{u}} (j : U ⟶ T) [Etale j] [LocallyQuasiFinite j]
  (Λ : Type u) [CommRing Λ]
  [U.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [T.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
  [T.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
  [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]
  [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]

/-- Forgetting coefficients identifies étale extension by zero of a sheaf of
`Λ`-modules with abelian extension by zero of the underlying abelian sheaf. -/
def extensionByZero_compSheafCompose
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F) ≅
      (abelianExtensionByZero j).obj
        ((sheafCompose U.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) :=
  (Functor.sheafPullback.compSheafComposeIso
      (etaleRestriction j) (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
      U.smallEtaleTopology T.smallEtaleTopology).app F

/-- The component of the sheaf-level identification of étale extension by zero
with finite-support lower shriek. -/
def extensionByZeroIsoLowerShriekModule_app
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F ≅
      (lowerShriekModule j Λ).obj F where
  hom :=
    liftModuleSheafHom
      ((extensionByZero_compSheafCompose j Λ F).hom ≫
        ((extensionByZeroIsoLowerShriek j).app
            ((sheafCompose U.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        ((lowerShriekModule_forgetFunctorIso j Λ).app F).inv)
  inv :=
    liftModuleSheafHom
      (((lowerShriekModule_forgetFunctorIso j Λ).app F).hom ≫
        ((extensionByZeroIsoLowerShriek j).symm.app
            ((sheafCompose U.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (extensionByZero_compSheafCompose j Λ F).inv)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheaf-level identification of étale extension by zero with finite-support
lower shriek on étale sheaves of `Λ`-modules. -/
def extensionByZeroIsoLowerShriekModule :
    etaleExtensionByZero j (ModuleCat.{u} Λ) ≅ lowerShriekModule j Λ :=
  NatIso.ofComponents (extensionByZeroIsoLowerShriekModule_app j Λ) sorry

/-- Exact extension by zero and exact finite-support shriek induce the derived
identification. -/
def extensionByZeroDerivedIsoLowerShriekModule
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [(etaleExtensionByZero j (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ))] :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ≅
      lowerShriekModuleDerived j Λ :=
  Functor.MapDerivedCategory.functorIso (extensionByZeroIsoLowerShriekModule j Λ)

end ExtensionIso

namespace etaleDerivedLowerShriek

-- Local instance justification (search instability): prioritize the existing strong-to-weak projection so base-topology goals do not repeatedly match unrelated over-site families.
attribute [local instance 10000] HasSheafify.isRightAdjoint

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g)

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

  (Λ : Type u) [CommRing Λ]
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
/-- `Over.mk g` has the same underlying scheme as `Y`. -/
instance instHasSheafCompose_overMk :
    HasSheafCompose (Over.mk g).left.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  inferInstanceAs
    (HasSheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

/-- Abelian sheafification on `Y` transfers to `Over.mk g`. -/
instance instHasSheafifyAddComm_overMk :
    HasSheafify (Over.mk g).left.smallEtaleTopology AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u})

/-- Sheafification preservation on `Y` transfers to `Over.mk g`. -/
instance instPreservesSheafification_overMk :
    (Over.mk g).left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  inferInstanceAs
    (Y.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

/-- `g ∘ f` has the same underlying source as `X`. -/
instance instHasSheafCompose_overMk_comp :
    HasSheafCompose (Over.mk (X.hom ≫ g)).left.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  inferInstanceAs
    (HasSheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

/-- Abelian sheafification on `X` transfers to `Over.mk (X.hom ≫ g)`. -/
instance instHasSheafifyAddComm_overMk_comp :
    HasSheafify (Over.mk (X.hom ≫ g)).left.smallEtaleTopology AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u})

/-- The interior of `P_g` is étale, as the open immersion `ιBase`. -/
instance instEtale_P_g_ι : Etale (Of.ι C.P_g) :=
  inferInstanceAs (Etale (CompDiagram.ιBase X g C))

/-- Left Kan extensions along `ι P_g` transfer from `Y` to `Over.mk g`. -/
instance instHasLeftKanExtension_overMk_ι
    (F : (Over.mk g).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) :
    (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F :=
  inferInstanceAs
    ((etaleRestriction (CompDiagram.ιBase X g C)).op.HasLeftKanExtension
      (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ))

/-- Abelian left Kan extensions along `ι P_g` transfer from `Y` to `Over.mk g`. -/
instance instHasLeftKanExtension_overMk_ι_ab
    (F : (Over.mk g).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F :=
  inferInstanceAs
    ((etaleRestriction (CompDiagram.ιBase X g C)).op.HasLeftKanExtension
      (F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}))

/-- Additive extension by zero along the interior of `P_g`. -/
instance instAdditive_P_g_ι :
    (etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ)).Additive :=
  inferInstanceAs
    ((etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ)).Additive)

/-- Finite-limit preservation along the interior of `P_g`. -/
instance instPreservesFiniteLimits_P_g_ι :
    PreservesFiniteLimits (etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteLimits
      (etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ)))

/-- Finite-colimit preservation along the interior of `P_g`. -/
instance instPreservesFiniteColimits_P_g_ι :
    PreservesFiniteColimits
      (etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteColimits
      (etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ)))

variable [(etaleModulePushforward (CompDiagram.toBase X g C) Λ).Additive]
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

/-- `Over.mk g` has the same underlying scheme as `Y`. -/
instance instHasSheafify_overMk :
    HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ))

/-- Derived category of sheaves on `Y` transfers to `Over.mk g`. -/
instance instHasDerivedCategory_overMk :
    HasDerivedCategory (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  inferInstanceAs (HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))

/-- Weak sheafification on étale objects of `Y` transfers to `Over.mk g`. -/
instance instHasWeakSheafify_overMk (U : (Over.mk g).left.Etale) :
    HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ))

/-- `g ∘ f` has the same underlying source as `X`. -/
instance instHasSheafify_overMk_comp :
    HasSheafify (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))

/-- Derived category of sheaves on `X` transfers to `Over.mk (X.hom ≫ g)`. -/
instance instHasDerivedCategory_overMk_comp :
    HasDerivedCategory
      (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))

/-- Weak sheafification on étale objects of `X` transfers to `Over.mk (X.hom ≫ g)`. -/
instance instHasWeakSheafify_overMk_comp (U : (Over.mk (X.hom ≫ g)).left.Etale) :
    HasWeakSheafify ((Over.mk (X.hom ≫ g)).left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))

/-- The interior compactification has ambient `U`. -/
instance instHasSheafify_ofInterior :
    HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology
      (ModuleCat.{u} Λ))

/-- Derived category of sheaves on `U` transfers to the ambient of `ofInterior`. -/
instance instHasDerivedCategory_ofInterior :
    HasDerivedCategory
      (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (HasDerivedCategory
      (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))

/-- Weak sheafification on the interior transfers to the ambient of `ofInterior`. -/
instance instHasWeakSheafify_ofInterior
    (U : (CompDiagram.ofInterior X g C).obj.right.left.Etale) :
    HasWeakSheafify
      ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ) :=
  inferInstanceAs
    (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U)
      (ModuleCat.{u} Λ))

/-- The derived Leray comparison `R(f̄ ≫ ḡ)_* ⟶ Rf̄_* ⋙ Rḡ_*` is an
isomorphism. -/
instance instIsIso_etaleDerivedPushforwardComp :
    IsIso
      (etaleDerivedPushforwardComp C.P_bar.obj.right.hom C.P_g.obj.right.hom Λ) :=
  etaleDerivedPushforwardComp_isIso C.P_bar.obj.right.hom C.P_g.obj.right.hom Λ

/-- Derived Leray identification `Rf̄_* ⋙ Rḡ_* ≅ R(f̄ ≫ ḡ)_*`. -/
def pushforwardCompIso :
    (etaleDerivedPushforward C.P_bar.obj.right.hom :
          EtaleDerived C.P_bar.obj.right.left Λ ⥤
            EtaleDerived C.P_g.obj.right.left Λ) ⋙
        (etaleDerivedPushforward C.P_g.obj.right.hom :
          EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ) ≅
      (etaleDerivedPushforward (CompDiagram.toComposite X g C) :
        EtaleDerived C.P_bar.obj.right.left Λ ⥤ EtaleDerived Z Λ) :=
  (asIso
      (etaleDerivedPushforwardComp C.P_bar.obj.right.hom C.P_g.obj.right.hom Λ :
        (etaleDerivedPushforward (CompDiagram.toComposite X g C) :
            EtaleDerived C.P_bar.obj.right.left Λ ⥤ EtaleDerived Z Λ) ⟶
          (etaleDerivedPushforward C.P_bar.obj.right.hom :
                EtaleDerived C.P_bar.obj.right.left Λ ⥤
                  EtaleDerived C.P_g.obj.right.left Λ) ⋙
            (etaleDerivedPushforward C.P_g.obj.right.hom :
              EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ))).symm

/-- Whiskered Lemma 63.8.1 comparison on the open/proper square of a
composition diagram, transported to the extension-by-zero model. -/
def squareMap :
    (etaleDerivedPushforward (CompDiagram.toBase X g C) :
          EtaleDerived (CompDiagram.interior X g C) Λ ⥤ EtaleDerived Y Λ) ⋙
        (etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ)).mapDerivedCategory ⟶
      (etaleExtensionByZero (CompDiagram.openImmersion X g C)
            (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward C.P_bar.obj.right.hom :
          EtaleDerived C.P_bar.obj.right.left Λ ⥤
            EtaleDerived C.P_g.obj.right.left Λ) :=
  (whiskerLeft
      (etaleDerivedPushforward (CompDiagram.toBase X g C))
      (extensionByZeroDerivedIsoLowerShriekModule (CompDiagram.ιBase X g C) Λ).hom ≫
    etaleDerivedLowerShriekPushforward C.P_bar.obj.right.hom
      (CompDiagram.toBase X g C) (CompDiagram.ιBase X g C)
      (CompDiagram.openImmersion X g C) (CompDiagram.square X g C) Λ ≫
    whiskerRight
      (extensionByZeroDerivedIsoLowerShriekModule
          (CompDiagram.openImmersion X g C) Λ).inv
      (etaleDerivedPushforward C.P_bar.obj.right.hom))

/-- Derived identification `j_! ⋙ j'_! ⟶ (j' ∘ j)_!` in the extension-by-zero
model. -/
def shriekComp :
    (etaleExtensionByZero (CompDiagram.ιInterior X g C)
            (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleExtensionByZero (CompDiagram.openImmersion X g C)
            (ModuleCat.{u} Λ)).mapDerivedCategory ⟶
      (etaleExtensionByZero
          (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)
          (ModuleCat.{u} Λ)).mapDerivedCategory :=
  whiskerRight
      (extensionByZeroDerivedIsoLowerShriekModule
          (CompDiagram.ιInterior X g C) Λ).hom
      (etaleExtensionByZero (CompDiagram.openImmersion X g C)
          (ModuleCat.{u} Λ)).mapDerivedCategory ≫
    whiskerLeft (lowerShriekModuleDerived (CompDiagram.ιInterior X g C) Λ)
      (extensionByZeroDerivedIsoLowerShriekModule
          (CompDiagram.openImmersion X g C) Λ).hom ≫
    (lowerShriekModuleDerivedCompIso (CompDiagram.ιInterior X g C)
        (CompDiagram.openImmersion X g C) Λ).hom ≫
    (extensionByZeroDerivedIsoLowerShriekModule
        (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C) Λ).inv

/-- Left Kan extensions along the interior of `ofInterior`. -/
instance instHasLeftKanExtension_ofInterior_ι
    (F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) :
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F :=
  inferInstanceAs
    ((etaleRestriction (CompDiagram.ιInterior X g C)).op.HasLeftKanExtension F)

/-- Additive extension by zero along the interior of `ofInterior`. -/
instance instAdditive_ofInterior_ι :
    (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ)).Additive :=
  inferInstanceAs
    ((etaleExtensionByZero (CompDiagram.ιInterior X g C) (ModuleCat.{u} Λ)).Additive)

/-- Finite-limit preservation along the interior of `ofInterior`. -/
instance instPreservesFiniteLimits_ofInterior_ι :
    PreservesFiniteLimits
      (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteLimits
      (etaleExtensionByZero (CompDiagram.ιInterior X g C) (ModuleCat.{u} Λ)))

/-- Finite-colimit preservation along the interior of `ofInterior`. -/
instance instPreservesFiniteColimits_ofInterior_ι :
    PreservesFiniteColimits
      (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteColimits
      (etaleExtensionByZero (CompDiagram.ιInterior X g C) (ModuleCat.{u} Λ)))

/-- Weak sheafification on the ambient of `ofComposite`. -/
instance instHasWeakSheafify_ofComposite
    (U : (CompDiagram.ofComposite X g C).obj.right.left.Etale) :
    HasWeakSheafify
      ((CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ) :=
  inferInstanceAs
    (HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ))

/-- Sheafification on the ambient of `ofComposite`. -/
instance instHasSheafify_ofComposite :
    HasSheafify (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) :=
  inferInstanceAs
    (HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))

/-- Derived category of sheaves on the ambient of `ofComposite`. -/
instance instHasDerivedCategory_ofComposite :
    HasDerivedCategory
      (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (HasDerivedCategory
      (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))

/-- Left Kan extensions along the interior of `ofComposite`. -/
instance instHasLeftKanExtension_ofComposite_ι
    (F : (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) :
    (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F :=
  inferInstanceAs
    ((etaleRestriction
        (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F)

/-- Additive extension by zero along the interior of `ofComposite`. -/
instance instAdditive_ofComposite_ι :
    (etaleExtensionByZero (Of.ι (CompDiagram.ofComposite X g C)) (ModuleCat.{u} Λ)).Additive :=
  inferInstanceAs
    ((etaleExtensionByZero
        (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)
        (ModuleCat.{u} Λ)).Additive)

/-- Finite-limit preservation along the interior of `ofComposite`. -/
instance instPreservesFiniteLimits_ofComposite_ι :
    PreservesFiniteLimits
      (etaleExtensionByZero (Of.ι (CompDiagram.ofComposite X g C)) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteLimits
      (etaleExtensionByZero
        (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)
        (ModuleCat.{u} Λ)))

/-- Finite-colimit preservation along the interior of `ofComposite`. -/
instance instPreservesFiniteColimits_ofComposite_ι :
    PreservesFiniteColimits
      (etaleExtensionByZero (Of.ι (CompDiagram.ofComposite X g C)) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteColimits
      (etaleExtensionByZero
        (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)
        (ModuleCat.{u} Λ)))

/-- Continuous small-étale pushforward along the structure map of `ofInterior`
is additive. -/
instance instAdditive_sheafPushforward_ofInterior_hom :
    ((smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (CompDiagram.toBase X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (CompDiagram.interior X g C).smallEtaleTopology).Additive)

/-- The structure map of `ofInterior` is right-derivable. -/
instance instHasRightDerived_ofInterior_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
          (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (CompDiagram.toBase X g C)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          (CompDiagram.interior X g C).smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Continuous small-étale pushforward along the structure map of `ofComposite`
is additive. -/
instance instAdditive_sheafPushforward_ofComposite_hom :
    ((smallEtalePullback (CompDiagram.ofComposite X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (CompDiagram.toComposite X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology).Additive)

/-- The structure map of `ofComposite` is right-derivable. -/
instance instHasRightDerived_ofComposite_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (CompDiagram.ofComposite X g C).obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology
          (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
          (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (CompDiagram.toComposite X g C)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology
          C.P_bar.obj.right.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Compactification model of `Rf_! ⋙ Rg_!`. -/
irreducible_def compDomain :
    EtaleDerived X.left Λ ⥤ EtaleDerived Z Λ :=
  etaleDerivedLowerShriek X (CompDiagram.ofInterior X g C) ⋙
    etaleDerivedLowerShriek (Over.mk g) C.P_g

/-- Compactification model of `R(g ∘ f)_!`. -/
irreducible_def compCodomain :
    EtaleDerived X.left Λ ⥤ EtaleDerived Z Λ :=
  etaleDerivedLowerShriek (Over.mk (X.hom ≫ g)) (CompDiagram.ofComposite X g C)

/-- Canonical comparison `Rf_! ⋙ Rg_! ⟶ R(g ∘ f)_!` of compactification models
attached to a composition diagram. -/
@[irreducible]
def comp : compDomain X g C Λ ⟶ compCodomain X g C Λ :=
  eqToHom (compDomain_def X g C Λ) ≫
  ((Functor.associator
      (etaleExtensionByZero (CompDiagram.ιInterior X g C) (ModuleCat.{u} Λ)).mapDerivedCategory
      (etaleDerivedPushforward (CompDiagram.toBase X g C) :
        EtaleDerived (CompDiagram.interior X g C) Λ ⥤ EtaleDerived Y Λ)
      (etaleDerivedLowerShriek (Over.mk g) C.P_g :
        EtaleDerived Y Λ ⥤ EtaleDerived Z Λ)).hom ≫
    whiskerLeft
      (etaleExtensionByZero (CompDiagram.ιInterior X g C) (ModuleCat.{u} Λ)).mapDerivedCategory
      ((Functor.associator
          (etaleDerivedPushforward (CompDiagram.toBase X g C) :
            EtaleDerived (CompDiagram.interior X g C) Λ ⥤ EtaleDerived Y Λ)
          (etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ)).mapDerivedCategory
          (etaleDerivedPushforward C.P_g.obj.right.hom :
            EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ)).inv ≫
        whiskerRight (squareMap X g C Λ)
          (etaleDerivedPushforward C.P_g.obj.right.hom :
            EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ) ≫
        (Functor.associator
            (etaleExtensionByZero (CompDiagram.openImmersion X g C)
                (ModuleCat.{u} Λ)).mapDerivedCategory
            (etaleDerivedPushforward C.P_bar.obj.right.hom :
              EtaleDerived C.P_bar.obj.right.left Λ ⥤
                EtaleDerived C.P_g.obj.right.left Λ)
            (etaleDerivedPushforward C.P_g.obj.right.hom :
              EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ)).hom) ≫
    (Functor.associator
        (etaleExtensionByZero (CompDiagram.ιInterior X g C) (ModuleCat.{u} Λ)).mapDerivedCategory
        (etaleExtensionByZero (CompDiagram.openImmersion X g C) (ModuleCat.{u} Λ)).mapDerivedCategory
        ((etaleDerivedPushforward C.P_bar.obj.right.hom :
              EtaleDerived C.P_bar.obj.right.left Λ ⥤
                EtaleDerived C.P_g.obj.right.left Λ) ⋙
          (etaleDerivedPushforward C.P_g.obj.right.hom :
            EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ))).inv ≫
    whiskerRight (shriekComp X g C Λ)
      ((etaleDerivedPushforward C.P_bar.obj.right.hom :
            EtaleDerived C.P_bar.obj.right.left Λ ⥤
              EtaleDerived C.P_g.obj.right.left Λ) ⋙
        (etaleDerivedPushforward C.P_g.obj.right.hom :
          EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ)) ≫
    whiskerLeft
      (etaleExtensionByZero
          (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)
          (ModuleCat.{u} Λ)).mapDerivedCategory
      (pushforwardCompIso X g C Λ).hom) ≫
    eqToHom (compCodomain_def X g C Λ).symm

/-- Component of `comp` at an object of `D(X_étale, Λ)`. -/
@[irreducible]
def comp_app (K : EtaleDerived X.left Λ) :
    (compDomain X g C Λ).obj K ⟶ (compCodomain X g C Λ).obj K :=
  (comp X g C Λ).app K

/-- The objectwise comparison is the component of `comp`. -/
theorem comp_app_eq (K : EtaleDerived X.left Λ) :
    comp_app X g C Λ K = (comp X g C Λ).app K :=
  sorry

/-- Unfolding of `comp` as the whiskered Lemma 63.8.1 map together with the
shriek and pushforward composition identifications. -/
theorem comp_eq :
    eqToHom (compDomain_def X g C Λ).symm ≫
        comp X g C Λ ≫ eqToHom (compCodomain_def X g C Λ) =
      (Functor.associator
          (etaleExtensionByZero (CompDiagram.ιInterior X g C)
              (ModuleCat.{u} Λ)).mapDerivedCategory
          (etaleDerivedPushforward (CompDiagram.toBase X g C) :
            EtaleDerived (CompDiagram.interior X g C) Λ ⥤ EtaleDerived Y Λ)
          (etaleDerivedLowerShriek (Over.mk g) C.P_g :
            EtaleDerived Y Λ ⥤ EtaleDerived Z Λ)).hom ≫
        whiskerLeft
          (etaleExtensionByZero (CompDiagram.ιInterior X g C)
              (ModuleCat.{u} Λ)).mapDerivedCategory
          ((Functor.associator
              (etaleDerivedPushforward (CompDiagram.toBase X g C) :
                EtaleDerived (CompDiagram.interior X g C) Λ ⥤ EtaleDerived Y Λ)
              (etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ)).mapDerivedCategory
              (etaleDerivedPushforward C.P_g.obj.right.hom :
                EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ)).inv ≫
            whiskerRight (squareMap X g C Λ)
              (etaleDerivedPushforward C.P_g.obj.right.hom :
                EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ) ≫
            (Functor.associator
                (etaleExtensionByZero (CompDiagram.openImmersion X g C)
                    (ModuleCat.{u} Λ)).mapDerivedCategory
                (etaleDerivedPushforward C.P_bar.obj.right.hom :
                  EtaleDerived C.P_bar.obj.right.left Λ ⥤
                    EtaleDerived C.P_g.obj.right.left Λ)
                (etaleDerivedPushforward C.P_g.obj.right.hom :
                  EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ)).hom) ≫
        (Functor.associator
            (etaleExtensionByZero (CompDiagram.ιInterior X g C)
                (ModuleCat.{u} Λ)).mapDerivedCategory
            (etaleExtensionByZero (CompDiagram.openImmersion X g C)
                (ModuleCat.{u} Λ)).mapDerivedCategory
            ((etaleDerivedPushforward C.P_bar.obj.right.hom :
                  EtaleDerived C.P_bar.obj.right.left Λ ⥤
                    EtaleDerived C.P_g.obj.right.left Λ) ⋙
              (etaleDerivedPushforward C.P_g.obj.right.hom :
                EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ))).inv ≫
        whiskerRight (shriekComp X g C Λ)
          ((etaleDerivedPushforward C.P_bar.obj.right.hom :
                EtaleDerived C.P_bar.obj.right.left Λ ⥤
                  EtaleDerived C.P_g.obj.right.left Λ) ⋙
            (etaleDerivedPushforward C.P_g.obj.right.hom :
              EtaleDerived C.P_g.obj.right.left Λ ⥤ EtaleDerived Z Λ)) ≫
        whiskerLeft
          (etaleExtensionByZero
              (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)
              (ModuleCat.{u} Λ)).mapDerivedCategory
          (pushforwardCompIso X g C Λ).hom :=
  sorry

/-- The comparison `Rf_! ⋙ Rg_! ⟶ R(g ∘ f)_!` is an isomorphism on objects
of `D⁺_tors(X_étale, Λ)`. -/
theorem comp_isIso_of_isGE_isTorsion
    (K : EtaleDerived X.left Λ) (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    [DerivedCategory.IsGE K n] :
    IsIso (comp_app X g C Λ K) :=
  sorry

/-- If `Λ` is a torsion ring, the comparison `Rf_! ⋙ Rg_! ⟶ R(g ∘ f)_!` is
an isomorphism of functors on `D(X_étale, Λ)`. -/
theorem comp_isIso_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) :
    IsIso (comp X g C Λ) :=
  sorry

/-- If `Λ` is a torsion ring, package `comp` as an isomorphism of
compactification models. -/
def compIso (hΛ : AddMonoid.IsTorsion Λ) :
    compDomain X g C Λ ≅ compCodomain X g C Λ :=
  @asIso _ _ _ _ (comp X g C Λ) (comp_isIso_of_isTorsion X g C Λ hΛ)


end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
