/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.GroupTheory.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap63.Lemma_63_4_3
public import stacks_project.Chap63.Lemma_63_8_6_Comparison
public import stacks_project.Chap63.Remark_63_10_9

/-!
# Compactification independence of derived étale lower shriek

Canonical comparison of the compactification models `R f̄_* ∘ j_!` of `Rf_!`
along a morphism of compactifications. The interior identification
`j_Q ! ≅ ambient_* ∘ j_P !` is Lemma 63.4.3 plus lower-shriek composition
along `ι P ≫ ambientMap φ = ι Q` and the proper identification
`ambient_! ≅ ambient_*`. The derived transition uses the actual 63.8.6
comparison followed by derived Leray, without assuming j_! preserves injectives.
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

-- Local instance justification (search instability): use the supplied sheafification
-- proof before searching the section's over-site families for weak sheafification.
attribute [local instance 10000] HasSheafify.isRightAdjoint

namespace CompactificationTransition
section ExtensionByZeroLowerShriek

variable (Λ : Type u) [CommRing Λ]
variable {U T : Scheme.{u}} (j : U ⟶ T) [Etale j]
variable [HasSheafCompose U.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose T.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]
variable [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [T.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

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
  (sheafPullback.compSheafComposeIso
      (etaleRestriction j) (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
      U.smallEtaleTopology T.smallEtaleTopology).app F

variable [LocallyQuasiFinite j]

/-- The forward extension-by-zero comparison after forgetting coefficients. -/
def extensionByZeroLowerShriekHomAb
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((extensionByZero_compSheafCompose Λ j F).hom ≫
        ((extensionByZeroIsoLowerShriek j).app
            ((sheafCompose U.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        ((lowerShriekModule_forgetAbelianIso j Λ).app F).inv)

/-- The reverse extension-by-zero comparison after forgetting coefficients. -/
def extensionByZeroLowerShriekInvAb
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  (((lowerShriekModule_forgetAbelianIso j Λ).app F).hom ≫
        ((extensionByZeroIsoLowerShriek j).symm.app
            ((sheafCompose U.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (extensionByZero_compSheafCompose Λ j F).inv)

/-- The specified forward comparison commutes with coefficient scalars. -/
theorem extensionByZeroLowerShriekHomAb_linear
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleSheafHomLinear (extensionByZeroLowerShriekHomAb Λ j F) := sorry

/-- The specified reverse comparison commutes with coefficient scalars. -/
theorem extensionByZeroLowerShriekInvAb_linear
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleSheafHomLinear (extensionByZeroLowerShriekInvAb Λ j F) := sorry

/-- The actual extension-by-zero comparison rebundles only these coefficient-linear maps. -/
def extensionByZeroIsoLowerShriekModule_app
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F ≅
      (lowerShriekModule j Λ).obj F where
  hom := liftEtaleModuleSheafHom (extensionByZeroLowerShriekHomAb Λ j F)
    (extensionByZeroLowerShriekHomAb_linear Λ j F)
  inv := liftEtaleModuleSheafHom (extensionByZeroLowerShriekInvAb Λ j F)
    (extensionByZeroLowerShriekInvAb_linear Λ j F)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheaf-level identification of étale extension by zero with finite-support
lower shriek on étale sheaves of `Λ`-modules. -/
def extensionByZeroIsoLowerShriekModule :
    etaleExtensionByZero j (ModuleCat.{u} Λ) ≅ lowerShriekModule j Λ :=
  NatIso.ofComponents (extensionByZeroIsoLowerShriekModule_app Λ j) sorry

/-- The objectwise identification is the component of
`extensionByZeroIsoLowerShriekModule`. -/
theorem extensionByZeroIsoLowerShriekModule_app_eq
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    extensionByZeroIsoLowerShriekModule_app Λ j F =
      (extensionByZeroIsoLowerShriekModule Λ j).app F :=
  sorry

/-- Exact extension by zero and exact finite-support shriek induce the actual derived isomorphism. -/
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
  Functor.MapDerivedCategory.functorIso (extensionByZeroIsoLowerShriekModule Λ j)

end ExtensionByZeroLowerShriek
end CompactificationTransition

open CompactificationTransition

/-- Small-étale module sheaves admit K-injective resolutions, giving total
right derivation of an additive functor with this Grothendieck source.
This is existence of a derived functor, not preservation of injectives by j_!. -/
instance compactificationModuleSheafFunctor_hasRightDerived
    {S T : Scheme.{u}} {Λ : Type u} [CommRing Λ]
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)) [F.Additive] :
    HasRightDerivedFunctor (RightDerived.Cochain.toDerived F)
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) := sorry

/-- Étale module direct image is additive, being actual precomposition on sections. -/
instance compactificationModulePushforward_additive
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [CommRing Λ] :
    (etaleModulePushforward f Λ).Additive := sorry

/-- Pin the universal-property witness to the existing étale-derived-pushforward
spelling, which is definitionally the cochain total right-derived functor. -/
instance compactificationDerivedPushforward_isRightDerived
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

namespace etaleDerivedLowerShriek

variable {Y : Scheme.{u}} {X : Over Y}

/-- A morphism of compactifications commutes with the structure maps to `Y`. -/
theorem ambientMap_comp_structure {P Q : Of Y X} (φ : P ⟶ Q) :
    Of.ambientMap φ ≫ Q.obj.right.hom = P.obj.right.hom :=
  Over.w φ.hom.right

/-- A morphism of compactifications is proper, by cancellation of properness
over `Y`. -/
instance instIsProper_ambientMap {P Q : Of Y X} (φ : P ⟶ Q) :
    IsProper (Of.ambientMap φ) :=
  sorry

variable (X) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable {P Q : Of Y X} (φ : P ⟶ Q)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Q.obj.right.left.Etale,
  HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose Q.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Q.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι Q)).op]
variable [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback Q.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    Q.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback Q.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      Q.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback (Of.ambientMap φ)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Q.obj.right.left.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [(etaleModulePushforward (Of.ambientMap φ) Λ).Additive]
variable [(etaleModulePushforward Q.obj.right.hom Λ).Additive]
variable [(etaleModulePushforward P.obj.right.hom Λ).Additive]

/-- Interior identification `j_Q ! ≅ ambient_* ∘ j_P !`, obtained by
transporting `extensionByZeroIsoLowerShriek` across lower-shriek composition
along `ι P ≫ ambientMap φ = ι Q` and the proper identification
`ambient_! ≅ ambient_*`. -/
def interiorComparisonIso :
    etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ) ≅
      etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ) ⋙
        etaleModulePushforward (Of.ambientMap φ) Λ :=
  let eQ :
      etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ) ≅
        lowerShriekModule (Of.ι Q) Λ :=
    extensionByZeroIsoLowerShriekModule Λ (Of.ι Q)
  let eP :
      etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ) ≅
        lowerShriekModule (Of.ι P) Λ :=
    extensionByZeroIsoLowerShriekModule Λ (Of.ι P)
  let c :
      lowerShriekModule (Of.ι Q) Λ ≅
        lowerShriekModule (Of.ι P) Λ ⋙
          etaleModulePushforward (Of.ambientMap φ) Λ :=
    lowerShriekModule_compProperIso (Of.ι P) (Of.ambientMap φ)
      (Of.ι_comp_ambientMap φ) Λ
  eQ ≪≫ c ≪≫
    isoWhiskerRight eP.symm (etaleModulePushforward (Of.ambientMap φ) Λ)

/-- Interior comparison `j_Q ! ⟶ ambient_* ∘ j_P !` along a morphism of
compactifications. -/
def interiorComparison :
    etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ) ⟶
      etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ) ⋙
        etaleModulePushforward (Of.ambientMap φ) Λ :=
  (interiorComparisonIso X Λ φ).hom

/-- The interior comparison is the forward map of `interiorComparisonIso`. -/
theorem interiorComparison_eq :
    interiorComparison X Λ φ = (interiorComparisonIso X Λ φ).hom :=
  sorry

/-- Underived Leray comparison of compactification structure maps:
`j_P ! ⋙ ambient_* ⋙ Q_* ⟶ j_P ! ⋙ P_*`. -/
def pushforwardLeray_underived :
    etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ) ⋙
        (etaleModulePushforward (Of.ambientMap φ) Λ ⋙
          etaleModulePushforward Q.obj.right.hom Λ) ⟶
      etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ) ⋙
        etaleModulePushforward P.obj.right.hom Λ :=
  whiskerLeft
    (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))
    ((etaleModulePushforwardCompIso (Of.ambientMap φ) Q.obj.right.hom).hom ≫
      (etaleModulePushforwardCongr (ambientMap_comp_structure φ)).hom)

/-- Underived comparison of compactification models
`j_Q ! ⋙ Q_* ⟶ j_P ! ⋙ P_*`. -/
def modelComparison_underived :
    etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ) ⋙
        etaleModulePushforward Q.obj.right.hom Λ ⟶
      etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ) ⋙
        etaleModulePushforward P.obj.right.hom Λ :=
  whiskerRight (interiorComparison X Λ φ)
      (etaleModulePushforward Q.obj.right.hom Λ) ≫
    (Functor.associator
        (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))
        (etaleModulePushforward (Of.ambientMap φ) Λ)
        (etaleModulePushforward Q.obj.right.hom Λ)).hom ≫
    pushforwardLeray_underived X Λ φ

/-- Source comparison J_Q ⟶ J_P ⋙ Rg_*: exact extension comparison,
the actual 63.8.6 derived map, and the reverse exact extension comparison. -/
def derivedInteriorComparison :
    (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).mapDerivedCategory ⟶
      (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward (Of.ambientMap φ) :
          EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Q.obj.right.left Λ) :=
  (extensionByZeroDerivedIsoLowerShriekModule Λ (Of.ι Q)).hom ≫
    etaleDerivedLowerShriekProper (Of.ι P) (Of.ambientMap φ)
      (Of.ι_comp_ambientMap φ) Λ ≫
    (isoWhiskerRight (extensionByZeroDerivedIsoLowerShriekModule Λ (Of.ι P)).symm
      (etaleDerivedPushforward (Of.ambientMap φ))).hom

/-- The cochain unit for the genuine iterated derived direct images Rg_* ⋙ Rq_*.
It applies the q-unit and then the g-unit, after the canonical termwise-composition iso. -/
def pushforwardLerayUnit :
    RightDerived.Cochain.toDerived
      (etaleModulePushforward (Of.ambientMap φ) Λ ⋙
        etaleModulePushforward Q.obj.right.hom Λ) ⟶
      (DerivedCategory.Q :
        CochainComplex (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived P.obj.right.left Λ) ⋙
        ((etaleDerivedPushforward (Of.ambientMap φ) :
          EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Q.obj.right.left Λ) ⋙
            (etaleDerivedPushforward Q.obj.right.hom :
              EtaleDerived Q.obj.right.left Λ ⥤ EtaleDerived Y Λ)) :=
  (isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleModulePushforward (Of.ambientMap φ) Λ ⋙
        etaleModulePushforward Q.obj.right.hom Λ)) (ComplexShape.up ℤ)).symm
    (DerivedCategory.Q :
      CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        EtaleDerived Y Λ)).hom ≫
    (Functor.associator
      ((etaleModulePushforward (Of.ambientMap φ) Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      ((etaleModulePushforward Q.obj.right.hom Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y Λ)).hom ≫
    RightDerived.Composition.iteratedUnit
      (RightDerived.Cochain.unit (etaleModulePushforward (Of.ambientMap φ) Λ))
      (RightDerived.Cochain.unit (etaleModulePushforward Q.obj.right.hom Λ))

/-- Étale inverse image is exact, so direct image preserves K-injectives.
Consequently this particular iterated direct-image unit is a right-derived model. -/
instance pushforwardLeray_isRightDerived :
    ((etaleDerivedPushforward (Of.ambientMap φ) :
      EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Q.obj.right.left Λ) ⋙
        (etaleDerivedPushforward Q.obj.right.hom :
          EtaleDerived Q.obj.right.left Λ ⥤ EtaleDerived Y Λ)).IsRightDerivedFunctor
      (pushforwardLerayUnit X Λ φ)
      (HomologicalComplex.quasiIso
        (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) := sorry

/-- Actual derived Leray: uniqueness for the iterated direct-image unit, transported
along the specified underived composition iso and compactification triangle. -/
def pushforwardLerayIso :
    (etaleDerivedPushforward (Of.ambientMap φ) :
      EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Q.obj.right.left Λ) ⋙
        (etaleDerivedPushforward Q.obj.right.hom :
          EtaleDerived Q.obj.right.left Λ ⥤ EtaleDerived Y Λ) ≅
      etaleDerivedPushforward P.obj.right.hom :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        EtaleDerived P.obj.right.left Λ)
    (HomologicalComplex.quasiIso
      (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (pushforwardLerayUnit X Λ φ)
    (RightDerived.Cochain.unit (etaleModulePushforward P.obj.right.hom Λ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModulePushforwardCompIso (Of.ambientMap φ) Q.obj.right.hom ≪≫
          etaleModulePushforwardCongr (ambientMap_comp_structure φ)) (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y Λ))

/-- Canonical source transition: first the derived interior comparison, then
derived Leray. Resolutions occur after extension by zero. -/
def isoOfHom :
    (etaleDerivedLowerShriek X Q :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⟶
      (etaleDerivedLowerShriek X P :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) :=
  whiskerRight (derivedInteriorComparison X Λ φ)
      (etaleDerivedPushforward Q.obj.right.hom) ≫
    (Functor.associator
      (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
      (etaleDerivedPushforward (Of.ambientMap φ))
      (etaleDerivedPushforward Q.obj.right.hom)).hom ≫
    whiskerLeft (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
      (pushforwardLerayIso X Λ φ).hom

/-- Component of `isoOfHom` at an object of `D(X_étale, Λ)`. -/
def isoOfHom_app (K : EtaleDerived X.left Λ) :
    ((etaleDerivedLowerShriek X Q :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).obj K) ⟶
      ((etaleDerivedLowerShriek X P :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).obj K) :=
  (isoOfHom X Λ φ).app K

/-- The objectwise comparison is the component of `isoOfHom`. -/
theorem isoOfHom_app_eq (K : EtaleDerived X.left Λ) :
    isoOfHom_app X Λ φ K = (isoOfHom X Λ φ).app K :=
  sorry

/-- The transition is the specified derived interior map followed by Leray. -/
theorem isoOfHom_eq :
    isoOfHom X Λ φ =
      whiskerRight (derivedInteriorComparison X Λ φ)
          (etaleDerivedPushforward Q.obj.right.hom) ≫
        (Functor.associator
          (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
          (etaleDerivedPushforward (Of.ambientMap φ))
          (etaleDerivedPushforward Q.obj.right.hom)).hom ≫
        whiskerLeft (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
          (pushforwardLerayIso X Λ φ).hom := rfl

/-- The comparison attached to the identity morphism of a compactification is
the identity. -/
theorem isoOfHom_refl :
    isoOfHom X Λ (𝟙 P) =
      𝟙 (etaleDerivedLowerShriek X P :
          EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) :=
  sorry

variable {R : Of Y X} (ψ : Q ⟶ R)
variable [HasSheafify R.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : R.obj.right.left.Etale,
  HasWeakSheafify (R.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf R.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι R)).op.HasLeftKanExtension F]
variable [HasSheafCompose R.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify R.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [R.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι R)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι R)).op]
variable [(etaleExtensionByZero (Of.ι R) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι R) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι R) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback R.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    R.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback R.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      R.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf R.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward R.obj.right.hom Λ).Additive]
variable [((smallEtalePullback (Of.ambientMap ψ)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) R.obj.right.left.smallEtaleTopology
    Q.obj.right.left.smallEtaleTopology).Additive]
variable [(etaleModulePushforward (Of.ambientMap ψ) Λ).Additive]
variable [((smallEtalePullback (Of.ambientMap (φ ≫ ψ))).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) R.obj.right.left.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [(etaleModulePushforward (Of.ambientMap (φ ≫ ψ)) Λ).Additive]

/-- Comparisons along morphisms of compactifications reverse composition. -/
theorem isoOfHom_comp :
    isoOfHom X Λ (φ ≫ ψ) =
      (isoOfHom X Λ ψ ≫ isoOfHom X Λ φ :
        (etaleDerivedLowerShriek X R :
            EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⟶
          (etaleDerivedLowerShriek X P :
            EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)) :=
  sorry

/-- On a torsion coefficient ring, the compactification models of `Rf_!` are
isomorphic. -/
theorem independent (hΛ : AddMonoid.IsTorsion Λ) :
    IsIsomorphic
      (etaleDerivedLowerShriek X P :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)
      (etaleDerivedLowerShriek X Q :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) :=
  sorry

/-- On objects of `D⁺_tors(X_étale, Λ)`, the compactification models of `Rf_!`
are isomorphic. -/
theorem independent_obj
    (K : EtaleDerived X.left Λ) (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    [DerivedCategory.IsGE K n] :
    IsIsomorphic
      ((etaleDerivedLowerShriek X P :
          EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).obj K)
      ((etaleDerivedLowerShriek X Q :
          EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).obj K) :=
  sorry

end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
