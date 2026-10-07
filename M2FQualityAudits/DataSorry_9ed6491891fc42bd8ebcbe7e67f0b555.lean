module

import Lean

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap63.Lemma_63_3_12_Comparison
public import stacks_project.Chap63.Lemma_63_7_1_Adjunction
public import stacks_project.Chap63.Lemma_63_8_1_Comparison
public import stacks_project.Chap63.Lemma_63_8_5_Pullback

/-!
# Derived base-change mates for proper pushforward and compact support

Module-valued Sites mates for `Rf_*` and `g_!` along a cartesian square, used
to assemble the 2×3 diagram of Lemma 63.8.5.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (Λ : Type u) [CommRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]

/-- The underived Sites pullback mate `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of a cartesian
square, obtained as the right mate of the inverse-image square. -/
def etaleModulePushforwardBaseChange :
    etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback g Λ ⟶
      etaleModuleSheafPullback g' Λ ⋙ etaleModulePushforward f' Λ :=
  DerivedBaseChange.map
    ((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback f').sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      Y'.smallEtaleTopology X'.smallEtaleTopology)
    (etaleModuleSheafPullback_square f g f' g' h_cart Λ)

/-- The underived mate is the right mate of the inverse-image square. -/
theorem etaleModulePushforwardBaseChange_eq :
    etaleModulePushforwardBaseChange f g f' g' h_cart Λ =
      DerivedBaseChange.map
        ((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
          Y.smallEtaleTopology X.smallEtaleTopology)
        ((smallEtalePullback f').sheafAdjunctionContinuous (ModuleCat.{u} Λ)
          Y'.smallEtaleTopology X'.smallEtaleTopology)
        (etaleModuleSheafPullback_square f g f' g' h_cart Λ) :=
  sorry

variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]

section CompactSupportBaseChange

variable [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
variable [IsSeparated f'] [LocallyOfFiniteType f'] [LocallyQuasiFinite f']
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]

/-- Forgetting coefficients identifies `g⁻¹ (f_! F)` with
`g⁻¹ ((etaleLowerShriek f) (forget F))` along `lowerShriekModule_forget`
and `lowerShriekIsoEtaleLowerShriek`. -/
def lowerShriekModuleBaseChange_forgetLeft
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleModuleSheafPullback g Λ).obj ((lowerShriekModule f Λ).obj F)) ≅
      (etaleAbelianSheafPullback g).obj
        ((etaleLowerShriek f).obj (etaleModuleForget Λ F)) :=
  (etaleModuleSheafPullback_compSheafComposeIso g Λ).app
      ((lowerShriekModule f Λ).obj F) ≪≫
    (etaleAbelianSheafPullback g).mapIso
      ((lowerShriekModule_forgetFunctorIso f Λ).app F ≪≫
        (lowerShriekIsoEtaleLowerShriek f).app (etaleModuleForget Λ F))

/-- Forgetting coefficients identifies `f'_! ((g')⁻¹ F)` with
`(etaleLowerShriek f') ((g')⁻¹ (forget F))`. -/
def lowerShriekModuleBaseChange_forgetRight
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule f' Λ).obj ((etaleModuleSheafPullback g' Λ).obj F)) ≅
      (etaleLowerShriek f').obj
        ((etaleAbelianSheafPullback g').obj (etaleModuleForget Λ F)) :=
  (lowerShriekModule_forgetFunctorIso f' Λ).app
      ((etaleModuleSheafPullback g' Λ).obj F) ≪≫
    (lowerShriekIsoEtaleLowerShriek f').app
      (etaleModuleForget Λ ((etaleModuleSheafPullback g' Λ).obj F)) ≪≫
    (etaleLowerShriek f').mapIso
      ((etaleModuleSheafPullback_compSheafComposeIso g' Λ).app F)

/-- The canonical comparison `g⁻¹ f_! ⟶ f'_! (g')⁻¹` on étale sheaves of
`Λ`-modules, obtained by lifting the abelian comparison of Lemma 63.3.12
along `forget₂`. -/
def lowerShriekModuleBaseChange :
    lowerShriekModule f Λ ⋙ etaleModuleSheafPullback g Λ ⟶
      etaleModuleSheafPullback g' Λ ⋙ lowerShriekModule f' Λ where
  app F :=
    liftModuleSheafHom
      ((lowerShriekModuleBaseChange_forgetLeft f g Λ F).hom ≫
        etaleLowerShriekBaseChange_app f g f' g' h_cart
          (etaleModuleForget Λ F) ≫
        (lowerShriekModuleBaseChange_forgetRight f' g' Λ F).inv)
  naturality := sorry

/-- The comparison at a sheaf of `Λ`-modules. -/
def lowerShriekModuleBaseChange_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleModuleSheafPullback g Λ).obj ((lowerShriekModule f Λ).obj F) ⟶
      (lowerShriekModule f' Λ).obj ((etaleModuleSheafPullback g' Λ).obj F) :=
  (lowerShriekModuleBaseChange f g f' g' h_cart Λ).app F

/-- The objectwise comparison is the component of
`lowerShriekModuleBaseChange`. -/
theorem lowerShriekModuleBaseChange_app_eq
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    lowerShriekModuleBaseChange_app f g f' g' h_cart Λ F =
      (lowerShriekModuleBaseChange f g f' g' h_cart Λ).app F :=
  sorry

/-- After forgetting coefficients and identifying compact support with
`etaleLowerShriek`, the module comparison is the comparison of
Lemma 63.3.12. -/
theorem lowerShriekModuleBaseChange_eq_etaleLowerShriekBaseChange
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).map
        (lowerShriekModuleBaseChange_app f g f' g' h_cart Λ F) =
      (lowerShriekModuleBaseChange_forgetLeft f g Λ F).hom ≫
        etaleLowerShriekBaseChange_app f g f' g' h_cart
          (etaleModuleForget Λ F) ≫
        (lowerShriekModuleBaseChange_forgetRight f' g' Λ F).inv :=
  sorry

/-- Derived compact-support base change `g⁻¹ f_! ⟶ f'_! (g')⁻¹` on
`D(X_étale, Λ)`, obtained by applying `mapDerivedCategory` to the underived
comparison. -/
def lowerShriekModuleDerivedBaseChange :
    lowerShriekModuleDerived f Λ ⋙ etaleModuleDerivedInverseImage g Λ ⟶
      etaleModuleDerivedInverseImage g' Λ ⋙ lowerShriekModuleDerived f' Λ :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (lowerShriekModule f Λ))
      (ExactFunctor.of (etaleModuleSheafPullback g Λ))).inv ≫
    ExactFunctor.MapDerivedCategory.map
      (ObjectProperty.homMk
        (lowerShriekModuleBaseChange f g f' g' h_cart Λ) :
        ExactFunctor.of
            (lowerShriekModule f Λ ⋙ etaleModuleSheafPullback g Λ) ⟶
          ExactFunctor.of
            (etaleModuleSheafPullback g' Λ ⋙ lowerShriekModule f' Λ)) ≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (etaleModuleSheafPullback g' Λ))
      (ExactFunctor.of (lowerShriekModule f' Λ))).hom

/-- The derived compact-support comparison at an object of `D(X_étale, Λ)`. -/
def lowerShriekModuleDerivedBaseChange_app (K : EtaleDerived X Λ) :
    (etaleModuleDerivedInverseImage g Λ).obj
      ((lowerShriekModuleDerived f Λ).obj K) ⟶
      (lowerShriekModuleDerived f' Λ).obj
        ((etaleModuleDerivedInverseImage g' Λ).obj K) :=
  (lowerShriekModuleDerivedBaseChange f g f' g' h_cart Λ).app K

end CompactSupportBaseChange

/-- The iterated cochain unit for `Rf_* ⋙ g⁻¹`, using exactness of inverse
image. -/
def etaleDerivedPushforwardBaseChange_srcUnit
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback g Λ) ⟶
      DerivedCategory.Q ⋙
        (etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage g Λ) :=
  (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback g Λ))
        (ComplexShape.up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y' Λ)).hom ≫
    (Functor.associator
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      ((etaleModuleSheafPullback g Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y' Λ)).hom ≫
    whiskerLeft
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (etaleModuleSheafPullback g Λ).mapDerivedCategoryFactors.inv ≫
    (Functor.associator
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y Λ)
      (etaleModuleDerivedInverseImage g Λ)).inv ≫
    whiskerRight (RightDerived.Cochain.unit (etaleModulePushforward f Λ))
      (etaleModuleDerivedInverseImage g Λ) ≫
    (Functor.associator
      (DerivedCategory.Q :
        CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived X Λ)
      (etaleDerivedPushforward f)
      (etaleModuleDerivedInverseImage g Λ)).hom

/-- Exactness of inverse image makes `Rf_* ⋙ g⁻¹` a right-derived functor of
`f_* ⋙ g⁻¹`. -/
instance etaleDerivedPushforwardBaseChange_src_isRightDerived
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    (etaleDerivedPushforward f ⋙
        etaleModuleDerivedInverseImage g Λ).IsRightDerivedFunctor
      (etaleDerivedPushforwardBaseChange_srcUnit f g Λ)
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  sorry

/-- The iterated cochain unit for `(g')⁻¹ ⋙ Rf'_*`. -/
def etaleDerivedPushforwardBaseChange_tgtUnit
    [(etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (etaleModuleSheafPullback g' Λ ⋙ etaleModulePushforward f' Λ) ⟶
      DerivedCategory.Q ⋙
        (etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f') :=
  RightDerived.Cochain.ExactFirst.unit
    (ExactFunctor.of (etaleModuleSheafPullback g' Λ))
    (etaleModulePushforward f' Λ)

/-- Exactness of inverse image makes `(g')⁻¹ ⋙ Rf'_*` a right-derived functor
of `(g')⁻¹ ⋙ f'_*`. -/
instance etaleDerivedPushforwardBaseChange_tgt_isRightDerived
    [(etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    (etaleModuleDerivedInverseImage g' Λ ⋙
        etaleDerivedPushforward f').IsRightDerivedFunctor
      (etaleDerivedPushforwardBaseChange_tgtUnit f' g' Λ)
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  sorry

/-- Derived base-change mate `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of a cartesian square,
the unbounded `D(X, Λ)` form of the comparison of Étale Cohomology,
Section 59.86. -/
def etaleDerivedPushforwardBaseChange
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback g Λ).Additive]
    [(etaleModuleSheafPullback g' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage g Λ ⟶
      etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f' :=
  rightDerivedNatTrans
    (etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage g Λ)
    (etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f')
    (etaleDerivedPushforwardBaseChange_srcUnit f g Λ)
    (etaleDerivedPushforwardBaseChange_tgtUnit f' g' Λ)
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (whiskerRight
      (NatTrans.mapHomologicalComplex
        (etaleModulePushforwardBaseChange f g f' g' h_cart Λ)
        (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y' Λ))

/-- The derived `Rf_*` base-change comparison at an object of `D(X_étale, Λ)`. -/
def etaleDerivedPushforwardBaseChange_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback g Λ).Additive]
    [(etaleModuleSheafPullback g' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X Λ) :
    (etaleModuleDerivedInverseImage g Λ).obj
      ((etaleDerivedPushforward f).obj K) ⟶
      (etaleDerivedPushforward f').obj
        ((etaleModuleDerivedInverseImage g' Λ).obj K) :=
  (etaleDerivedPushforwardBaseChange f g f' g' h_cart Λ).app K

/-- The derived `Rf_*` mate is the right-derived natural transformation of the
underived Sites mate. -/
theorem etaleDerivedPushforwardBaseChange_eq
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback g Λ).Additive]
    [(etaleModuleSheafPullback g' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforwardBaseChange f g f' g' h_cart Λ =
      rightDerivedNatTrans
        (etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage g Λ)
        (etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f')
        (etaleDerivedPushforwardBaseChange_srcUnit f g Λ)
        (etaleDerivedPushforwardBaseChange_tgtUnit f' g' Λ)
        (HomologicalComplex.quasiIso
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
        (whiskerRight
          (NatTrans.mapHomologicalComplex
            (etaleModulePushforwardBaseChange f g f' g' h_cart Λ)
            (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
              EtaleDerived Y' Λ)) :=
  sorry

section BaseChangeDiagram

variable {X₁ Y₁ X'₁ Y'₁ : Scheme.{u}}
variable (b : Y₁ ⟶ Y) (b' : Y'₁ ⟶ Y') (a : X₁ ⟶ X) (a' : X'₁ ⟶ X')
variable (f₁ : X₁ ⟶ Y₁) (f'₁ : X'₁ ⟶ Y'₁) (g₁ : Y'₁ ⟶ Y₁) (g'₁ : X'₁ ⟶ X₁)
variable (h_sq : CommSq g' f' f g) (h_sq₁ : CommSq g'₁ f'₁ f₁ g₁)
variable (h_Y' : IsPullback b' g₁ g b) (h_X : IsPullback a f₁ f b)
variable (h_X' : IsPullback a' f'₁ f' b') (h_back : IsPullback a' g'₁ g' a)
variable [IsProper f] [IsProper f'] [IsProper f₁] [IsProper f'₁]
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [IsSeparated g'] [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable [IsSeparated g₁] [LocallyQuasiFinite g₁] [LocallyOfFiniteType g₁]
variable [IsSeparated g'₁] [LocallyQuasiFinite g'₁] [LocallyOfFiniteType g'₁]
variable [HasWeakSheafify X₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [X₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [X₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X₁.Etale,
  HasWeakSheafify (X₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y₁.Etale,
  HasWeakSheafify (Y₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'₁.Etale,
  HasWeakSheafify (X'₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'₁.Etale,
  HasWeakSheafify (Y'₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a).op.HasLeftKanExtension P]
variable [∀ P : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a').op.HasLeftKanExtension P]
variable [∀ P : Y₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f₁).op.HasLeftKanExtension P]
variable [∀ P : Y'₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f'₁).op.HasLeftKanExtension P]
variable [∀ P : Y₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g₁).op.HasLeftKanExtension P]
variable [∀ P : X₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g'₁).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g₁ ≫ b)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (b' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f₁ ≫ b)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a ≫ f)).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f'₁ ≫ b')).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a' ≫ f')).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g'₁ ≫ a)).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a' ≫ g')).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a).op.HasLeftKanExtension P]
variable [∀ P : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a').op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b').op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a').op]

/-- Left vertical of the `2×3` diagram: the Lemma 63.8.1 comparison of the
original square, whiskered by inverse image along `b`. -/
def etaleDerivedLowerShriekPushforward_baseChange_leftVertical
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f' ⋙
        lowerShriekModuleDerived g Λ ⋙ etaleModuleDerivedInverseImage b Λ ⟶
      lowerShriekModuleDerived g' Λ ⋙
        etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage b Λ :=
  (Functor.associator
      (etaleDerivedPushforward f')
      (lowerShriekModuleDerived g Λ)
      (etaleModuleDerivedInverseImage b Λ)).inv ≫
    whiskerRight
      (etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ)
      (etaleModuleDerivedInverseImage b Λ) ≫
    (Functor.associator
      (lowerShriekModuleDerived g' Λ)
      (etaleDerivedPushforward f)
      (etaleModuleDerivedInverseImage b Λ)).hom

/-- Evaluating the left vertical at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_baseChange_leftVertical_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ) :
    (etaleModuleDerivedInverseImage b Λ).obj
      ((lowerShriekModuleDerived g Λ).obj
        ((etaleDerivedPushforward f').obj K)) ⟶
      (etaleModuleDerivedInverseImage b Λ).obj
        ((etaleDerivedPushforward f).obj
          ((lowerShriekModuleDerived g' Λ).obj K)) :=
  (etaleDerivedLowerShriekPushforward_baseChange_leftVertical
      f g f' g' Λ b h_sq).app K

/-- Right vertical of the `2×3` diagram: inverse image along `a'` followed by
the Lemma 63.8.1 comparison of the base-changed square. -/
def etaleDerivedLowerShriekPushforward_baseChange_rightVertical
    [(etaleModulePushforward f₁ Λ).Additive]
    [(etaleModulePushforward f'₁ Λ).Additive]
    [(etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ).Additive]
    [(lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleModuleDerivedInverseImage a' Λ ⋙
        etaleDerivedPushforward f'₁ ⋙ lowerShriekModuleDerived g₁ Λ ⟶
      etaleModuleDerivedInverseImage a' Λ ⋙
        lowerShriekModuleDerived g'₁ Λ ⋙ etaleDerivedPushforward f₁ :=
  whiskerLeft
    (etaleModuleDerivedInverseImage a' Λ)
    (etaleDerivedLowerShriekPushforward f₁ f'₁ g₁ g'₁ h_sq₁ Λ)

/-- Evaluating the right vertical at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_baseChange_rightVertical_app
    [(etaleModulePushforward f₁ Λ).Additive]
    [(etaleModulePushforward f'₁ Λ).Additive]
    [(etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ).Additive]
    [(lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ) :
    (lowerShriekModuleDerived g₁ Λ).obj
      ((etaleDerivedPushforward f'₁).obj
        ((etaleModuleDerivedInverseImage a' Λ).obj K)) ⟶
      (etaleDerivedPushforward f₁).obj
        ((lowerShriekModuleDerived g'₁ Λ).obj
          ((etaleModuleDerivedInverseImage a' Λ).obj K)) :=
  (etaleDerivedLowerShriekPushforward_baseChange_rightVertical
      Λ a' f₁ f'₁ g₁ g'₁ h_sq₁).app K

/-- Top horizontal of the `2×3` diagram: compact-support base change of `g`
along `h_Y'`, then `Rf'_*` base change along `h_X'`. -/
def etaleDerivedLowerShriekPushforward_baseChange_top
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'₁ Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ etaleModuleSheafPullback b' Λ).Additive]
    [(etaleModuleSheafPullback a' Λ ⋙ etaleModulePushforward f'₁ Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f' ⋙
        lowerShriekModuleDerived g Λ ⋙ etaleModuleDerivedInverseImage b Λ ⟶
      etaleModuleDerivedInverseImage a' Λ ⋙
        etaleDerivedPushforward f'₁ ⋙ lowerShriekModuleDerived g₁ Λ :=
  whiskerLeft (etaleDerivedPushforward f')
      (lowerShriekModuleDerivedBaseChange g b g₁ b' h_Y' Λ) ≫
    (Functor.associator
      (etaleDerivedPushforward f')
      (etaleModuleDerivedInverseImage b' Λ)
      (lowerShriekModuleDerived g₁ Λ)).inv ≫
    whiskerRight
      (etaleDerivedPushforwardBaseChange f' b' f'₁ a' h_X' Λ)
      (lowerShriekModuleDerived g₁ Λ) ≫
    (Functor.associator
      (etaleModuleDerivedInverseImage a' Λ)
      (etaleDerivedPushforward f'₁)
      (lowerShriekModuleDerived g₁ Λ)).hom

/-- Evaluating the top horizontal at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_baseChange_top_app
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'₁ Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ etaleModuleSheafPullback b' Λ).Additive]
    [(etaleModuleSheafPullback a' Λ ⋙ etaleModulePushforward f'₁ Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ) :
    (etaleModuleDerivedInverseImage b Λ).obj
      ((lowerShriekModuleDerived g Λ).obj
        ((etaleDerivedPushforward f').obj K)) ⟶
      (lowerShriekModuleDerived g₁ Λ).obj
        ((etaleDerivedPushforward f'₁).obj
          ((etaleModuleDerivedInverseImage a' Λ).obj K)) :=
  (etaleDerivedLowerShriekPushforward_baseChange_top
      g f' Λ b b' a' f'₁ g₁ h_Y' h_X').app K

/-- Bottom horizontal of the `2×3` diagram: `Rf_*` base change along `h_X`,
then compact-support base change of `g'` along `h_back`. -/
def etaleDerivedLowerShriekPushforward_baseChange_bottom
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f₁ Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback b Λ).Additive]
    [(etaleModuleSheafPullback a Λ ⋙ etaleModulePushforward f₁ Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    lowerShriekModuleDerived g' Λ ⋙
        etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage b Λ ⟶
      etaleModuleDerivedInverseImage a' Λ ⋙
        lowerShriekModuleDerived g'₁ Λ ⋙ etaleDerivedPushforward f₁ :=
  whiskerLeft (lowerShriekModuleDerived g' Λ)
      (etaleDerivedPushforwardBaseChange f b f₁ a h_X Λ) ≫
    (Functor.associator
      (lowerShriekModuleDerived g' Λ)
      (etaleModuleDerivedInverseImage a Λ)
      (etaleDerivedPushforward f₁)).inv ≫
    whiskerRight
      (lowerShriekModuleDerivedBaseChange g' a g'₁ a' h_back Λ)
      (etaleDerivedPushforward f₁) ≫
    (Functor.associator
      (etaleModuleDerivedInverseImage a' Λ)
      (lowerShriekModuleDerived g'₁ Λ)
      (etaleDerivedPushforward f₁)).hom

/-- Evaluating the bottom horizontal at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_baseChange_bottom_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f₁ Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback b Λ).Additive]
    [(etaleModuleSheafPullback a Λ ⋙ etaleModulePushforward f₁ Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ) :
    (etaleModuleDerivedInverseImage b Λ).obj
      ((etaleDerivedPushforward f).obj
        ((lowerShriekModuleDerived g' Λ).obj K)) ⟶
      (etaleDerivedPushforward f₁).obj
        ((lowerShriekModuleDerived g'₁ Λ).obj
          ((etaleModuleDerivedInverseImage a' Λ).obj K)) :=
  (etaleDerivedLowerShriekPushforward_baseChange_bottom
      f g' Λ b a a' f₁ g'₁ h_X h_back).app K

/-- Functor-level commutativity of the outer `2×3` rectangle. -/
theorem etaleDerivedLowerShriekPushforward_baseChange_natTrans
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f₁ Λ).Additive]
    [(etaleModulePushforward f'₁ Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ).Additive]
    [(lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback b Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ etaleModuleSheafPullback b' Λ).Additive]
    [(etaleModuleSheafPullback a Λ ⋙ etaleModulePushforward f₁ Λ).Additive]
    [(etaleModuleSheafPullback a' Λ ⋙ etaleModulePushforward f'₁ Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedLowerShriekPushforward_baseChange_top
        g f' Λ b b' a' f'₁ g₁ h_Y' h_X' ≫
      etaleDerivedLowerShriekPushforward_baseChange_rightVertical
        Λ a' f₁ f'₁ g₁ g'₁ h_sq₁ =
      etaleDerivedLowerShriekPushforward_baseChange_leftVertical
          f g f' g' Λ b h_sq ≫
        etaleDerivedLowerShriekPushforward_baseChange_bottom
          f g' Λ b a a' f₁ g'₁ h_X h_back :=
  sorry

end BaseChangeDiagram

end AlgebraicGeometry.Scheme.Etale

end


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
