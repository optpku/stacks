/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap63.Lemma_63_3_6
public import stacks_project.Chap63.Lemma_63_8_1_Comparison
public import stacks_project.Chap63.Lemma_63_10_3
public import stacks_project.Chap63.«63_11_4_1_UpperShriek»

/-!
# Uniqueness comparison for derived étale upper shriek

Along a finite compactification of a separated quasi-finite morphism, the
compactification presentation `Rf^!` is the mate of `Rf_! ≅ f_!` against the
Section 63.7 derived adjunction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.QuasiFinite X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [IsFinite P.obj.right.hom]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
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
variable [PreservesFiniteLimits
  ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology)]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Compactification.Of.ι P)).op]
variable [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]

/-- The abelian compactification identification `f_! ≅ π_* ∘ j_!` after
transporting along `X.hom = ι P ≫ P.obj.right.hom`. -/
def etaleAbelianLowerShriekCompactifyPushforwardIso :
    etaleLowerShriek X.hom ≅
      abelianExtensionByZero (Compactification.Of.ι P) ⋙
        etaleAbelianPushforward P.obj.right.hom :=
  etaleLowerShriekCompactifyIso_eq (Compactification.Of.ι P) P.obj.right.hom
      X.hom (Over.w P.obj.hom) ≪≫
    isoWhiskerLeft (abelianExtensionByZero (Compactification.Of.ι P))
      (etaleLowerShriekIso P.obj.right.hom)

/-- Forgetting coefficients identifies `π_* (j_! F)` with
`π_*^{ab} (j_!^{ab} (forget F))`. -/
def etaleModuleCompactifyPushforward_forgetLeft
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleModulePushforward P.obj.right.hom Λ).obj
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ)).obj F)) ≅
      (etaleAbelianPushforward P.obj.right.hom).obj
        ((abelianExtensionByZero (Compactification.Of.ι P)).obj
          ((sheafCompose X.left.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :=
  (etaleModulePushforward_compSheafComposeIso P.obj.right.hom Λ).app
      ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)).obj F) ≪≫
    (etaleAbelianPushforward P.obj.right.hom).mapIso
      ((Functor.sheafPullback.compSheafComposeIso
          (etaleRestriction (Compactification.Of.ι P))
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
          X.left.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology).app F)

/-- Forgetting coefficients identifies `f_! F` with `lowerShriek (forget F)`. -/
def etaleModuleCompactifyPushforward_forgetRight
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule X.hom Λ).obj F) ≅
      (lowerShriek X.hom).obj
        ((sheafCompose X.left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) :=
  (lowerShriekModule_forgetFunctorIso X.hom Λ).app F

/-- The component of the sheaf-level identification `π_* ∘ j_! ≅ f_!` at a sheaf
of `Λ`-modules. -/
def etaleModuleLowerShriekCompactifyPushforwardIso_app
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology
        P.obj.right.left.smallEtaleTopology).obj
        ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} Λ)).obj F) ≅
      (lowerShriekModule X.hom Λ).obj F where
  hom :=
    liftModuleSheafHom
      ((etaleModuleCompactifyPushforward_forgetLeft X Λ P F).hom ≫
        ((etaleAbelianLowerShriekCompactifyPushforwardIso X P).symm.app
            ((sheafCompose X.left.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        ((lowerShriekIsoEtaleLowerShriek X.hom).symm.app
            ((sheafCompose X.left.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (etaleModuleCompactifyPushforward_forgetRight X Λ F).inv)
  inv :=
    liftModuleSheafHom
      ((etaleModuleCompactifyPushforward_forgetRight X Λ F).hom ≫
        ((lowerShriekIsoEtaleLowerShriek X.hom).app
            ((sheafCompose X.left.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        ((etaleAbelianLowerShriekCompactifyPushforwardIso X P).app
            ((sheafCompose X.left.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (etaleModuleCompactifyPushforward_forgetLeft X Λ P F).inv)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheaf-level compactification identification `π_* ∘ j_! ≅ f_!` on étale
sheaves of `Λ`-modules. -/
def etaleModuleLowerShriekCompactifyPushforwardIso :
    etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ) ⋙
        (smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology ≅
      lowerShriekModule X.hom Λ :=
  NatIso.ofComponents
    (etaleModuleLowerShriekCompactifyPushforwardIso_app X Λ P) sorry

/-- The exact derived functor `π_* ∘ j_!` agrees with Section 63.7's
`lowerShriekModuleDerived`. -/
def etaleDerivedExactLowerShriekIsoModuleDerived :
    etaleDerivedExactLowerShriek X P ≅ lowerShriekModuleDerived X.hom Λ :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)))
      (ExactFunctor.of
        ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology))).symm ≪≫
    Functor.MapDerivedCategory.functorIso
      (etaleModuleLowerShriekCompactifyPushforwardIso X Λ P)

/-- The compactification presentation `Rf_!` agrees with Section 63.7's
`f_!` on unbounded derived categories. -/
def etaleDerivedLowerShriekIsoModuleDerived :
    (etaleDerivedLowerShriek X P :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ≅
      lowerShriekModuleDerived X.hom Λ :=
  etaleDerivedLowerShriekIso X P ≪≫
    etaleDerivedExactLowerShriekIsoModuleDerived X Λ P

/-- The uniqueness isomorphism identifying compactification `Rf^!` with the
K-injective derived upper shriek of Section 63.7, as the mate of
`etaleDerivedLowerShriekIsoModuleDerived`. -/
def etaleDerivedUpperShriekComparisonIso :
    etaleDerivedUpperShriek X Λ P ≅ upperShriekModuleDerived X.hom Λ :=
  conjugateIsoEquiv
    (etaleDerivedLowerShriekAdjunction X Λ P)
    (lowerShriekModuleDerivedAdjunction X.hom Λ)
    (etaleDerivedLowerShriekIsoModuleDerived X Λ P).symm

/-- Objectwise evaluation of `etaleDerivedUpperShriekComparisonIso`. -/
def etaleDerivedUpperShriekComparisonIso_app (K : EtaleDerived Y Λ) :
    (etaleDerivedUpperShriek X Λ P).obj K ≅
      (upperShriekModuleDerived X.hom Λ).obj K :=
  (etaleDerivedUpperShriekComparisonIso X Λ P).app K

/-- The comparison isomorphism is the conjugate of the inverse of
`etaleDerivedLowerShriekIsoModuleDerived` along the two derived adjunctions. -/
theorem etaleDerivedUpperShriekComparisonIso_spec :
    etaleDerivedUpperShriekComparisonIso X Λ P =
      conjugateIsoEquiv
        (etaleDerivedLowerShriekAdjunction X Λ P)
        (lowerShriekModuleDerivedAdjunction X.hom Λ)
        (etaleDerivedLowerShriekIsoModuleDerived X Λ P).symm :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
