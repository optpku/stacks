/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Adjunction.Mates
public import stacks_project.Chap63.Definition_63_12_1_Gamma
public import stacks_project.Chap63.Lemma_63_3_10

/-!
# Underived versus derived compactly supported H^0

Comparison maps identifying the underived group `H^0_c(X, F)` of
Definition 63.3.7 with the derived group `H^0_c(X, F)` of
Definition 63.12.1, via global sections of `j_! F` on a compactification.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Universe-lifted integers, the coefficient ring for derived étale cohomology
of abelian sheaves. -/
abbrev ULiftInt : Type u := ULift.{u} ℤ

/-- The coefficient functor sending an abelian group to the associated
`ULift ℤ`-module. -/
def addCommGrpToULiftIntModule :
    AddCommGrpCat.{u} ⥤ ModuleCat.{u} ULiftInt :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- Unfolding of `addCommGrpToULiftIntModule`. -/
theorem addCommGrpToULiftIntModule_eq :
    addCommGrpToULiftIntModule =
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv ⋙
        ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom :=
  sorry

/-- The canonical additive map from an abelian group to the associated
`ULift ℤ`-module, via the inverse of `forget₂`. -/
def addCommGrpToULiftIntModuleAddHom (A : AddCommGrpCat.{u}) :
    A →+ addCommGrpToULiftIntModule.obj A :=
  ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.inv.app A).hom

/-- Unfolding of `addCommGrpToULiftIntModuleAddHom`. -/
theorem addCommGrpToULiftIntModuleAddHom_eq (A : AddCommGrpCat.{u}) :
    addCommGrpToULiftIntModuleAddHom A =
      ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.inv.app A).hom :=
  sorry

variable {k : Type u} [Field k]
variable {X : SchemeOverField k}
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [IsOpenImmersion (Compactification.Of.ι P)]
variable [IsProper P.obj.right.hom]

/-- The interior morphism of a compactification, as an over-morphism over `k`,
is an open immersion. -/
instance isOpenImmersion_compactification_overHom :
    IsOpenImmersion P.obj.hom.left :=
  inferInstanceAs (IsOpenImmersion (Compactification.Of.ι P))
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} ULiftInt)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} ULiftInt)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u} ULiftInt)]
variable [∀ U : (Spec (CommRingCat.of k)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U)
    (ModuleCat.{u} ULiftInt)]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} ULiftInt))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} ULiftInt,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} ULiftInt)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} ULiftInt))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} ULiftInt))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} ULiftInt) (Spec (CommRingCat.of k)).smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} ULiftInt) (Spec (CommRingCat.of k)).smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
    (ComplexShape.up ℤ))]
variable [HasDerivedCategory (ModuleCat.{u} ULiftInt)]
variable [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
    (ModuleCat.{u} ULiftInt)).obj
    (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} ULiftInt)).obj
      (op (globalEtale (Spec (CommRingCat.of k))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} ULiftInt))
    (ComplexShape.up ℤ))]
variable [CompactSpace (Spec (CommRingCat.of k))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of k))]
variable [HasWeakSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous
    AddCommGrpCat.{u} P.obj.right.left.smallEtaleTopology
    X.left.smallEtaleTopology).IsRightAdjoint]
variable [X.left.smallEtaleTopology.HasSheafCompose addCommGrpToULiftIntModule]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose addCommGrpToULiftIntModule]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} ULiftInt) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} ULiftInt) AddCommGrpCat.{u})]

/-- Left Kan extensions along étale restriction of the interior over-morphism
agree with those along `Compactification.Of.ι`. -/
instance hasLeftKanExtension_etaleRestriction_compactification_overHom :
    ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction P.obj.hom.left).op.HasLeftKanExtension F :=
  inferInstanceAs
    (∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F)

/-- Left Kan extensions along small-étale pullback of the interior
over-morphism agree with those along `Compactification.Of.ι`. -/
instance hasLeftKanExtension_smallEtalePullback_compactification_overHom :
    ∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback P.obj.hom.left).op.HasLeftKanExtension G :=
  inferInstanceAs
    (∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback (Compactification.Of.ι P)).op.HasLeftKanExtension G)

/-- Right-adjointness of small-étale pushforward along the interior
over-morphism agrees with that along `Compactification.Of.ι`. -/
instance isRightAdjoint_smallEtalePullback_compactification_overHom :
    ((smallEtalePullback P.obj.hom.left).sheafPushforwardContinuous
        AddCommGrpCat.{u} P.obj.right.left.smallEtaleTopology
        X.left.smallEtaleTopology).IsRightAdjoint :=
  inferInstanceAs
    (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous
        AddCommGrpCat.{u} P.obj.right.left.smallEtaleTopology
        X.left.smallEtaleTopology).IsRightAdjoint)

/-- The sheaf of `ULift ℤ`-modules associated to an abelian small-étale sheaf. -/
def etaleAbelianToIntModuleSheaf
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt) :=
  (sheafCompose X.left.smallEtaleTopology addCommGrpToULiftIntModule).obj F

/-- Unfolding of `etaleAbelianToIntModuleSheaf`. -/
theorem etaleAbelianToIntModuleSheaf_obj
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleAbelianToIntModuleSheaf F =
      (sheafCompose X.left.smallEtaleTopology addCommGrpToULiftIntModule).obj F :=
  sorry

/-- Pullback of global sections of `j_! F` along `globalEtalePullbackIso` of the
compactification structure map. -/
def etaleExtensionByZeroGlobalSectionsPullback
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} ULiftInt)).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) ⟶
      (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
            (ModuleCat.{u} ULiftInt)
            (Spec (CommRingCat.of k)).smallEtaleTopology
            P.obj.right.left.smallEtaleTopology).obj
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} ULiftInt)).obj F)).obj.obj
        (op (globalEtale (Spec (CommRingCat.of k)))) :=
  ((etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} ULiftInt)).obj F).obj.map
    (op (globalEtalePullbackIso P.obj.right.hom).hom)

/-- Unfolding of `etaleExtensionByZeroGlobalSectionsPullback`. -/
theorem etaleExtensionByZeroGlobalSectionsPullback_eq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) :
    etaleExtensionByZeroGlobalSectionsPullback P F =
      ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} ULiftInt)).obj F).obj.map
        (op (globalEtalePullbackIso P.obj.right.hom).hom) :=
  sorry

/-- The comparison morphism in `D(ULift ℤ)` from the single complex on
`Γ(X̄, j_! F)` to `RΓ_c(X, F[0])`. -/
def etaleDerivedCohomologyCompactSupportFromDerived
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} ULiftInt) (0 : ℤ)).obj
      (((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} ULiftInt)).obj F).obj.obj
        (op (globalEtale P.obj.right.left))) ⟶
      (etaleDerivedGammaCompactSupport P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
            (0 : ℤ)).obj F) :=
  let π := P.obj.right.hom
  let ext0 := etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} ULiftInt)
  let G := ext0.obj F
  let push :=
    (smallEtalePullback π).sheafPushforwardContinuous (ModuleCat.{u} ULiftInt)
      (Spec (CommRingCat.of k)).smallEtaleTopology
      P.obj.right.left.smallEtaleTopology
  let Γk :=
    (sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} ULiftInt)).obj
      (op (globalEtale (Spec (CommRingCat.of k))))
  (DerivedCategory.singleFunctor (ModuleCat.{u} ULiftInt) (0 : ℤ)).map
      (etaleExtensionByZeroGlobalSectionsPullback P F) ≫
    (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex Γk
              (ComplexShape.up ℤ) (0 : ℤ)).inv.app (push.obj G)) ≫
      (RightDerived.Cochain.unit Γk).app
        ((HomologicalComplex.single
            (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
              (ModuleCat.{u} ULiftInt))
            (ComplexShape.up ℤ) (0 : ℤ)).obj (push.obj G))) ≫
      (etaleDerivedGamma (Spec (CommRingCat.of k)) ULiftInt).map
          (DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex push
                    (ComplexShape.up ℤ) (0 : ℤ)).inv.app G) ≫
            (RightDerived.Cochain.unit push).app
              ((HomologicalComplex.single
                  (Sheaf P.obj.right.left.smallEtaleTopology
                    (ModuleCat.{u} ULiftInt))
                  (ComplexShape.up ℤ) (0 : ℤ)).obj G)) ≫
        (etaleDerivedGamma (Spec (CommRingCat.of k)) ULiftInt).map
          ((etaleDerivedPushforward π).map
            ((ext0.mapDerivedCategorySingleFunctor (0 : ℤ)).inv.app F))

/-- Unfolding of `etaleDerivedCohomologyCompactSupportFromDerived`. -/
theorem etaleDerivedCohomologyCompactSupportFromDerived_comp
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) :
    etaleDerivedCohomologyCompactSupportFromDerived P F =
      etaleDerivedCohomologyCompactSupportFromDerived P F :=
  sorry

/-- The `ModuleCat` comparison `Γ(X̄, j_! F) ⟶ H^0_c(X, F[0])`. -/
def etaleDerivedCohomologyCompactSupportFromGlobal
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} ULiftInt)).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) ⟶
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
            (0 : ℤ)).obj F) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} ULiftInt) (0 : ℤ)).inv.app
      (((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} ULiftInt)).obj F).obj.obj
        (op (globalEtale P.obj.right.left))) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} ULiftInt) (0 : ℤ)).map
      (etaleDerivedCohomologyCompactSupportFromDerived P F)

/-- `etaleDerivedCohomologyCompactSupportFromGlobal` is degree-zero homology of
the derived comparison after the single-functor identification of sections. -/
theorem etaleDerivedCohomologyCompactSupportFromGlobal_comp
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) :
    etaleDerivedCohomologyCompactSupportFromGlobal P F =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{u} ULiftInt) (0 : ℤ)).inv.app
          (((etaleExtensionByZero (Compactification.Of.ι P)
                (ModuleCat.{u} ULiftInt)).obj F).obj.obj
            (op (globalEtale P.obj.right.left))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} ULiftInt) (0 : ℤ)).map
          (etaleDerivedCohomologyCompactSupportFromDerived P F) :=
  sorry

/-- Additive form of `etaleDerivedCohomologyCompactSupportFromGlobal`. -/
def etaleDerivedCohomologyCompactSupportZeroAddHom
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} ULiftInt)).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) →+
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
            (0 : ℤ)).obj F) :=
  (etaleDerivedCohomologyCompactSupportFromGlobal P F).hom.toAddMonoidHom

/-- Unfolding of `etaleDerivedCohomologyCompactSupportZeroAddHom`. -/
theorem etaleDerivedCohomologyCompactSupportZeroAddHom_eq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) :
    etaleDerivedCohomologyCompactSupportZeroAddHom P F =
      (etaleDerivedCohomologyCompactSupportFromGlobal P F).hom.toAddMonoidHom :=
  sorry

/-- The additive comparison `Γ(X̄, j_! F) →+ H^0_c(X, F[0])` is bijective. -/
theorem etaleDerivedCohomologyCompactSupportZero_bijective
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
    (hF :
      IsLocallyTorsion
        ((sheafCompose X.left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} ULiftInt) AddCommGrpCat.{u})).obj F)) :
    Function.Bijective (etaleDerivedCohomologyCompactSupportZeroAddHom P F) :=
  sorry

/-- Additive equivalence `Γ(X̄, j_! F) ≃+ derived H^0_c(X, F[0])`. -/
def etaleDerivedCohomologyCompactSupportZeroEquiv
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
    (hF :
      IsLocallyTorsion
        ((sheafCompose X.left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} ULiftInt) AddCommGrpCat.{u})).obj F)) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} ULiftInt)).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) ≃+
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
            (0 : ℤ)).obj F) :=
  AddEquiv.ofBijective (etaleDerivedCohomologyCompactSupportZeroAddHom P F)
    (etaleDerivedCohomologyCompactSupportZero_bijective P F hF)

/-- The underlying map of `etaleDerivedCohomologyCompactSupportZeroEquiv`. -/
theorem etaleDerivedCohomologyCompactSupportZeroEquiv_apply
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
    (hF :
      IsLocallyTorsion
        ((sheafCompose X.left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} ULiftInt) AddCommGrpCat.{u})).obj F))
    (σ :
      ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} ULiftInt)).obj F).obj.obj
        (op (globalEtale P.obj.right.left))) :
    etaleDerivedCohomologyCompactSupportZeroEquiv P F hF σ =
      etaleDerivedCohomologyCompactSupportZeroAddHom P F σ :=
  sorry

/-- Objectwise `ULift ℤ`-module structure on global sections of an abelian
extension by zero. -/
def etaleExtensionByZeroGlobalSectionsULiftInt
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ModuleCat.{u} ULiftInt :=
  ModuleCat.of ULiftInt
    (((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
      (op (globalEtale P.obj.right.left)))

/-- The carrier of `etaleExtensionByZeroGlobalSectionsULiftInt` is the abelian
global-section group. -/
theorem etaleExtensionByZeroGlobalSectionsULiftInt_carrier
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleExtensionByZeroGlobalSectionsULiftInt P F =
      ModuleCat.of ULiftInt
        (((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
          (op (globalEtale P.obj.right.left))) :=
  sorry

/-- Canonical additive identification of abelian global sections of `j_! F`
with the carrier of `etaleExtensionByZeroGlobalSectionsULiftInt`. -/
def etaleExtensionByZeroGlobalSectionsULiftIntAddEquiv
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) ≃+
      etaleExtensionByZeroGlobalSectionsULiftInt P F :=
  AddEquiv.refl _

/-- The identity identification of abelian and `ULift ℤ`-module global
sections. -/
theorem etaleExtensionByZeroGlobalSectionsULiftIntAddEquiv_apply
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ :
      ((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
        (op (globalEtale P.obj.right.left))) :
    etaleExtensionByZeroGlobalSectionsULiftIntAddEquiv P F σ = σ :=
  sorry

/-- The composite additive comparison from underived `H^0_c(X, F)` to the
`ULift ℤ`-module of global sections of `j_! F`. -/
def globalSectionsCompactSupportToExtensionByZero
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportSubgroup X F →+
      etaleExtensionByZeroGlobalSectionsULiftInt P F :=
  (etaleExtensionByZeroGlobalSectionsULiftIntAddEquiv P F).toAddMonoidHom.comp
    (globalSectionsCompactSupportCompactifyGlobalEquiv P.obj.hom F).toAddMonoidHom

/-- Unfolding of `globalSectionsCompactSupportToExtensionByZero`. -/
theorem globalSectionsCompactSupportToExtensionByZero_comp
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportToExtensionByZero P F =
      (etaleExtensionByZeroGlobalSectionsULiftIntAddEquiv P F).toAddMonoidHom.comp
        (globalSectionsCompactSupportCompactifyGlobalEquiv P.obj.hom F).toAddMonoidHom :=
  sorry

/-- Restriction along the interior immersion commutes with conversion from
abelian coefficients to `ULift ℤ`-modules. -/
def etaleRestrictionSheafComposeConverter :
    TwoSquare
      (etaleRestrictionSheaf (Compactification.Of.ι P) AddCommGrpCat.{u})
      (sheafCompose P.obj.right.left.smallEtaleTopology addCommGrpToULiftIntModule)
      (sheafCompose X.left.smallEtaleTopology addCommGrpToULiftIntModule)
      (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} ULiftInt)) :=
  (𝟙
    (etaleRestrictionSheaf (Compactification.Of.ι P) AddCommGrpCat.{u} ⋙
      sheafCompose X.left.smallEtaleTopology addCommGrpToULiftIntModule))

/-- The mate of `etaleRestrictionSheafComposeConverter`, comparing
`j_!` after coefficient conversion with coefficient conversion after `j_!`. -/
def etaleExtensionByZeroConverter :
    TwoSquare
      (sheafCompose X.left.smallEtaleTopology addCommGrpToULiftIntModule)
      (abelianExtensionByZero (Compactification.Of.ι P))
      (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} ULiftInt))
      (sheafCompose P.obj.right.left.smallEtaleTopology addCommGrpToULiftIntModule) :=
  (mateEquiv
      (abelianExtensionByZero_adjunction (Compactification.Of.ι P))
      (etaleExtensionByZero_adjunction (Compactification.Of.ι P)
        (ModuleCat.{u} ULiftInt))).symm
    (etaleRestrictionSheafComposeConverter P)

/-- Global sections of the mate comparing `j_! F_ℤ` with the coefficient
conversion of `j_! F`. -/
def etaleExtensionByZeroConverterSections
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} ULiftInt)).obj
        (etaleAbelianToIntModuleSheaf F)).obj.obj
        (op (globalEtale P.obj.right.left)) →+
      ((sheafCompose P.obj.right.left.smallEtaleTopology
            addCommGrpToULiftIntModule).obj
        ((abelianExtensionByZero (Compactification.Of.ι P)).obj F)).obj.obj
        (op (globalEtale P.obj.right.left)) :=
  (((etaleExtensionByZeroConverter P).app F).hom.app
      (op (globalEtale P.obj.right.left))).hom.toAddMonoidHom

/-- Unfolding of `etaleExtensionByZeroConverterSections`. -/
theorem etaleExtensionByZeroConverterSections_eq
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleExtensionByZeroConverterSections P F =
      (((etaleExtensionByZeroConverter P).app F).hom.app
          (op (globalEtale P.obj.right.left))).hom.toAddMonoidHom :=
  sorry

/-- The mate comparison on global sections is bijective. -/
theorem etaleExtensionByZeroConverterSections_bijective
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective (etaleExtensionByZeroConverterSections P F) :=
  sorry

/-- Additive equivalence between global sections of `j_! F_ℤ` and of the
coefficient conversion of `j_! F`. -/
def etaleExtensionByZeroConverterSectionsEquiv
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} ULiftInt)).obj
        (etaleAbelianToIntModuleSheaf F)).obj.obj
        (op (globalEtale P.obj.right.left)) ≃+
      ((sheafCompose P.obj.right.left.smallEtaleTopology
            addCommGrpToULiftIntModule).obj
        ((abelianExtensionByZero (Compactification.Of.ι P)).obj F)).obj.obj
        (op (globalEtale P.obj.right.left)) :=
  AddEquiv.ofBijective (etaleExtensionByZeroConverterSections P F)
    (etaleExtensionByZeroConverterSections_bijective P F)

/-- Coefficient conversion on the abelian global-section group of `j_! F`. -/
def etaleExtensionByZeroAbelianToConvertedSections
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) →+
      ((sheafCompose P.obj.right.left.smallEtaleTopology
            addCommGrpToULiftIntModule).obj
        ((abelianExtensionByZero (Compactification.Of.ι P)).obj F)).obj.obj
        (op (globalEtale P.obj.right.left)) :=
  addCommGrpToULiftIntModuleAddHom
    (((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
      (op (globalEtale P.obj.right.left)))

/-- Unfolding of `etaleExtensionByZeroAbelianToConvertedSections`. -/
theorem etaleExtensionByZeroAbelianToConvertedSections_eq
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleExtensionByZeroAbelianToConvertedSections P F =
      addCommGrpToULiftIntModuleAddHom
        (((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
          (op (globalEtale P.obj.right.left))) :=
  sorry

/-- Additive conversion from abelian global sections of `j_! F` to global
sections of `j_!` of the associated `ULift ℤ`-module sheaf. -/
def etaleExtensionByZeroAbelianToModuleSections
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) →+
      ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} ULiftInt)).obj
          (etaleAbelianToIntModuleSheaf F)).obj.obj
        (op (globalEtale P.obj.right.left)) :=
  (etaleExtensionByZeroConverterSectionsEquiv P F).symm.toAddMonoidHom.comp
    (etaleExtensionByZeroAbelianToConvertedSections P F)

/-- The conversion of global sections is coefficient conversion followed by
the inverse of the mate comparison. -/
theorem etaleExtensionByZeroAbelianToModuleSections_comp
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleExtensionByZeroAbelianToModuleSections P F =
      (etaleExtensionByZeroConverterSectionsEquiv P F).symm.toAddMonoidHom.comp
        (etaleExtensionByZeroAbelianToConvertedSections P F) :=
  sorry

/-- The composite additive comparison from underived `H^0_c(X, F)` to derived
`H^0_c(X, F_ℤ[0])`. -/
def globalSectionsCompactSupportDerivedHom
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    globalSectionsCompactSupportSubgroup X F →+
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
            (0 : ℤ)).obj (etaleAbelianToIntModuleSheaf F)) :=
  have := hF
  (etaleDerivedCohomologyCompactSupportZeroAddHom P
        (etaleAbelianToIntModuleSheaf F)).comp
    ((etaleExtensionByZeroAbelianToModuleSections P F).comp
      (globalSectionsCompactSupportCompactifyGlobalEquiv P.obj.hom F).toAddMonoidHom)

/-- `globalSectionsCompactSupportDerivedHom` is Lemma 63.3.10 followed by
coefficient conversion and the derived comparison from global sections of
`j_! F`. -/
theorem globalSectionsCompactSupportDerivedHom_comp
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    globalSectionsCompactSupportDerivedHom P F hF =
      (etaleDerivedCohomologyCompactSupportZeroAddHom P
            (etaleAbelianToIntModuleSheaf F)).comp
        ((etaleExtensionByZeroAbelianToModuleSections P F).comp
          (globalSectionsCompactSupportCompactifyGlobalEquiv P.obj.hom F).toAddMonoidHom) :=
  sorry

/-- The composite comparison `H^0_c(X, F) →+ derived H^0_c` is bijective. -/
theorem globalSectionsCompactSupportDerivedHom_bijective
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    Function.Bijective (globalSectionsCompactSupportDerivedHom P F hF) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
