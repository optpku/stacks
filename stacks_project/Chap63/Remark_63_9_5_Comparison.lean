module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZeroComparison
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_7_3_ExtensionByZero
public import stacks_project.Chap63.Lemma_63_9_1_Comparison
public import stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_9_4_Cartesian

/-!
# Derived étale comparison `Rf_! ⟶ Rf_*`

Canonical natural transformation of compactification models obtained by
promoting the sheaf-level map `j_! ⟶ j_*` of Lemma 59.70.6 to
`j_! ⟶ Rj_*` and whiskering with `R f̄_*`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

section InteriorComparison

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Of Y X)
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
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
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
variable [((smallEtalePullback (Of.ι P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
    X.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Of.ι P)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
      X.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (Of.ι P) Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward (Of.ι P) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (Of.ι P ≫ P.obj.right.hom) Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (Of.ι P ≫ P.obj.right.hom) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback X.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    X.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback X.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      X.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback (Of.ι P ≫ P.obj.right.hom)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    X.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Of.ι P ≫ P.obj.right.hom)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      X.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward X.hom Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward X.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (Of.ι P) Λ ⋙
    etaleModulePushforward P.obj.right.hom Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (Of.ι P) Λ ⋙
      etaleModulePushforward P.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

/-- Derived interior comparison `j_! ⟶ Rj_*` obtained by descending the
sheaf-level map `moduleExtensionByZeroToDirectImage` along the exact
presentation of `j_!` and the cochain unit of `Rj_*`. -/
def interiorToPushforward :
    (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory ⟶
      etaleDerivedPushforward (Of.ι P) :=
  ((etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory).rightDerivedDesc
    ((etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.inv)
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (etaleDerivedPushforward (Of.ι P))
    (whiskerRight
        (NatTrans.mapHomologicalComplex
          (moduleExtensionByZeroToDirectImage (Λ := Λ) (Of.ι P))
          (ComplexShape.up ℤ))
        (DerivedCategory.Q :
          CochainComplex
            (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            EtaleDerived P.obj.right.left Λ) ≫
      RightDerived.Cochain.unit
        ((smallEtalePullback (Of.ι P)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
          X.left.smallEtaleTopology))

/-- Component of `interiorToPushforward` at an object of `D(X_étale, Λ)`. -/
def interiorToPushforward_app (K : EtaleDerived X.left Λ) :
    ((etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory).obj K ⟶
      (etaleDerivedPushforward (Of.ι P)).obj K :=
  (interiorToPushforward X P).app K

/-- The objectwise interior comparison is the component of
`interiorToPushforward`. -/
theorem interiorToPushforward_app_eq (K : EtaleDerived X.left Λ) :
    interiorToPushforward_app X P K = (interiorToPushforward X P).app K :=
  sorry

/-- Unfolding of `interiorToPushforward` as the cochain-level descent of
`moduleExtensionByZeroToDirectImage`. -/
theorem interiorToPushforward_eq :
    interiorToPushforward X P =
      ((etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory).rightDerivedDesc
        ((etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.inv)
        (HomologicalComplex.quasiIso
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
        (etaleDerivedPushforward (Of.ι P))
        (whiskerRight
            (NatTrans.mapHomologicalComplex
              (moduleExtensionByZeroToDirectImage (Λ := Λ) (Of.ι P))
          (ComplexShape.up ℤ))
            (DerivedCategory.Q :
              CochainComplex
                (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
                EtaleDerived P.obj.right.left Λ) ≫
          RightDerived.Cochain.unit
        ((smallEtalePullback (Of.ι P)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
          X.left.smallEtaleTopology)) :=
  sorry

/-- Transport of `R(j ≫ f̄)_*` to `Rf_*` along the compactification triangle
`j ≫ f̄ = X.hom`. -/
def toPushforward_congr :
    (etaleDerivedPushforward (Of.ι P ≫ P.obj.right.hom) :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ≅
      (etaleDerivedPushforward X.hom :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        EtaleDerived X.left Λ)
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (RightDerived.Cochain.unit
      (etaleModulePushforward (Of.ι P ≫ P.obj.right.hom) Λ))
    (RightDerived.Cochain.unit (etaleModulePushforward X.hom Λ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModulePushforwardCongr (Λ := Λ) (Over.w P.obj.hom))
        (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y Λ))

/-- Canonical comparison `Rf_! ⟶ Rf_*` of compactification models, obtained by
whiskering `interiorToPushforward` with `R f̄_*` and inverting derived Leray. -/
@[irreducible]
def toPushforward :
    etaleDerivedLowerShriek X P ⟶
      (etaleDerivedPushforward X.hom :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) :=
  whiskerRight (interiorToPushforward X P)
      (etaleDerivedPushforward P.obj.right.hom :
        EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Y Λ) ≫
    (@asIso (EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) _
        (etaleDerivedPushforward (Of.ι P ≫ P.obj.right.hom) :
          EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)
        ((etaleDerivedPushforward (Of.ι P) :
            EtaleDerived X.left Λ ⥤ EtaleDerived P.obj.right.left Λ) ⋙
          (etaleDerivedPushforward P.obj.right.hom :
            EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Y Λ))
        (etaleDerivedPushforwardComp (Of.ι P) P.obj.right.hom Λ)
        (etaleDerivedPushforwardComp_isIso (Of.ι P) P.obj.right.hom Λ)).inv ≫
    (toPushforward_congr X P).hom

/-- Component of `toPushforward` at an object of `D(X_étale, Λ)`. -/
def toPushforward_app (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriek X P).obj K ⟶
      (etaleDerivedPushforward X.hom).obj K :=
  (toPushforward X P).app K

/-- The objectwise comparison is the component of `toPushforward`. -/
theorem toPushforward_app_eq (K : EtaleDerived X.left Λ) :
    toPushforward_app X P K = (toPushforward X P).app K :=
  sorry

/-- Unfolding of `toPushforward` as interior whiskering, inverted Leray, and
transport along `Over.w`. -/
theorem toPushforward_eq :
    toPushforward X P =
      whiskerRight (interiorToPushforward X P)
          (etaleDerivedPushforward P.obj.right.hom :
            EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Y Λ) ≫
        (@asIso (EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) _
            (etaleDerivedPushforward (Of.ι P ≫ P.obj.right.hom) :
              EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)
            ((etaleDerivedPushforward (Of.ι P) :
                EtaleDerived X.left Λ ⥤ EtaleDerived P.obj.right.left Λ) ⋙
              (etaleDerivedPushforward P.obj.right.hom :
                EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Y Λ))
            (etaleDerivedPushforwardComp (Of.ι P) P.obj.right.hom Λ)
            (etaleDerivedPushforwardComp_isIso (Of.ι P) P.obj.right.hom Λ)).inv ≫
        (toPushforward_congr X P).hom :=
  sorry

variable {Q : Of Y X} (φ : P ⟶ Q)
variable [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Q.obj.right.left.Etale,
  HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
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
variable [((smallEtalePullback (Of.ι Q)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Q.obj.right.left.smallEtaleTopology
    X.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Of.ι Q)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Q.obj.right.left.smallEtaleTopology
      X.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (Of.ι Q) Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward (Of.ι Q) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (Of.ι Q ≫ Q.obj.right.hom) Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (Of.ι Q ≫ Q.obj.right.hom) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback (Of.ι Q ≫ Q.obj.right.hom)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    X.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Of.ι Q ≫ Q.obj.right.hom)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      X.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (Of.ι Q) Λ ⋙
    etaleModulePushforward Q.obj.right.hom Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (Of.ι Q) Λ ⋙
      etaleModulePushforward Q.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

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
variable [((smallEtalePullback (Of.ambientMap φ)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Q.obj.right.left.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [(etaleModulePushforward (Of.ambientMap φ) Λ).Additive]
variable [(etaleModulePushforward Q.obj.right.hom Λ).Additive]
variable [(etaleModulePushforward P.obj.right.hom Λ).Additive]

/-- On objects of `D⁺_tors(X_étale, Λ)`, the comparison `Rf_! ⟶ Rf_*` is
independent of the compactification: along a morphism of compactifications
the two `toPushforward` maps agree after identifying the compactification
models of `Rf_!`. -/
theorem toPushforward_isoOfHom_of_isGE_isTorsion
    (K : EtaleDerived X.left Λ) (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    [DerivedCategory.IsGE K n] :
    isoOfHom_app X Λ φ K ≫ toPushforward_app X P K = toPushforward_app X Q K :=
  sorry

/-- If `Λ` is a torsion ring, the comparison `Rf_! ⟶ Rf_*` is independent of
the compactification as a natural transformation on `D(X_étale, Λ)`. -/
theorem toPushforward_isoOfHom_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) :
    isoOfHom X Λ φ ≫ toPushforward X P = toPushforward X Q :=
  sorry

end InteriorComparison

section CompCompat

-- Local instance justification (search instability): prefer the existing
-- strong-to-weak projection so composition goals do not repeatedly match
-- unrelated over-site sheafification families.
attribute [local instance 10000] HasSheafify.isRightAdjoint

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g)
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
  [PreservesFiniteLimits
    (etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
    (etaleExtensionByZero (CompDiagram.ιBase X g C) (ModuleCat.{u} Λ))]
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
  [((smallEtalePullback X.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback X.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [((smallEtalePullback g).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback g).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [((smallEtalePullback (X.hom ≫ g)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z.smallEtaleTopology X.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback (X.hom ≫ g)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology X.left.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [(etaleModulePushforward X.hom Λ).Additive]
  [(etaleModulePushforward g Λ).Additive]
  [(etaleModulePushforward (X.hom ≫ g) Λ).Additive]
  [(etaleModulePushforward X.hom Λ ⋙ etaleModulePushforward g Λ).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleModulePushforward X.hom Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
    (HomologicalComplex.quasiIso
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleModulePushforward (X.hom ≫ g) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward X.hom Λ ⋙ etaleModulePushforward g Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/-- Compactification model of `R(g ∘ f)_*`. -/
irreducible_def starCompCodomain :
    EtaleDerived X.left Λ ⥤ EtaleDerived Z Λ :=
  etaleDerivedPushforward (X.hom ≫ g)

variable [((smallEtalePullback (CompDiagram.ιInterior X g C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (CompDiagram.interior X g C).smallEtaleTopology
    X.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback (CompDiagram.ιInterior X g C)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) (CompDiagram.interior X g C).smallEtaleTopology
        X.left.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (CompDiagram.ιInterior X g C) Λ).Additive]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward (CompDiagram.ιInterior X g C) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [((smallEtalePullback (CompDiagram.ιBase X g C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
    Y.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback (CompDiagram.ιBase X g C)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
        Y.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (CompDiagram.ιBase X g C) Λ).Additive]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward (CompDiagram.ιBase X g C) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [((smallEtalePullback
      (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) C.P_bar.obj.right.left.smallEtaleTopology
    X.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback
          (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) C.P_bar.obj.right.left.smallEtaleTopology
        X.left.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [(etaleModulePushforward
    (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C) Λ).Additive]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward
        (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (CompDiagram.ιInterior X g C) Λ ⋙
    etaleModulePushforward (CompDiagram.toBase X g C) Λ).Additive]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward (CompDiagram.ιInterior X g C) Λ ⋙
        etaleModulePushforward (CompDiagram.toBase X g C) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (CompDiagram.ιBase X g C) Λ ⋙
    etaleModulePushforward C.P_g.obj.right.hom Λ).Additive]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward (CompDiagram.ιBase X g C) Λ ⋙
        etaleModulePushforward C.P_g.obj.right.hom Λ))
    (HomologicalComplex.quasiIso
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [(etaleModulePushforward
      (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C) Λ ⋙
    etaleModulePushforward (CompDiagram.toComposite X g C) Λ).Additive]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward
          (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C) Λ ⋙
        etaleModulePushforward (CompDiagram.toComposite X g C) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/-- Interior pushforward along `ofInterior.ι` transfers from `ιInterior`. -/
instance (priority := 10000) instAdditive_sheafPushforward_ofInterior_ι :
    ((smallEtalePullback (CompDiagram.ofInterior X g C).ι).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
      X.left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (CompDiagram.ιInterior X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (CompDiagram.interior X g C).smallEtaleTopology
      X.left.smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along `ofInterior.ι`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_ofInterior_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (CompDiagram.ofInterior X g C).ι).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
          X.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (CompDiagram.ιInterior X g C)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (CompDiagram.interior X g C).smallEtaleTopology
          X.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along `ofInterior.ι` transfers from `ιInterior`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_ofInterior_ι :
    (etaleModulePushforward (CompDiagram.ofInterior X g C).ι Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward (CompDiagram.ιInterior X g C) Λ).Additive)

/-- Right-derivability of module pushforward along `ofInterior.ι`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_ofInterior_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ofInterior X g C).ι Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ιInterior X g C) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Composite interior-plus-structure-map of `ofInterior` is `X.hom`. -/
instance (priority := 10000) instAdditive_sheafPushforward_ofInterior_ι_comp_hom :
    ((smallEtalePullback
        ((CompDiagram.ofInterior X g C).ι ≫
          (CompDiagram.ofInterior X g C).obj.right.hom)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology).Additive :=
  (congrArg
      (fun f ↦ (smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology)
      (Over.w (CompDiagram.ofInterior X g C).obj.hom).symm) ▸
    inferInstanceAs
      (((smallEtalePullback X.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology).Additive)

/-- Right-derivability of the composite interior-plus-structure-map of `ofInterior`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_ofInterior_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            ((CompDiagram.ofInterior X g C).ι ≫
              (CompDiagram.ofInterior X g C).obj.right.hom)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  (congrArg
      (fun f ↦ RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology))
      (Over.w (CompDiagram.ofInterior X g C).obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          ((smallEtalePullback X.hom).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology))
        (HomologicalComplex.quasiIso
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along the composite interior of `ofInterior`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_ofInterior_ι_comp_hom :
    (etaleModulePushforward
      ((CompDiagram.ofInterior X g C).ι ≫
        (CompDiagram.ofInterior X g C).obj.right.hom) Λ).Additive :=
  (congrArg (fun f ↦ etaleModulePushforward f Λ)
      (Over.w (CompDiagram.ofInterior X g C).obj.hom).symm) ▸
    inferInstanceAs ((etaleModulePushforward X.hom Λ).Additive)

/-- Right-derivability of module pushforward along the composite interior of
`ofInterior`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_ofInterior_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward
          ((CompDiagram.ofInterior X g C).ι ≫
            (CompDiagram.ofInterior X g C).obj.right.hom) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  (congrArg (fun f ↦ RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (Over.w (CompDiagram.ofInterior X g C).obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived (etaleModulePushforward X.hom Λ))
        (HomologicalComplex.quasiIso
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Iterated module pushforward of `ofInterior`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_ofInterior_comp :
    (etaleModulePushforward (CompDiagram.ofInterior X g C).ι Λ ⋙
      etaleModulePushforward (CompDiagram.ofInterior X g C).obj.right.hom Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward (CompDiagram.ιInterior X g C) Λ ⋙
      etaleModulePushforward (CompDiagram.toBase X g C) Λ).Additive)

/-- Right-derivability of iterated module pushforward of `ofInterior`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_ofInterior_comp :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ofInterior X g C).ι Λ ⋙
          etaleModulePushforward (CompDiagram.ofInterior X g C).obj.right.hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ιInterior X g C) Λ ⋙
          etaleModulePushforward (CompDiagram.toBase X g C) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Pushforward along the structure map of `ofInterior` transfers from `toBase`. -/
instance (priority := 10000) instAdditive_sheafPushforward_ofInterior_obj_right_hom :
    ((smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (CompDiagram.toBase X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (CompDiagram.interior X g C).smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along the structure map of `ofInterior`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_ofInterior_obj_right_hom :
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

/-- Module pushforward along the structure map of `ofInterior`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_ofInterior_obj_right_hom :
    (etaleModulePushforward (CompDiagram.ofInterior X g C).obj.right.hom Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward (CompDiagram.toBase X g C) Λ).Additive)

/-- Right-derivability of module pushforward along the structure map of
`ofInterior`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_ofInterior_obj_right_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ofInterior X g C).obj.right.hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
          (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.toBase X g C) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Pushforward along `g` transfers to `Over.mk g`. -/
instance (priority := 10000) instAdditive_sheafPushforward_overMk_g_hom :
    ((smallEtalePullback (Over.mk g).hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      (Over.mk g).left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback g).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along `Over.mk g`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_overMk_g_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (Over.mk g).hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology
          (Over.mk g).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback g).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along `Over.mk g`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_overMk_g_hom :
    (etaleModulePushforward (Over.mk g).hom Λ).Additive :=
  inferInstanceAs ((etaleModulePushforward g Λ).Additive)

/-- Right-derivability of module pushforward along `Over.mk g`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_overMk_g_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (Over.mk g).hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Interior pushforward along `P_g.ι` transfers from `ιBase`. -/
instance (priority := 10000) instAdditive_sheafPushforward_P_g_ι :
    ((smallEtalePullback C.P_g.ι).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
      (Over.mk g).left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (CompDiagram.ιBase X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
      Y.smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along `P_g.ι`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_P_g_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback C.P_g.ι).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
          (Over.mk g).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (CompDiagram.ιBase X g C)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
          Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along `P_g.ι`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_P_g_ι :
    (etaleModulePushforward C.P_g.ι Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward (CompDiagram.ιBase X g C) Λ).Additive)

/-- Right-derivability of module pushforward along `P_g.ι`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_P_g_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward C.P_g.ι Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ιBase X g C) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Composite interior of `P_g` is `g`. -/
instance (priority := 10000) instAdditive_sheafPushforward_P_g_ι_comp_hom :
    ((smallEtalePullback (C.P_g.ι ≫ C.P_g.obj.right.hom)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      (Over.mk g).left.smallEtaleTopology).Additive :=
  (congrArg
      (fun f ↦ (smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology
        (Over.mk g).left.smallEtaleTopology)
      (Over.w C.P_g.obj.hom).symm) ▸
    inferInstanceAs
      (((smallEtalePullback g).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive)

/-- Right-derivability of the composite interior of `P_g`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_P_g_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (C.P_g.ι ≫ C.P_g.obj.right.hom)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology
          (Over.mk g).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  (congrArg
      (fun f ↦ RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology
          (Over.mk g).left.smallEtaleTopology))
      (Over.w C.P_g.obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          ((smallEtalePullback g).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
        (HomologicalComplex.quasiIso
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along the composite interior of `P_g`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_P_g_ι_comp_hom :
    (etaleModulePushforward (C.P_g.ι ≫ C.P_g.obj.right.hom) Λ).Additive :=
  (congrArg (fun f ↦ etaleModulePushforward f Λ)
      (Over.w C.P_g.obj.hom).symm) ▸
    inferInstanceAs ((etaleModulePushforward g Λ).Additive)

/-- Right-derivability of module pushforward along the composite interior of `P_g`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_P_g_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (C.P_g.ι ≫ C.P_g.obj.right.hom) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  (congrArg (fun f ↦ RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (Over.w C.P_g.obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
        (HomologicalComplex.quasiIso
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Iterated module pushforward of `P_g`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_P_g_comp :
    (etaleModulePushforward C.P_g.ι Λ ⋙
      etaleModulePushforward C.P_g.obj.right.hom Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward (CompDiagram.ιBase X g C) Λ ⋙
      etaleModulePushforward C.P_g.obj.right.hom Λ).Additive)

/-- Right-derivability of iterated module pushforward of `P_g`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_P_g_comp :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward C.P_g.ι Λ ⋙
          etaleModulePushforward C.P_g.obj.right.hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ιBase X g C) Λ ⋙
          etaleModulePushforward C.P_g.obj.right.hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Pushforward along `g ∘ f` transfers to `Over.mk (X.hom ≫ g)`. -/
instance (priority := 10000) instAdditive_sheafPushforward_overMk_comp_hom :
    ((smallEtalePullback (Over.mk (X.hom ≫ g)).hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      (Over.mk (X.hom ≫ g)).left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (X.hom ≫ g)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology X.left.smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along `Over.mk (X.hom ≫ g)`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_overMk_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (Over.mk (X.hom ≫ g)).hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology
          (Over.mk (X.hom ≫ g)).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (X.hom ≫ g)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology X.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along `Over.mk (X.hom ≫ g)`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_overMk_comp_hom :
    (etaleModulePushforward (Over.mk (X.hom ≫ g)).hom Λ).Additive :=
  inferInstanceAs ((etaleModulePushforward (X.hom ≫ g) Λ).Additive)

/-- Right-derivability of module pushforward along `Over.mk (X.hom ≫ g)`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_overMk_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (Over.mk (X.hom ≫ g)).hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (X.hom ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Interior pushforward along `ofComposite.ι`. -/
instance (priority := 10000) instAdditive_sheafPushforward_ofComposite_ι :
    ((smallEtalePullback (CompDiagram.ofComposite X g C).ι).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
      (Over.mk (X.hom ≫ g)).left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback
        (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) C.P_bar.obj.right.left.smallEtaleTopology
      X.left.smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along `ofComposite.ι`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_ofComposite_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (CompDiagram.ofComposite X g C).ι).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
          (Over.mk (X.hom ≫ g)).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) C.P_bar.obj.right.left.smallEtaleTopology
          X.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along `ofComposite.ι`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_ofComposite_ι :
    (etaleModulePushforward (CompDiagram.ofComposite X g C).ι Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward
      (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C) Λ).Additive)

/-- Right-derivability of module pushforward along `ofComposite.ι`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_ofComposite_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ofComposite X g C).ι Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward
          (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Composite interior of `ofComposite` is `X.hom ≫ g`. -/
instance (priority := 10000) instAdditive_sheafPushforward_ofComposite_ι_comp_hom :
    ((smallEtalePullback
        ((CompDiagram.ofComposite X g C).ι ≫
          (CompDiagram.ofComposite X g C).obj.right.hom)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      (Over.mk (X.hom ≫ g)).left.smallEtaleTopology).Additive :=
  (congrArg
      (fun f ↦ (smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology
        (Over.mk (X.hom ≫ g)).left.smallEtaleTopology)
      (Over.w (CompDiagram.ofComposite X g C).obj.hom).symm) ▸
    inferInstanceAs
      (((smallEtalePullback (X.hom ≫ g)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology X.left.smallEtaleTopology).Additive)

/-- Right-derivability of the composite interior of `ofComposite`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_ofComposite_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            ((CompDiagram.ofComposite X g C).ι ≫
              (CompDiagram.ofComposite X g C).obj.right.hom)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology
          (Over.mk (X.hom ≫ g)).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  (congrArg
      (fun f ↦ RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology
          (Over.mk (X.hom ≫ g)).left.smallEtaleTopology))
      (Over.w (CompDiagram.ofComposite X g C).obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          ((smallEtalePullback (X.hom ≫ g)).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) Z.smallEtaleTopology X.left.smallEtaleTopology))
        (HomologicalComplex.quasiIso
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along the composite interior of `ofComposite`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_ofComposite_ι_comp_hom :
    (etaleModulePushforward
      ((CompDiagram.ofComposite X g C).ι ≫
        (CompDiagram.ofComposite X g C).obj.right.hom) Λ).Additive :=
  (congrArg (fun f ↦ etaleModulePushforward f Λ)
      (Over.w (CompDiagram.ofComposite X g C).obj.hom).symm) ▸
    inferInstanceAs ((etaleModulePushforward (X.hom ≫ g) Λ).Additive)

/-- Right-derivability of module pushforward along the composite interior of
`ofComposite`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_ofComposite_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward
          ((CompDiagram.ofComposite X g C).ι ≫
            (CompDiagram.ofComposite X g C).obj.right.hom) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  (congrArg (fun f ↦ RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (Over.w (CompDiagram.ofComposite X g C).obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived (etaleModulePushforward (X.hom ≫ g) Λ))
        (HomologicalComplex.quasiIso
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Iterated module pushforward of `ofComposite`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_ofComposite_comp :
    (etaleModulePushforward (CompDiagram.ofComposite X g C).ι Λ ⋙
      etaleModulePushforward (CompDiagram.ofComposite X g C).obj.right.hom Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward
        (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C) Λ ⋙
      etaleModulePushforward (CompDiagram.toComposite X g C) Λ).Additive)

/-- Right-derivability of iterated module pushforward of `ofComposite`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_ofComposite_comp :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ofComposite X g C).ι Λ ⋙
          etaleModulePushforward (CompDiagram.ofComposite X g C).obj.right.hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward
            (CompDiagram.ιInterior X g C ≫ CompDiagram.openImmersion X g C) Λ ⋙
          etaleModulePushforward (CompDiagram.toComposite X g C) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Pushforward along the structure map of `ofComposite` transfers from
`toComposite`. -/
instance (priority := 10000) instAdditive_sheafPushforward_ofComposite_obj_right_hom :
    ((smallEtalePullback (CompDiagram.ofComposite X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (CompDiagram.toComposite X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along the structure map of `ofComposite`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_ofComposite_obj_right_hom :
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

/-- Module pushforward along the structure map of `ofComposite`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_ofComposite_obj_right_hom :
    (etaleModulePushforward (CompDiagram.ofComposite X g C).obj.right.hom Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward (CompDiagram.toComposite X g C) Λ).Additive)

/-- Right-derivability of module pushforward along the structure map of
`ofComposite`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_ofComposite_obj_right_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.ofComposite X g C).obj.right.hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
          (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (CompDiagram.toComposite X g C) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Whiskered `toPushforward` from `Rf_! ⋙ Rg_!` to `Rf_* ⋙ Rg_*`. -/
irreducible_def toPushforward_compDomain :
    compDomain X g C Λ ⟶
      ((etaleDerivedPushforward X.hom :
          EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⋙
        (etaleDerivedPushforward g :
          EtaleDerived Y Λ ⥤ EtaleDerived Z Λ)) :=
  eqToHom (compDomain_def X g C Λ) ≫
    whiskerRight (toPushforward X (CompDiagram.ofInterior X g C))
      (etaleDerivedLowerShriek (Over.mk g) C.P_g) ≫
    whiskerLeft (etaleDerivedPushforward X.hom)
      (toPushforward (Over.mk g) C.P_g)

/-- `toPushforward` from `R(g ∘ f)_!` to `R(g ∘ f)_*`. -/
irreducible_def toPushforward_compCodomain :
    compCodomain X g C Λ ⟶ starCompCodomain X g Λ :=
  eqToHom (compCodomain_def X g C Λ) ≫
    toPushforward (Over.mk (X.hom ≫ g)) (CompDiagram.ofComposite X g C) ≫
    eqToHom (starCompCodomain_def X g Λ).symm

/-- Compatibility of `toPushforward` with `Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!` and
`Rg_* ∘ Rf_* ⟶ R(g ∘ f)_*`. -/
theorem toPushforward_comp_compat :
    toPushforward_compDomain X g C Λ ≫
        (@asIso (EtaleDerived X.left Λ ⥤ EtaleDerived Z Λ) _
            (etaleDerivedPushforward (X.hom ≫ g) :
              EtaleDerived X.left Λ ⥤ EtaleDerived Z Λ)
            ((etaleDerivedPushforward X.hom :
                EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⋙
              (etaleDerivedPushforward g :
                EtaleDerived Y Λ ⥤ EtaleDerived Z Λ))
            (etaleDerivedPushforwardComp X.hom g Λ)
            (etaleDerivedPushforwardComp_isIso X.hom g Λ)).inv ≫
        eqToHom (starCompCodomain_def X g Λ).symm =
      comp X g C Λ ≫ toPushforward_compCodomain X g C Λ :=
  sorry

end CompCompat

section BaseChangeCompat

-- Local instance justification (search instability): prefer the existing
-- strong-to-weak projection so base-change goals do not repeatedly match
-- unrelated over-site sheafification families.
attribute [local instance 10000] HasSheafify.isRightAdjoint

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h_cart : IsPullback g' f' f g)
  [IsSeparated f] [Scheme.Hom.FiniteType f]
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  (P : Of Y (Over.mk f))
  (Λ : Type u) [CommRing Λ]
  [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.Etale,
    HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
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
  [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : P.obj.right.left.Etale,
    HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
    (ModuleCat.{u} Λ)]
  [∀ U : (ambient f g f' g' h_cart P).Etale,
    HasWeakSheafify ((ambient f g f' g' h_cart P).smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
  [HasDerivedCategory
    (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback f).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback f').op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (ambientToBase f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
    (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
    (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ))]
  [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology
        P.obj.right.left.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))]
  [((smallEtalePullback f).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [((smallEtalePullback f').sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology X'.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback f').sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y'.smallEtaleTopology X'.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
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
  [((smallEtalePullback (Of.ι P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
    (Over.mk f).left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback (Of.ι P)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
        (Over.mk f).left.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))]
  [(etaleModulePushforward (Of.ι P) Λ).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleModulePushforward (Of.ι P) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))]
  [(etaleModulePushforward (Of.ι P ≫ P.obj.right.hom) Λ).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward (Of.ι P ≫ P.obj.right.hom) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))]
  [((smallEtalePullback (Of.ι P ≫ P.obj.right.hom)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology (Over.mk f).left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback (Of.ι P ≫ P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology (Over.mk f).left.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))]
  [(etaleModulePushforward (Of.ι P) Λ ⋙
    etaleModulePushforward P.obj.right.hom Λ).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward (Of.ι P) Λ ⋙
        etaleModulePushforward P.obj.right.hom Λ))
    (HomologicalComplex.quasiIso
      (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))]
  [((smallEtalePullback (interiorLift f g f' g' h_cart P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (ambient f g f' g' h_cart P).smallEtaleTopology
    X'.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback (interiorLift f g f' g' h_cart P)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) (ambient f g f' g' h_cart P).smallEtaleTopology
        X'.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [(etaleModulePushforward (interiorLift f g f' g' h_cart P) Λ).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward (interiorLift f g f' g' h_cart P) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [(etaleModulePushforward
      (interiorLift f g f' g' h_cart P ≫
        ambientToBase f g f' g' h_cart P) Λ).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward
        (interiorLift f g f' g' h_cart P ≫
          ambientToBase f g f' g' h_cart P) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [((smallEtalePullback
      (interiorLift f g f' g' h_cart P ≫
        ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology X'.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback
          (interiorLift f g f' g' h_cart P ≫
            ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y'.smallEtaleTopology X'.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [(etaleModulePushforward (interiorLift f g f' g' h_cart P) Λ ⋙
    etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePushforward (interiorLift f g f' g' h_cart P) Λ ⋙
        etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
    AddCommGrpCat.{u}]
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
    AddCommGrpCat.{u}]
  [HasSheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose X'.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y'.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose P.obj.right.left.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (ambient f g f' g' h_cart P).smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X'.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y'.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [P.obj.right.left.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient f g f' g' h_cart P).smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
      (ambientToBase f g f' g' h_cart P ≫ g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
      (ambientToSource f g f' g' h_cart P ≫
        P.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (ambient f g f' g' h_cart P).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
      (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
      (interiorLift f g f' g' h_cart P ≫
        ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (g' ≫ Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (smallEtalePullback
      (ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (smallEtalePullback g).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (smallEtalePullback g').op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (interiorLift f g f' g' h_cart P)).op]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [((smallEtalePullback
      (ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology
    (ambient f g f' g' h_cart P).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback
          (ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y'.smallEtaleTopology
        (ambient f g f' g' h_cart P).smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))]
  [(etaleModulePushforward P.obj.right.hom Λ ⋙
    etaleModuleSheafPullback g Λ).Additive]
  [(etaleModuleSheafPullback (ambientToSource f g f' g' h_cart P) Λ ⋙
    etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward P.obj.right.hom Λ).Additive]

/-- Pushforward along `Over.mk f` transfers from `f`. -/
instance (priority := 10000) instAdditive_sheafPushforward_overMk_f_hom :
    ((smallEtalePullback (Over.mk f).hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (Over.mk f).left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along `Over.mk f`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_overMk_f_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (Over.mk f).hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          (Over.mk f).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along `Over.mk f`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_overMk_f_hom :
    (etaleModulePushforward (Over.mk f).hom Λ).Additive :=
  inferInstanceAs ((etaleModulePushforward f Λ).Additive)

/-- Right-derivability of module pushforward along `Over.mk f`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_overMk_f_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (Over.mk f).hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Interior pushforward along `P.ι` transfers from `Of.ι P`. -/
instance (priority := 10000) instAdditive_sheafPushforward_P_ι :
    ((smallEtalePullback P.ι).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
      (Over.mk f).left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (Of.ι P)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
      (Over.mk f).left.smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along `P.ι`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_P_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback P.ι).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
          (Over.mk f).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (Of.ι P)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) P.obj.right.left.smallEtaleTopology
          (Over.mk f).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Module pushforward along `P.ι`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_P_ι :
    (etaleModulePushforward P.ι Λ).Additive :=
  inferInstanceAs ((etaleModulePushforward (Of.ι P) Λ).Additive)

/-- Right-derivability of module pushforward along `P.ι`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_P_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward P.ι Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (Of.ι P) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Composite interior of `P` is `f`. -/
instance (priority := 10000) instAdditive_sheafPushforward_P_ι_comp_hom :
    ((smallEtalePullback (P.ι ≫ P.obj.right.hom)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (Over.mk f).left.smallEtaleTopology).Additive :=
  (congrArg
      (fun h ↦ (smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology
        (Over.mk f).left.smallEtaleTopology)
      (Over.w P.obj.hom).symm) ▸
    inferInstanceAs
      (((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive)

/-- Right-derivability of the composite interior of `P`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_P_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (P.ι ≫ P.obj.right.hom)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          (Over.mk f).left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  (congrArg
      (fun h ↦ RightDerived.Cochain.toDerived
        ((smallEtalePullback h).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          (Over.mk f).left.smallEtaleTopology))
      (Over.w P.obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          ((smallEtalePullback f).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
        (HomologicalComplex.quasiIso
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along the composite interior of `P`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_P_ι_comp_hom :
    (etaleModulePushforward (P.ι ≫ P.obj.right.hom) Λ).Additive :=
  (congrArg (fun h ↦ etaleModulePushforward h Λ) (Over.w P.obj.hom).symm) ▸
    inferInstanceAs ((etaleModulePushforward f Λ).Additive)

/-- Right-derivability of module pushforward along the composite interior of `P`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_P_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (P.ι ≫ P.obj.right.hom) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  (congrArg (fun h ↦ RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (Over.w P.obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
        (HomologicalComplex.quasiIso
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Iterated module pushforward of `P`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_P_comp :
    (etaleModulePushforward P.ι Λ ⋙
      etaleModulePushforward P.obj.right.hom Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward (Of.ι P) Λ ⋙
      etaleModulePushforward P.obj.right.hom Λ).Additive)

/-- Right-derivability of iterated module pushforward of `P`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_P_comp :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward P.ι Λ ⋙
          etaleModulePushforward P.obj.right.hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (Of.ι P) Λ ⋙
          etaleModulePushforward P.obj.right.hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Pushforward along `Over.mk f'` transfers from `f'`. -/
instance (priority := 10000) instAdditive_sheafPushforward_overMk_f'_hom :
    ((smallEtalePullback (Over.mk f').hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (Over.mk f').left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback f').sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology X'.smallEtaleTopology).Additive)

/-- Right-derivability of pushforward along `Over.mk f'`. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_overMk_f'_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (Over.mk f').hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y'.smallEtaleTopology
          (Over.mk f').left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f').sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y'.smallEtaleTopology X'.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along `Over.mk f'`. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_overMk_f'_hom :
    (etaleModulePushforward (Over.mk f').hom Λ).Additive :=
  inferInstanceAs ((etaleModulePushforward f' Λ).Additive)

/-- Right-derivability of module pushforward along `Over.mk f'`. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_overMk_f'_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (Over.mk f').hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Interior pushforward along the base-changed compactification. -/
instance (priority := 10000) instAdditive_sheafPushforward_compactificationPullback_ι :
    ((smallEtalePullback
        (compactificationPullback f g f' g' h_cart P).ι).sheafPushforwardContinuous
      (ModuleCat.{u} Λ)
      (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
      (Over.mk f').left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (interiorLift f g f' g' h_cart P)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (ambient f g f' g' h_cart P).smallEtaleTopology
      X'.smallEtaleTopology).Additive)

/-- Right-derivability of interior pushforward of the base-changed compactification. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_compactificationPullback_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            (compactificationPullback f g f' g' h_cart P).ι).sheafPushforwardContinuous
          (ModuleCat.{u} Λ)
          (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
          (Over.mk f').left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (interiorLift f g f' g' h_cart P)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (ambient f g f' g' h_cart P).smallEtaleTopology
          X'.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along the interior of the base-changed compactification. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_compactificationPullback_ι :
    (etaleModulePushforward (compactificationPullback f g f' g' h_cart P).ι Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward (interiorLift f g f' g' h_cart P) Λ).Additive)

/-- Right-derivability of module pushforward along the interior of the
base-changed compactification. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_compactificationPullback_ι :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (compactificationPullback f g f' g' h_cart P).ι Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (interiorLift f g f' g' h_cart P) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Composite interior of the base-changed compactification is `f'`. -/
instance (priority := 10000) instAdditive_sheafPushforward_compactificationPullback_ι_comp_hom :
    ((smallEtalePullback
        ((compactificationPullback f g f' g' h_cart P).ι ≫
          (compactificationPullback f g f' g' h_cart P).obj.right.hom)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (Over.mk f').left.smallEtaleTopology).Additive :=
  (congrArg
      (fun h ↦ (smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y'.smallEtaleTopology
        (Over.mk f').left.smallEtaleTopology)
      (Over.w (compactificationPullback f g f' g' h_cart P).obj.hom).symm) ▸
    inferInstanceAs
      (((smallEtalePullback f').sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y'.smallEtaleTopology X'.smallEtaleTopology).Additive)

/-- Right-derivability of the composite interior of the base-changed
compactification. -/
instance (priority := 10000) instHasRightDerived_sheafPushforward_compactificationPullback_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            ((compactificationPullback f g f' g' h_cart P).ι ≫
              (compactificationPullback f g f' g' h_cart P).obj.right.hom)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y'.smallEtaleTopology
          (Over.mk f').left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  (congrArg
      (fun h ↦ RightDerived.Cochain.toDerived
        ((smallEtalePullback h).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y'.smallEtaleTopology
          (Over.mk f').left.smallEtaleTopology))
      (Over.w (compactificationPullback f g f' g' h_cart P).obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          ((smallEtalePullback f').sheafPushforwardContinuous
            (ModuleCat.{u} Λ) Y'.smallEtaleTopology X'.smallEtaleTopology))
        (HomologicalComplex.quasiIso
          (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Module pushforward along the composite interior of the base-changed
compactification. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_compactificationPullback_ι_comp_hom :
    (etaleModulePushforward
      ((compactificationPullback f g f' g' h_cart P).ι ≫
        (compactificationPullback f g f' g' h_cart P).obj.right.hom) Λ).Additive :=
  (congrArg (fun h ↦ etaleModulePushforward h Λ)
      (Over.w (compactificationPullback f g f' g' h_cart P).obj.hom).symm) ▸
    inferInstanceAs ((etaleModulePushforward f' Λ).Additive)

/-- Right-derivability of module pushforward along the composite interior of the
base-changed compactification. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_compactificationPullback_ι_comp_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward
          ((compactificationPullback f g f' g' h_cart P).ι ≫
            (compactificationPullback f g f' g' h_cart P).obj.right.hom) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  (congrArg (fun h ↦ RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (Over.w (compactificationPullback f g f' g' h_cart P).obj.hom).symm) ▸
    inferInstanceAs
      (HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
        (HomologicalComplex.quasiIso
          (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Iterated module pushforward of the base-changed compactification. -/
instance (priority := 10000) instAdditive_etaleModulePushforward_compactificationPullback_comp :
    (etaleModulePushforward (compactificationPullback f g f' g' h_cart P).ι Λ ⋙
      etaleModulePushforward
        (compactificationPullback f g f' g' h_cart P).obj.right.hom Λ).Additive :=
  inferInstanceAs
    ((etaleModulePushforward (interiorLift f g f' g' h_cart P) Λ ⋙
      etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ).Additive)

/-- Right-derivability of iterated module pushforward of the base-changed
compactification. -/
instance (priority := 10000) instHasRightDerived_etaleModulePushforward_compactificationPullback_comp :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (compactificationPullback f g f' g' h_cart P).ι Λ ⋙
          etaleModulePushforward
            (compactificationPullback f g f' g' h_cart P).obj.right.hom Λ))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (interiorLift f g f' g' h_cart P) Λ ⋙
          etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))

/-- Compactification model of `Rf'_* ∘ (g')⁻¹`. -/
irreducible_def baseChangeStarCodomain :
    EtaleDerived X Λ ⥤ EtaleDerived Y' Λ :=
  have := f
  have := g
  have := h_cart
  have := P
  etaleModuleDerivedInverseImage g' Λ ⋙
    (etaleDerivedPushforward f' : EtaleDerived X' Λ ⥤ EtaleDerived Y' Λ)

/-- Whiskered `toPushforward` followed by the star-side mate, from
`g⁻¹ ∘ Rf_!` to `Rf'_* ∘ (g')⁻¹`. -/
irreducible_def toPushforward_baseChangeStar :
    baseChangeDomain f g P Λ ⟶
      baseChangeStarCodomain f g f' g' h_cart P Λ :=
  eqToHom (baseChangeDomain_def f g P Λ) ≫
    whiskerRight (toPushforward (Over.mk f) P)
      (etaleModuleDerivedInverseImage g Λ) ≫
    etaleDerivedPushforwardBaseChange f g f' g' h_cart Λ ≫
    eqToHom (baseChangeStarCodomain_def f g f' g' h_cart P Λ).symm

/-- Whiskered `toPushforward` from `Rf'_! ∘ (g')⁻¹` to `Rf'_* ∘ (g')⁻¹`. -/
irreducible_def toPushforward_baseChangeCodomain :
    baseChangeCodomain f g f' g' h_cart P Λ ⟶
      baseChangeStarCodomain f g f' g' h_cart P Λ :=
  eqToHom (baseChangeCodomain_def f g f' g' h_cart P Λ) ≫
    whiskerLeft (etaleModuleDerivedInverseImage g' Λ)
      (toPushforward (Over.mk f')
        (compactificationPullback f g f' g' h_cart P)) ≫
    eqToHom (baseChangeStarCodomain_def f g f' g' h_cart P Λ).symm

/-- Composite of shriek-side base change with whiskered `toPushforward`. -/
irreducible_def toPushforward_baseChange_comp :
    baseChangeDomain f g P Λ ⟶
      baseChangeStarCodomain f g f' g' h_cart P Λ :=
  baseChange f g f' g' h_cart P Λ ≫
    toPushforward_baseChangeCodomain f g f' g' h_cart P Λ

/-- Compatibility of `toPushforward` with `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` and
the derived pushforward mate of Remark 21.19.3. -/
theorem toPushforward_baseChange_compat :
    toPushforward_baseChangeStar f g f' g' h_cart P Λ =
      toPushforward_baseChange_comp f g f' g' h_cart P Λ :=
  sorry

end BaseChangeCompat

end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
