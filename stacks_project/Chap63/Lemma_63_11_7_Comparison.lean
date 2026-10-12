/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.GroupTheory.Torsion
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import stacks_project.Chap63.Lemma_63_9_4_Cartesian
public import stacks_project.Chap63.«63_11_4_1_UpperShriek»

/-!
# Uniqueness comparison for cartesian base change of derived étale upper shriek

The missing derived adjunction `g⁻¹ ⊣ Rg_*` on unbounded étale module
categories, and the conjugate of `etaleDerivedLowerShriek.baseChangeIso`
identifying `Rg_* ⋙ Rf^!` with `R(f')^! ⋙ Rg'_*`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.Etale
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section InverseImagePushforward

variable {A B : Scheme.{u}} (h : A ⟶ B) (Λ : Type u) [CommRing Λ]
variable [HasSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : A.Etale,
  HasWeakSheafify (A.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : B.Etale,
  HasWeakSheafify (B.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback h).op.HasLeftKanExtension F]
variable [((smallEtalePullback h).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback h).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
variable [IsGrothendieckAbelian (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- The unbounded derived adjunction `g⁻¹ ⊣ Rg_*` on étale sheaves of
`Λ`-modules, obtained by deriving the sheaf-level adjunction
`etaleModuleSheafPullback ⊣ etaleModulePushforward` and identifying the
K-injective right derived functor with `etaleDerivedPushforward`. -/
def etaleModuleDerivedInverseImageAdjunction :
    etaleModuleDerivedInverseImage h Λ ⊣ etaleDerivedPushforward h :=
  (Adjunction.Derived.KInjective.adjunction
      (ExactFunctor.of (etaleModuleSheafPullback h Λ))
      (etaleModulePushforward h Λ)
      ((smallEtalePullback h).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
        B.smallEtaleTopology A.smallEtaleTopology)).ofNatIsoRight
    ((Adjunction.Derived.KInjective.right (etaleModulePushforward h Λ)).rightDerivedUnique
      (etaleDerivedPushforward h)
      (Adjunction.Derived.KInjective.rightUnit (etaleModulePushforward h Λ))
      (RightDerived.Cochain.unit (etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ)))

/-- The hom-equivalence of the derived inverse-image/pushforward adjunction. -/
def etaleModuleDerivedInverseImageAdjunction_homEquiv
    (K : EtaleDerived B Λ) (L : EtaleDerived A Λ) :
    ((etaleModuleDerivedInverseImage h Λ).obj K ⟶ L) ≃
      (K ⟶ (etaleDerivedPushforward h).obj L) :=
  (etaleModuleDerivedInverseImageAdjunction h Λ).homEquiv K L

/-- The derived inverse-image/pushforward adjunction is the K-injective derived
adjunction of sheaf pullback, transported along uniqueness of right derived
functors onto `etaleDerivedPushforward`. -/
theorem etaleModuleDerivedInverseImageAdjunction_def :
    etaleModuleDerivedInverseImageAdjunction h Λ =
      (Adjunction.Derived.KInjective.adjunction
          (ExactFunctor.of (etaleModuleSheafPullback h Λ))
          (etaleModulePushforward h Λ)
          ((smallEtalePullback h).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
            B.smallEtaleTopology A.smallEtaleTopology)).ofNatIsoRight
        ((Adjunction.Derived.KInjective.right
            (etaleModulePushforward h Λ)).rightDerivedUnique
          (etaleDerivedPushforward h)
          (Adjunction.Derived.KInjective.rightUnit (etaleModulePushforward h Λ))
          (RightDerived.Cochain.unit (etaleModulePushforward h Λ))
          (HomologicalComplex.quasiIso
            (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))) :=
  sorry

end InverseImagePushforward

section Cartesian

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
  [HasSheafify (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).Etale,
  HasWeakSheafify
    ((etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
    (ModuleCat.{u} Λ))]

  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
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
  [HasSheafCompose (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
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
  [(etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P ≫ g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P ≫
      P.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P ≫
      etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ Of.ι P)).op.HasLeftKanExtension F]

  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]

  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)).op]

  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]

  [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ))]

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
    (up ℤ))]
  [((smallEtalePullback
      (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology
    (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
      (ModuleCat.{u} Λ))
    (up ℤ))]

  [(etaleModulePushforward P.obj.right.hom Λ ⋙
    etaleModuleSheafPullback g Λ).Additive]
  [(etaleModuleSheafPullback
      (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P) Λ ⋙
    etaleModulePushforward
      (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward
      (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward P.obj.right.hom Λ).Additive]

  [((smallEtalePullback g).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology Y'.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback g).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology Y'.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
  [((smallEtalePullback g').sheafPushforwardContinuous
    (ModuleCat.{u} Λ) X.smallEtaleTopology X'.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback g').sheafPushforwardContinuous
      (ModuleCat.{u} Λ) X.smallEtaleTopology X'.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
  [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [IsGrothendieckAbelian (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [((etaleDerivedLowerShriek (Over.mk f) P :
      EtaleDerived (Over.mk f).left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]
  [((etaleDerivedLowerShriek (Over.mk f')
      (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P) :
      EtaleDerived (Over.mk f').left Λ ⥤ EtaleDerived Y' Λ)).IsLeftAdjoint]

namespace etaleDerivedLowerShriek

/-- Identification of `lowerShriekPullback` with the compactification
presentation `Rf'_!` of `compactificationPullback`. -/
def lowerShriekPullbackIso :
    lowerShriekPullback f g f' g' h_cart P Λ ≅
      etaleDerivedLowerShriek (Over.mk f')
        (compactificationPullback f g f' g' h_cart P) :=
  eqToIso rfl

end etaleDerivedLowerShriek

namespace etaleDerivedUpperShriek

/-- The composite left adjoints `Rf'_! ∘ (g')⁻¹` and `g⁻¹ ∘ Rf_!` after
transporting `etaleDerivedLowerShriek.baseChangeIso` off its irreducible
compactification models. -/
def baseChangeLeftIso (hΛ : AddMonoid.IsTorsion Λ) :
    etaleModuleDerivedInverseImage g' Λ ⋙
        etaleDerivedLowerShriek (Over.mk f')
          (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P) ≅
      etaleDerivedLowerShriek (Over.mk f) P ⋙
        etaleModuleDerivedInverseImage g Λ :=
  (isoWhiskerLeft (etaleModuleDerivedInverseImage g' Λ)
      (etaleDerivedLowerShriek.lowerShriekPullbackIso f g f' g' h_cart P Λ)).symm ≪≫
    eqToIso (etaleDerivedLowerShriek.baseChangeCodomain_def f g f' g' h_cart P Λ).symm ≪≫
    (etaleDerivedLowerShriek.baseChangeIso f g f' g' h_cart P Λ hΛ).symm ≪≫
    eqToIso (etaleDerivedLowerShriek.baseChangeDomain_def f g P Λ)

/-- The uniqueness-of-adjoints isomorphism
`Rg_* ⋙ Rf^! ≅ R(f')^! ⋙ Rg'_*` conjugate to lower-shriek base change. -/
def baseChangeComparisonIso (hΛ : AddMonoid.IsTorsion Λ) :
    etaleDerivedPushforward g ⋙ etaleDerivedUpperShriek (Over.mk f) Λ P ≅
      etaleDerivedUpperShriek (Over.mk f') Λ
          (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P) ⋙
        etaleDerivedPushforward g' :=
  conjugateIsoEquiv
    ((etaleDerivedLowerShriekAdjunction (Over.mk f) Λ P).comp
      (etaleModuleDerivedInverseImageAdjunction g Λ))
    ((etaleModuleDerivedInverseImageAdjunction g' Λ).comp
      (etaleDerivedLowerShriekAdjunction (Over.mk f') Λ
        (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P)))
    (baseChangeLeftIso f g f' g' h_cart P Λ hΛ)

/-- Objectwise evaluation of `baseChangeComparisonIso`. -/
def baseChangeComparisonIso_app
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived Y' Λ) :
    (etaleDerivedUpperShriek (Over.mk f) Λ P).obj
        ((etaleDerivedPushforward g).obj K) ≅
      (etaleDerivedPushforward g').obj
        ((etaleDerivedUpperShriek (Over.mk f') Λ
            (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P)).obj
          K) :=
  (baseChangeComparisonIso f g f' g' h_cart P Λ hΛ).app K

/-- The comparison isomorphism is the conjugate of the transported inverse of
`etaleDerivedLowerShriek.baseChangeIso` along the composite adjunctions
`etaleDerivedLowerShriekAdjunction` then
`etaleModuleDerivedInverseImageAdjunction`. -/
theorem baseChangeComparisonIso_spec
    (hΛ : AddMonoid.IsTorsion Λ) :
    baseChangeComparisonIso f g f' g' h_cart P Λ hΛ =
      conjugateIsoEquiv
        ((etaleDerivedLowerShriekAdjunction (Over.mk f) Λ P).comp
          (etaleModuleDerivedInverseImageAdjunction g Λ))
        ((etaleModuleDerivedInverseImageAdjunction g' Λ).comp
          (etaleDerivedLowerShriekAdjunction (Over.mk f') Λ
            (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P)))
        (baseChangeLeftIso f g f' g' h_cart P Λ hΛ) :=
  sorry

end etaleDerivedUpperShriek

end Cartesian

end AlgebraicGeometry.Scheme.Etale

end
