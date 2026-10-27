/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.GeometricFiber
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Stalk

/-!
# Derived lower-shriek stalks and compactly supported fibre cohomology
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
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

open etaleDerivedLowerShriek

section StalkComparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)
variable [IsSeparated f] [Scheme.Hom.FiniteType f]
variable [IsSeparated (geometricFiberOverField f ybar).hom]
variable [Scheme.Hom.FiniteType (geometricFiberOverField f ybar).hom]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace (Hom.geometricFiber f ybar)]
variable [QuasiSeparatedSpace (Hom.geometricFiber f ybar)]
variable [CompactSpace (Spec (CommRingCat.of ybar.K))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of ybar.K))]
variable (P : Of Y (Over.mk f))
variable (Λ : Type u) [CommRing Λ]

variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (Hom.geometricFiber f ybar).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify (Hom.geometricFiber f ybar).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (Hom.geometricFiber f ybar).Etale,
  HasWeakSheafify ((Hom.geometricFiber f ybar).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf (Hom.geometricFiber f ybar).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (Spec (CommRingCat.of ybar.K)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of ybar.K)).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).Etale,
  HasWeakSheafify ((ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology (ModuleCat.{u} Λ))]

  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (Hom.geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (Hom.geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  AddCommGrpCat.{u}]

  [HasSheafCompose X.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (Hom.geometricFiber f ybar).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(Hom.geometricFiber f ybar).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(Spec (CommRingCat.of ybar.K)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback ybar.hom).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (geometricFiberToX f ybar)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : (Spec (CommRingCat.of ybar.K)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P ≫ ybar.hom)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P ≫ P.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P ≫
      ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (geometricFiberToX f ybar ≫ Of.ι P)).op.HasLeftKanExtension F]

  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback ybar.hom).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (geometricFiberToX f ybar)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (geometricFiberToX f ybar : Hom.geometricFiber f ybar ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (geometricFiberToX f ybar : Hom.geometricFiber f ybar ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]

  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback ybar.hom).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (geometricFiberToX f ybar)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op]

  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (Hom.geometricFiber f ybar).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : (Hom.geometricFiber f ybar).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]

  [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) (ModuleCat.{u} Λ))]

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
  [((smallEtalePullback (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
    (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
      (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

  [(etaleModulePushforward P.obj.right.hom Λ ⋙
    smallEtaleInverseImage ybar.hom (ModuleCat.{u} Λ)).Additive]
  [(smallEtaleInverseImage (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) (ModuleCat.{u} Λ) ⋙
    etaleModulePushforward (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) Λ).Additive]
  [(etaleModulePushforward (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) Λ).Additive]
  [(etaleModulePushforward P.obj.right.hom Λ).Additive]


  [HasDerivedCategory (ModuleCat.{u} Λ)]
  [((sheafSections (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (globalEtale (Spec (CommRingCat.of ybar.K))))).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale (Spec (CommRingCat.of ybar.K))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

-- Match `Over.mk f` with the explicit over-object used by `baseChangeUnfolded`.
set_option backward.isDefEq.respectTransparency false in
/-- Objectwise comparison `(Rf_! K)_ȳ ⟶ RΓ_c(X_ȳ, K|_{X_ȳ})`, obtained by
applying derived sections to lower-shriek base change on the geometric-fibre
square. -/
def etaleDerivedLowerShriekStalkCompactSupport_app (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    etaleDerivedGammaStalk ybar
        ((etaleDerivedLowerShriek (Λ := Λ)
          { left := X, right := ⟨⟨⟩⟩, hom := f } P).obj K) ⟶
      (etaleDerivedGammaCompactSupport (Λ := Λ) (X := geometricFiberOverField f ybar)
          (Compactification.geometricFiber f ybar P)).obj
        ((etaleModuleDerivedInverseImage (geometricFiberToX f ybar) Λ).obj K) :=
  (etaleDerivedGamma (Spec (CommRingCat.of ybar.K)) Λ).map
    ((baseChangeUnfolded f ybar.hom (geometricFiberToPoint f ybar)
        (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P Λ).app K)

/-- Canonical comparison of functors `D(X_étale, Λ) ⥤ D(Λ)` obtained by
applying derived sections to lower-shriek base change on the geometric fibre. -/
def etaleDerivedLowerShriekStalkCompactSupport :
    (etaleDerivedLowerShriek (Λ := Λ)
          { left := X, right := ⟨⟨⟩⟩, hom := f } P ⋙
        etaleModuleDerivedInverseImage ybar.hom Λ ⋙
        etaleDerivedGamma (Spec (CommRingCat.of ybar.K)) Λ) ⟶
      (etaleModuleDerivedInverseImage (geometricFiberToX f ybar) Λ ⋙
        etaleDerivedGammaCompactSupport (Λ := Λ) (X := geometricFiberOverField f ybar)
          (Compactification.geometricFiber f ybar P)) where
  app K := etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K
  naturality := sorry

/-- The objectwise comparison is the component of
`etaleDerivedLowerShriekStalkCompactSupport`. -/
theorem etaleDerivedLowerShriekStalkCompactSupport_app_eq
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K =
      (etaleDerivedLowerShriekStalkCompactSupport f ybar P Λ).app K :=
  sorry

/-- On objects of `D⁺_tors(X_étale, Λ)`, the stalk comparison is an
isomorphism. -/
theorem isIso_etaleDerivedLowerShriekStalkCompactSupport_of_isGE_isTorsion
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K)
    (n : ℤ) [hGE : DerivedCategory.IsGE K n] :
    IsIso (etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K) :=
  sorry

/-- If `Λ` is torsion, the stalk comparison is an isomorphism on all of
`D(X_étale, Λ)`. -/
theorem isIso_etaleDerivedLowerShriekStalkCompactSupport_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso (etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K) :=
  sorry

/-- If `Λ` is torsion, the functorial stalk comparison is an isomorphism. -/
theorem isIso_etaleDerivedLowerShriekStalkCompactSupport_natTrans_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) :
    IsIso (etaleDerivedLowerShriekStalkCompactSupport f ybar P Λ) :=
  sorry

/-- The geometric-stalk comparison is invertible at every admissible complex. -/
instance etaleDerivedLowerShriekStalkCompactSupport_app_isIso
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    [hK : Fact (Derived.compactSupportAdmissible X Λ K)] :
    IsIso (etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K) := by
  rcases hK.out with ⟨ht, n, hn⟩ | hΛ
  · exact isIso_etaleDerivedLowerShriekStalkCompactSupport_of_isGE_isTorsion
      f ybar P Λ K ht n (hGE := hn)
  · exact isIso_etaleDerivedLowerShriekStalkCompactSupport_of_isTorsion
      f ybar P Λ hΛ K

/-- Torsion coefficients make the geometric-stalk comparison invertible as a
natural transformation. -/
instance etaleDerivedLowerShriekStalkCompactSupport_isIso
    [hΛ : Fact (AddMonoid.IsTorsion Λ)] :
    IsIso (etaleDerivedLowerShriekStalkCompactSupport f ybar P Λ) :=
  isIso_etaleDerivedLowerShriekStalkCompactSupport_natTrans_of_isTorsion
    f ybar P Λ hΛ.out

/-- For a separated finite-type morphism, the geometric stalk of derived lower
shriek of a bounded-below torsion complex is canonically isomorphic to the
compactly supported cohomology of its geometric fibre. -/
def etaleDerivedLowerShriekStalkCompactSupportIso
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K)
    (n : ℤ) [hGE : DerivedCategory.IsGE K n] :
    etaleDerivedGammaStalk ybar
        ((etaleDerivedLowerShriek (Λ := Λ)
          { left := X, right := ⟨⟨⟩⟩, hom := f } P).obj K) ≅
      (etaleDerivedGammaCompactSupport (Λ := Λ) (X := geometricFiberOverField f ybar)
          (Compactification.geometricFiber f ybar P)).obj
        ((etaleModuleDerivedInverseImage (geometricFiberToX f ybar) Λ).obj K) :=
  @asIso _ _ _ _
    (etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K)
    (isIso_etaleDerivedLowerShriekStalkCompactSupport_of_isGE_isTorsion
      f ybar P Λ K h_tors n)

/-- The forward map of `etaleDerivedLowerShriekStalkCompactSupportIso` is the
stalk comparison `(Rf_! K)_ȳ ⟶ RΓ_c(X_ȳ, K|_{X_ȳ})`. -/
theorem etaleDerivedLowerShriekStalkCompactSupportIso_hom
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K)
    (n : ℤ) [hGE : DerivedCategory.IsGE K n] :
    (etaleDerivedLowerShriekStalkCompactSupportIso f ybar P Λ K h_tors n).hom =
      etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K :=
  sorry

/-- Over a torsion coefficient ring, the geometric stalk of derived lower shriek
is canonically isomorphic to compactly supported geometric-fibre cohomology
for every complex. -/
def etaleDerivedLowerShriekStalkCompactSupportIso_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    etaleDerivedGammaStalk ybar
        ((etaleDerivedLowerShriek (Λ := Λ)
          { left := X, right := ⟨⟨⟩⟩, hom := f } P).obj K) ≅
      (etaleDerivedGammaCompactSupport (Λ := Λ) (X := geometricFiberOverField f ybar)
          (Compactification.geometricFiber f ybar P)).obj
        ((etaleModuleDerivedInverseImage (geometricFiberToX f ybar) Λ).obj K) :=
  @asIso _ _ _ _
    (etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K)
    (isIso_etaleDerivedLowerShriekStalkCompactSupport_of_isTorsion
      f ybar P Λ hΛ K)

/-- The forward map of
`etaleDerivedLowerShriekStalkCompactSupportIso_of_isTorsion` is the stalk
comparison `(Rf_! K)_ȳ ⟶ RΓ_c(X_ȳ, K|_{X_ȳ})`. -/
theorem etaleDerivedLowerShriekStalkCompactSupportIso_of_isTorsion_hom
    (hΛ : AddMonoid.IsTorsion Λ) (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedLowerShriekStalkCompactSupportIso_of_isTorsion f ybar P Λ hΛ
        K).hom =
      etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K :=
  sorry

end StalkComparison

end AlgebraicGeometry.Scheme.Etale

end
