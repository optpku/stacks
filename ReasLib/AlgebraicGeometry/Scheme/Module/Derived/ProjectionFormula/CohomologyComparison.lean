/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.KFlatModel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Delta
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.ProjectionFormula
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.KFlat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.DeltaFunctor
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Composition
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Morphism
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory CategoryTheory.Pretriangulated
open RingedSite.Hom
open RingedSpace.ModuleDerived
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme

namespace ModuleDerived
namespace ProjectionFormula

/-- Postcompose a delta functor with canonical fixed-right derived tensoring. -/
noncomputable def postcomposeRightTensor {A : Type (u + 1)} [Category.{u} A] [Abelian A]
    (X : Scheme.{u}) (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (D : DeltaFunctor A (RingedSpace.ModuleDerived X.toRingedSpace)) :
    DeltaFunctor A (RingedSpace.ModuleDerived X.toRingedSpace) :=
  D.postcomposeExactFunctor (DerivedTensor.Right.functor K)

/-- The underlying functor after `postcomposeRightTensor` is ordinary functor composition. -/
theorem postcomposeRightTensor_toFunctor {A : Type (u + 1)} [Category.{u} A] [Abelian A]
    (X : Scheme.{u}) (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (D : DeltaFunctor A (RingedSpace.ModuleDerived X.toRingedSpace)) :
    (postcomposeRightTensor X K D).toFunctor =
      D.toFunctor ⋙ DerivedTensor.Right.functor K := sorry

/-- The complex `K = Rfₙ(E ⊗ᴸ Q(G))` occurring in the projection formula. -/
noncomputable def kernel {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ) :
    RingedSpace.ModuleDerived S.toRingedSpace :=
  (RingedSpace.moduleDerivedPushforward f.toShHom).obj
    (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))

/-- The defining expression for the projection-formula kernel. -/
theorem kernel_def {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ) :
    kernel f E G =
      (RingedSpace.moduleDerivedPushforward f.toShHom).obj
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G)) := sorry

/-- The ordinary complex `G• ⊗ f^*F`, functorial in the coefficient module `F`. -/
noncomputable def coefficientComplexFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ) :
    S.Modules ⥤ CochainComplex X.Modules ℤ :=
  CochainComplex.singleFunctor S.Modules 0 ⋙
    (RingedSpace.Hom.pullback f.toShHom).mapHomologicalComplex (up ℤ) ⋙
      ((curriedTensor X.Modules).map₂CochainComplex).obj G

/-- The coefficient complex attached to `F` is the ordinary totalized complex
`G• ⊗ f^*F`. -/
noncomputable def coefficientComplex {X S : Scheme.{u}} (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ) (F : S.Modules) :
    CochainComplex X.Modules ℤ :=
  (coefficientComplexFunctor f G).obj F

/-- Evaluation of the coefficient-complex functor gives `coefficientComplex`. -/
theorem coefficientComplexFunctor_obj {X S : Scheme.{u}} (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ) (F : S.Modules) :
    (coefficientComplexFunctor f G).obj F = coefficientComplex f G F := sorry

/-- Relative flatness of the terms of `G` makes the coefficient-complex functor exact. -/
theorem coefficientComplexFunctor_exact {X S : Scheme.{u}} (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom] :
    exactFunctor S.Modules (CochainComplex X.Modules ℤ)
      (coefficientComplexFunctor f G) := sorry

/-- The ordinary coefficient-complex functor bundled with its exactness. -/
noncomputable def coefficientComplexExactFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom] :
    S.Modules ⥤ₑ CochainComplex X.Modules ℤ :=
  ⟨coefficientComplexFunctor f G, coefficientComplexFunctor_exact f G⟩

/-- The underlying functor of `coefficientComplexExactFunctor` is the ordinary
coefficient-complex functor. -/
theorem coefficientComplexExactFunctor_obj {X S : Scheme.{u}} (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom] :
    (coefficientComplexExactFunctor f G).obj = coefficientComplexFunctor f G := sorry

/-- The canonical comparison from derived pullback of a degree-zero coefficient module to the
localized ordinary pullback complex. -/
noncomputable def pullbackSingleComplexComparison {X S : Scheme.{u}} (f : X ⟶ S)
    (F : S.Modules) :
    (RingedSpace.modulePullbackDerived f.toShHom).obj
        ((DerivedCategory.singleFunctor S.Modules 0).obj F) ⟶
      DerivedCategory.Q.obj
        (((RingedSpace.Hom.pullback f.toShHom).mapHomologicalComplex (up ℤ)).obj
          ((CochainComplex.singleFunctor S.Modules 0).obj F)) :=
  let SF := (CochainComplex.singleFunctor S.Modules 0).obj F
  (RingedSpace.modulePullbackDerived f.toShHom).map
      ((DerivedCategory.singleFunctorIsoCompQ S.Modules 0).hom.app F) ≫
    (RingedSpace.modulePullbackDerived f.toShHom).map
      ((DerivedCategory.quotientCompQhIso S.Modules).inv.app SF) ≫
    ((RingedSpace.modulePullbackToDerived f.toShHom).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis S.toRingedSpace)).app
        ((HomotopyCategory.quotient S.Modules (up ℤ)).obj SF) ≫
    (DerivedCategory.quotientCompQhIso X.Modules).hom.app
      (((RingedSpace.Hom.pullback f.toShHom).mapHomologicalComplex (up ℤ)).obj SF)

/-- The derived-to-ordinary comparison for the coefficient complex `G• ⊗ f^*F`,
computed from a supplied two-variable derived tensor. -/
noncomputable def coefficientComparisonWithBifunctor {X S : Scheme.{u}} (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ) (F : S.Modules)
    [h : DerivedTensor.Bifunctor.Has
      (C := RingedSpace.Modules X.toRingedSpace)] :
    DerivedTensor.Right.obj
        (DerivedCategory.Q.obj G : RingedSpace.ModuleDerived X.toRingedSpace)
        ((RingedSpace.modulePullbackDerived f.toShHom).obj
          ((DerivedCategory.singleFunctor S.Modules 0).obj F)) ⟶
      DerivedCategory.Q.obj (coefficientComplex f G F) :=
  let G' : CochainComplex (RingedSpace.Modules X.toRingedSpace) ℤ := G
  let SF := (CochainComplex.singleFunctor S.Modules 0).obj F
  let PF := ((RingedSpace.Hom.pullback f.toShHom).mapHomologicalComplex (up ℤ)).obj SF
  (DerivedTensor.Bifunctor.Right.isoApp
      ((RingedSpace.modulePullbackDerived f.toShHom).obj
        ((DerivedCategory.singleFunctor S.Modules 0).obj F))
      (DerivedCategory.Q.obj G')).hom ≫
    (DerivedTensor.Bifunctor.functor
      (C := RingedSpace.Modules X.toRingedSpace)).map
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj G' :
          RingedSpace.ModuleDerived X.toRingedSpace))
        (pullbackSingleComplexComparison f F)) ≫
    DerivedTensor.Bifunctor.counitAppOfQ G' PF

/-- The canonical derived-to-ordinary comparison for the coefficient complex
`G• ⊗ f^*F`, obtained from the canonical two-variable derived tensor model. -/
noncomputable def coefficientComparison {X S : Scheme.{u}} (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ) (F : S.Modules) :
    DerivedTensor.Right.obj
        (DerivedCategory.Q.obj G : RingedSpace.ModuleDerived X.toRingedSpace)
        ((RingedSpace.modulePullbackDerived f.toShHom).obj
          ((DerivedCategory.singleFunctor S.Modules 0).obj F)) ⟶
      DerivedCategory.Q.obj (coefficientComplex f G F) :=
  coefficientComparisonWithBifunctor (h := hasDerivedTensorBifunctor X) f G F

/-- The canonical coefficient comparison agrees with every supplied two-variable derived
tensor presentation. -/
theorem coefficientComparison_eq_withBifunctor {X S : Scheme.{u}} (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ) (F : S.Modules)
    [h : DerivedTensor.Bifunctor.Has
      (C := RingedSpace.Modules X.toRingedSpace)] :
    coefficientComparison f G F = coefficientComparisonWithBifunctor f G F := sorry

/-- Additive global sections on the opens ringed sites commute canonically with direct image. -/
noncomputable def ringedSiteGlobalSectionsPushforwardIso {X S : Scheme.{u}} (f : X ⟶ S) :
    RingedSite.Hom.moduleGlobalSectionsAdditiveFunctor
        (RingedSpace.opensRingedSite X.toRingedSpace) ≅
      RingedSite.Hom.modulePushforward (RingedSpace.opensRingedSiteHom f.toShHom) ⋙
        RingedSite.Hom.moduleGlobalSectionsAdditiveFunctor
          (RingedSpace.opensRingedSite S.toRingedSpace) where
  hom := RingedSite.Hom.ModuleSections.pushforwardNat
    (RingedSpace.opensRingedSiteHom f.toShHom)
  inv :=
    { app := fun M ↦
        let hS := congrArg
          (fun H ↦ H.obj ((RingedSite.Hom.modulePushforward
            (RingedSpace.opensRingedSiteHom f.toShHom)).obj M))
          (RingedSite.Hom.moduleGlobalSectionsForget_eq
            (RingedSpace.opensRingedSite S.toRingedSpace))
        let hX := congrArg (fun H ↦ H.obj M)
          (RingedSite.Hom.moduleGlobalSectionsForget_eq
            (RingedSpace.opensRingedSite X.toRingedSpace))
        eqToHom hS.symm ≫
          (forget₂ (ModuleCat (RingedSite.Hom.globalSectionsRing
            (RingedSpace.opensRingedSite S.toRingedSpace))) AddCommGrpCat.{u}).map
            ((RingedSite.Hom.ModuleSections.moduleGlobalSectionsPushforwardNatIso
              (RingedSpace.opensRingedSiteHom f.toShHom)).inv.app M) ≫
          eqToHom hX
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Underlying additive global sections commute canonically with direct image. -/
noncomputable def globalSectionsPushforwardIso {X S : Scheme.{u}} (f : X ⟶ S) :
    (RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace ⋙
        forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}) ≅
      RingedSpace.Hom.pushforward f.toShHom ⋙
        (RingedSpace.moduleGlobalSectionsFunctor S.toRingedSpace ⋙
          forget₂ (ModuleCat S.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}) :=
  RingedSpace.Module.Derived.GlobalSections.additiveIso X.toRingedSpace ≪≫
    ringedSiteGlobalSectionsPushforwardIso f ≪≫
    Functor.isoWhiskerLeft (RingedSpace.Hom.pushforward f.toShHom)
      (RingedSpace.Module.Derived.GlobalSections.additiveIso S.toRingedSpace).symm

/-- The cochain-level additive global-sections comparison for direct image. -/
noncomputable def cochainGlobalSectionsPushforwardIso {X S : Scheme.{u}} (f : X ⟶ S) :
    ((RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace ⋙
          forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapHomologicalComplex
        (up ℤ)) ⋙ DerivedCategory.Q ≅
      (RingedSpace.Hom.pushforward f.toShHom).mapHomologicalComplex (up ℤ) ⋙
        (((RingedSpace.moduleGlobalSectionsFunctor S.toRingedSpace ⋙
            forget₂ (ModuleCat S.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapHomologicalComplex
          (up ℤ)) ⋙ DerivedCategory.Q) :=
  Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (globalSectionsPushforwardIso f) (up ℤ))
      DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.Hom.pushforward f.toShHom ⋙
          (RingedSpace.moduleGlobalSectionsFunctor S.toRingedSpace ⋙
            forget₂ (ModuleCat S.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u})))
        (up ℤ)).symm
      DerivedCategory.Q ≪≫
    Functor.associator _ _ _

/-- The cochain localization of additive global sections agrees with derived module-valued
global sections followed by forgetting scalars. -/
noncomputable def cochainToAbelianSourceIso (X : Scheme.{u}) :
    ((RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace ⋙
          forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapHomologicalComplex
        (up ℤ)) ⋙ DerivedCategory.Q ≅
      (RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q ⋙
          (forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing)
            AddCommGrpCat.{u}).mapDerivedCategory) :=
  Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace ⋙
          forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}))
        (up ℤ)).symm
      DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace).mapHomologicalComplex (up ℤ))
      (forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing)
        AddCommGrpCat.{u}).mapDerivedCategoryFactors.symm

/-- The cochain-level unit for abelian-valued derived global sections, expressed from the
ordinary composite additive functor. -/
noncomputable def globalSectionsToAbelianUnit (X : Scheme.{u}) :
    ((RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace ⋙
          forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapHomologicalComplex
        (up ℤ)) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙
        RingedSpace.Module.Derived.GlobalSections.toAbelian X.toRingedSpace :=
  (cochainToAbelianSourceIso X).hom ≫
    RingedSpace.Module.Derived.GlobalSections.cochainToAbelianUnit X.toRingedSpace

/-- Derived pushforward followed by abelian-valued derived global sections. -/
noncomputable abbrev pushforwardToAbelian {X S : Scheme.{u}} (f : X ⟶ S) :
    RingedSpace.ModuleDerived X.toRingedSpace ⥤ DerivedCategory AddCommGrpCat.{u} :=
  RingedSpace.moduleDerivedPushforward f.toShHom ⋙
    RingedSpace.Module.Derived.GlobalSections.toAbelian S.toRingedSpace

/-- The cochain-level unit for derived pushforward followed by abelian-valued derived global
sections. -/
noncomputable def pushforwardToAbelianUnit {X S : Scheme.{u}} (f : X ⟶ S) :
    ((RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace ⋙
          forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapHomologicalComplex
        (up ℤ)) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ pushforwardToAbelian f :=
  (cochainGlobalSectionsPushforwardIso f).hom ≫
    Functor.RightDerived.Composition.iteratedUnit
      (RingedSpace.moduleDerivedPushforward.unit f.toShHom)
      (globalSectionsToAbelianUnit S)

/-- Abelian-valued derived global sections have the expected cochain-level universal property. -/
noncomputable instance globalSectionsToAbelian_isRightDerived (X : Scheme.{u}) :
    @Functor.IsRightDerivedFunctor
      (C := CochainComplex X.Modules ℤ)
      (D := RingedSpace.ModuleDerived X.toRingedSpace)
      (H := DerivedCategory AddCommGrpCat.{u})
      _ _ _
      (RingedSpace.Module.Derived.GlobalSections.toAbelian X.toRingedSpace)
      (F := _)
      (L := (DerivedCategory.Q :
        CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace))
      (globalSectionsToAbelianUnit X)
      (HomologicalComplex.quasiIso X.Modules (up ℤ))
      (inferInstanceAs
        ((DerivedCategory.Q :
          CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace).IsLocalization
            (HomologicalComplex.quasiIso X.Modules (up ℤ)))) := sorry

/-- The iterated pushforward/global-sections model has the expected cochain-level universal
property. -/
noncomputable instance pushforwardToAbelian_isRightDerived {X S : Scheme.{u}} (f : X ⟶ S) :
    @Functor.IsRightDerivedFunctor
      (C := CochainComplex X.Modules ℤ)
      (D := RingedSpace.ModuleDerived X.toRingedSpace)
      (H := DerivedCategory AddCommGrpCat.{u})
      _ _ _
      (pushforwardToAbelian f)
      (F := _)
      (L := (DerivedCategory.Q :
        CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace))
      (pushforwardToAbelianUnit f)
      (HomologicalComplex.quasiIso X.Modules (up ℤ))
      (inferInstanceAs
        ((DerivedCategory.Q :
          CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace).IsLocalization
            (HomologicalComplex.quasiIso X.Modules (up ℤ)))) := sorry

/-- The Leray comparison computed from supplied right-derived universal properties. -/
noncomputable def pushforwardToAbelianComparisonWithDerived
    {X S : Scheme.{u}} (f : X ⟶ S)
    [hX : @Functor.IsRightDerivedFunctor
      (C := CochainComplex X.Modules ℤ)
      (D := RingedSpace.ModuleDerived X.toRingedSpace)
      (H := DerivedCategory AddCommGrpCat.{u})
      _ _ _
      (RingedSpace.Module.Derived.GlobalSections.toAbelian X.toRingedSpace)
      (F := _)
        (L := (DerivedCategory.Q :
          CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace))
        (globalSectionsToAbelianUnit X)
        (HomologicalComplex.quasiIso X.Modules (up ℤ))
        (inferInstanceAs
          ((DerivedCategory.Q :
            CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace).IsLocalization
              (HomologicalComplex.quasiIso X.Modules (up ℤ))))]
    [hf : @Functor.IsRightDerivedFunctor
      (C := CochainComplex X.Modules ℤ)
      (D := RingedSpace.ModuleDerived X.toRingedSpace)
      (H := DerivedCategory AddCommGrpCat.{u})
      _ _ _
      (pushforwardToAbelian f)
      (F := _)
      (L := (DerivedCategory.Q :
        CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace))
      (pushforwardToAbelianUnit f)
      (HomologicalComplex.quasiIso X.Modules (up ℤ))
      (inferInstanceAs
        ((DerivedCategory.Q :
          CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace).IsLocalization
            (HomologicalComplex.quasiIso X.Modules (up ℤ))))] :
    pushforwardToAbelian f ⟶
      RingedSpace.Module.Derived.GlobalSections.toAbelian X.toRingedSpace :=
  (@Functor.RightDerived.natIsoOfIso
    (C := CochainComplex X.Modules ℤ)
    (D := RingedSpace.ModuleDerived X.toRingedSpace)
    (H := DerivedCategory AddCommGrpCat.{u})
    _ _ _
    (DerivedCategory.Q :
      CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (F := _) (F' := _) (RF := _) (RF' := _)
    (globalSectionsToAbelianUnit X)
    (pushforwardToAbelianUnit f)
    (inferInstanceAs
      ((DerivedCategory.Q :
        CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace).IsLocalization
          (HomologicalComplex.quasiIso X.Modules (up ℤ))))
    hX hf (Iso.refl _)).inv

/-- The canonical forward Leray comparison between global sections after derived pushforward
and global sections on the source. -/
noncomputable def pushforwardToAbelianComparison {X S : Scheme.{u}} (f : X ⟶ S) :
    pushforwardToAbelian f ⟶
      RingedSpace.Module.Derived.GlobalSections.toAbelian X.toRingedSpace :=
  pushforwardToAbelianComparisonWithDerived
    (hX := globalSectionsToAbelian_isRightDerived X)
    (hf := pushforwardToAbelian_isRightDerived f) f

/-- The canonical forward Leray comparison agrees with every presentation by right-derived
universal properties. -/
theorem pushforwardToAbelianComparison_eq_withDerived
    {X S : Scheme.{u}} (f : X ⟶ S)
    [hX : @Functor.IsRightDerivedFunctor
      (C := CochainComplex X.Modules ℤ)
      (D := RingedSpace.ModuleDerived X.toRingedSpace)
      (H := DerivedCategory AddCommGrpCat.{u})
      _ _ _
      (RingedSpace.Module.Derived.GlobalSections.toAbelian X.toRingedSpace)
      (F := _)
        (L := (DerivedCategory.Q :
          CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace))
        (globalSectionsToAbelianUnit X)
        (HomologicalComplex.quasiIso X.Modules (up ℤ))
        (inferInstanceAs
          ((DerivedCategory.Q :
            CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace).IsLocalization
              (HomologicalComplex.quasiIso X.Modules (up ℤ))))]
    [hf : @Functor.IsRightDerivedFunctor
      (C := CochainComplex X.Modules ℤ)
      (D := RingedSpace.ModuleDerived X.toRingedSpace)
      (H := DerivedCategory AddCommGrpCat.{u})
      _ _ _
      (pushforwardToAbelian f)
      (F := _)
      (L := (DerivedCategory.Q :
        CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace))
      (pushforwardToAbelianUnit f)
      (HomologicalComplex.quasiIso X.Modules (up ℤ))
      (inferInstanceAs
        ((DerivedCategory.Q :
          CochainComplex X.Modules ℤ ⥤ RingedSpace.ModuleDerived X.toRingedSpace).IsLocalization
            (HomologicalComplex.quasiIso X.Modules (up ℤ))))] :
    pushforwardToAbelianComparison f =
      pushforwardToAbelianComparisonWithDerived f := sorry

/-- The source delta functor, using the symmetric presentation
`F ↦ RΓ(S, F[0] ⊗ᴸ K)` of `F ↦ RΓ(S, K ⊗ᴸ F[0])`. -/
noncomputable def source {X S : Scheme.{u}}
    (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ) :
    DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u}) :=
  DeltaFunctor.postcomposeExactFunctor
    (DeltaFunctor.postcomposeExactFunctor
      (postcomposeRightTensor S (kernel f E G)
        (RingedSpace.Module.Derived.GlobalSections.Delta.single S.toRingedSpace))
      (RingedSpace.moduleDerivedGlobalSections S.toRingedSpace))
    (forget₂ (ModuleCat S.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapDerivedCategory

/-- The value of `source` is the derived global sections of the symmetric derived tensor
`F[0] ⊗ᴸ K`. -/
theorem source_obj {X S : Scheme.{u}}
    (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ) (F : S.Modules) :
    (source f E G).obj F =
      (RingedSpace.Module.Derived.GlobalSections.toAbelian S.toRingedSpace).obj
        (DerivedTensor.Right.obj
          ((DerivedCategory.singleFunctor S.Modules 0).obj F) (kernel f E G)) := sorry

/-- The target delta functor, using the symmetric presentation
`F ↦ RΓ(X, Q(G• ⊗ f^*F) ⊗ᴸ E)` of
`F ↦ RΓ(X, E ⊗ᴸ Q(G• ⊗ f^*F))`. -/
noncomputable def target {X S : Scheme.{u}}
    (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom] :
    DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u}) :=
  DeltaFunctor.postcomposeExactFunctor
    (DeltaFunctor.postcomposeExactFunctor
      (postcomposeRightTensor X E
        ((DerivedCategory.Delta.functor X.Modules).precomposeExactFunctor
          (coefficientComplexExactFunctor f G)))
      (RingedSpace.moduleDerivedGlobalSections X.toRingedSpace))
    (forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapDerivedCategory

/-- The value of `target` is the derived global sections of the symmetric derived tensor with
the ordinary coefficient complex. -/
theorem target_obj {X S : Scheme.{u}}
    (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    (F : S.Modules) :
    (target f E G).obj F =
      (RingedSpace.Module.Derived.GlobalSections.toAbelian X.toRingedSpace).obj
        (DerivedTensor.Right.obj
          (DerivedCategory.Q.obj (coefficientComplex f G F)) E) := sorry

/-- The component at `F` of the projection-formula comparison computed using selected
functorial K-flat resolutions. The two fixed-right derived tensors are transported to the
ambient K-flat tensor, where the projection-formula mate, associator, and coefficient comparison
form the displayed composite. -/
noncomputable def comparisonAppWithResolutions {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [kflatLocalizationS : DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (P_X : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules X.toRingedSpace))
    (P_S : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules S.toRingedSpace))
    (F : S.Modules) :
    (source f E G).obj F ⟶ (target f E G).obj F :=
  let F₀ : RingedSpace.ModuleDerived S.toRingedSpace :=
    (DerivedCategory.singleFunctor (RingedSpace.Modules S.toRingedSpace) 0).obj F
  let QG : RingedSpace.ModuleDerived X.toRingedSpace := DerivedCategory.Q.obj G
  let fF : RingedSpace.ModuleDerived X.toRingedSpace :=
    (RingedSpace.modulePullbackDerived f.toShHom).obj F₀
  let QGF : RingedSpace.ModuleDerived X.toRingedSpace :=
    DerivedCategory.Q.obj (coefficientComplex f G F)
  (RingedSpace.Module.Derived.GlobalSections.toAbelian S.toRingedSpace).map
      (((DerivedTensor.Right.KFlat.objIsoTensor P_S F₀ (kernel f E G) :
          DerivedTensor.Right.obj F₀ (kernel f E G) ≅ F₀ ⊗ kernel f E G)).hom ≫
        ((RingedSpace.ModuleDerived.symmetricCategory S.toRingedSpace).toBraidedCategory.braiding
          F₀ (kernel f E G)).hom ≫
        RingedSpace.ModuleDerived.ProjectionFormula.leftMate f.toShHom
          (DerivedTensor.Right.obj E QG) F₀ ≫
        (RingedSpace.moduleDerivedPushforward f.toShHom).map
          ((((DerivedTensor.Right.KFlat.objIsoTensor P_X E QG).hom ⊗ₘ 𝟙 fF) ≫
              (α_ E QG fF).hom) ≫
            (𝟙 E ⊗ₘ (DerivedTensor.Right.KFlat.objIsoTensor P_X QG fF).inv) ≫
            (𝟙 E ⊗ₘ coefficientComparison f G F) ≫
            ((RingedSpace.ModuleDerived.symmetricCategory X.toRingedSpace).toBraidedCategory.braiding
              E QGF).hom ≫
            (DerivedTensor.Right.KFlat.objIsoTensor P_X QGF E).inv)) ≫
    (pushforwardToAbelianComparison f).app (DerivedTensor.Right.obj QGF E)

/-- The resolution-dependent components of the projection-formula comparison are natural in the
coefficient module. -/
theorem comparisonAppWithResolutions_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (P_X : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules X.toRingedSpace))
    (P_S : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules S.toRingedSpace))
    {F F' : S.Modules} (φ : F ⟶ F') :
    (source f E G).map φ ≫ comparisonAppWithResolutions f E G P_X P_S F' =
      comparisonAppWithResolutions f E G P_X P_S F ≫ (target f E G).map φ := sorry

/-- The resolution-dependent components of the projection-formula comparison commute with
connecting morphisms. -/
theorem comparisonAppWithResolutions_boundary {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (P_X : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules X.toRingedSpace))
    (P_S : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules S.toRingedSpace))
    {T : ShortComplex S.Modules} (hT : T.ShortExact) :
    CommSq (comparisonAppWithResolutions f E G P_X P_S T.X₃)
      ((source f E G).δ hT) ((target f E G).δ hT)
      ((comparisonAppWithResolutions f E G P_X P_S T.X₁)⟦(1 : ℤ)⟧') := sorry

/-- The boundary-compatible comparison computed from selected functorial K-flat resolutions. -/
noncomputable def comparisonWithResolutions {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (P_X : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules X.toRingedSpace))
    (P_S : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules S.toRingedSpace)) :
    source f E G ⟶ target f E G where
  app :=
    { app := fun F ↦ comparisonAppWithResolutions f E G P_X P_S F
      naturality := fun _ _ φ ↦
        comparisonAppWithResolutions_naturality f E G P_X P_S φ }
  comm := fun _ hT ↦ comparisonAppWithResolutions_boundary f E G P_X P_S hT

/-- Evaluation of the resolution-dependent bundled comparison gives its explicit component. -/
theorem comparisonWithResolutions_app {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (P_X : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules X.toRingedSpace))
    (P_S : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules S.toRingedSpace))
    (F : S.Modules) :
    (comparisonWithResolutions f E G P_X P_S).app.app F =
      comparisonAppWithResolutions f E G P_X P_S F := sorry

/-- The canonical boundary-compatible comparison from the source delta functor to the target
delta functor, computed using the explicit ambient K-flat tensor models. -/
noncomputable def comparison {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [h_homotopy_tensor_X : RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      X.toRingedSpace]
    [h_tensor_X : RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [h_kflat_tensor_X : HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [h_localization_X : RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [h_kflat_localization_X : DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [h_homotopy_tensor_S : RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      S.toRingedSpace]
    [h_tensor_S : RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [h_kflat_tensor_S : HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [h_localization_S : RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [h_kflat_localization_S : DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)] :
    source f E G ⟶ target f E G where
  app :=
    { app := fun F ↦
        let F₀ : RingedSpace.ModuleDerived S.toRingedSpace :=
          (DerivedCategory.singleFunctor (RingedSpace.Modules S.toRingedSpace) 0).obj F
        let QG : RingedSpace.ModuleDerived X.toRingedSpace := DerivedCategory.Q.obj G
        let fF : RingedSpace.ModuleDerived X.toRingedSpace :=
          (RingedSpace.modulePullbackDerived f.toShHom).obj F₀
        let QGF : RingedSpace.ModuleDerived X.toRingedSpace :=
          DerivedCategory.Q.obj (coefficientComplex f G F)
        (RingedSpace.Module.Derived.GlobalSections.toAbelian S.toRingedSpace).map
            ((@DerivedTensor.Right.Monoidal.Model.objIsoTensor
                (RingedSpace.Modules S.toRingedSpace) _ _ _ _ _ _
                (RingedSpace.ModuleDerived.monoidalCategory S.toRingedSpace)
                (@kFlatTensorModel S (hasKFlatResolutions S) h_homotopy_tensor_S h_tensor_S
                  h_kflat_tensor_S
                  h_localization_S h_kflat_localization_S
                  (homotopyLocalization_isLocalization S) :
                    DerivedTensor.Right.Monoidal.Model
                      (C := RingedSpace.Modules S.toRingedSpace))
                F₀ (kernel f E G) _).hom ≫
              ((RingedSpace.ModuleDerived.symmetricCategory S.toRingedSpace).toBraidedCategory.braiding
                F₀ (kernel f E G)).hom ≫
              RingedSpace.ModuleDerived.ProjectionFormula.leftMate f.toShHom
                (DerivedTensor.Right.obj E QG) F₀ ≫
              (RingedSpace.moduleDerivedPushforward f.toShHom).map
                ((((@DerivedTensor.Right.Monoidal.Model.objIsoTensor
                    (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _
                    (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace)
                    (@kFlatTensorModel X (hasKFlatResolutions X) h_homotopy_tensor_X h_tensor_X
                      h_kflat_tensor_X
                      h_localization_X h_kflat_localization_X
                      (homotopyLocalization_isLocalization X) :
                        DerivedTensor.Right.Monoidal.Model
                          (C := RingedSpace.Modules X.toRingedSpace)) E QG _).hom ⊗ₘ 𝟙 fF) ≫
                    (α_ E QG fF).hom) ≫
                  (𝟙 E ⊗ₘ (@DerivedTensor.Right.Monoidal.Model.objIsoTensor
                    (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _
                    (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace)
                    (@kFlatTensorModel X (hasKFlatResolutions X) h_homotopy_tensor_X h_tensor_X
                      h_kflat_tensor_X
                      h_localization_X h_kflat_localization_X
                      (homotopyLocalization_isLocalization X) :
                        DerivedTensor.Right.Monoidal.Model
                          (C := RingedSpace.Modules X.toRingedSpace)) QG fF _).inv) ≫
                  (𝟙 E ⊗ₘ coefficientComparison f G F) ≫
                  ((RingedSpace.ModuleDerived.symmetricCategory
                    X.toRingedSpace).toBraidedCategory.braiding E QGF).hom ≫
                  (@DerivedTensor.Right.Monoidal.Model.objIsoTensor
                    (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _
                    (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace)
                    (@kFlatTensorModel X (hasKFlatResolutions X) h_homotopy_tensor_X h_tensor_X
                      h_kflat_tensor_X
                      h_localization_X h_kflat_localization_X
                      (homotopyLocalization_isLocalization X) :
                        DerivedTensor.Right.Monoidal.Model
                          (C := RingedSpace.Modules X.toRingedSpace)) QGF E _).inv)) ≫
          (pushforwardToAbelianComparison f).app (DerivedTensor.Right.obj QGF E)
      naturality := fun _ _ _ ↦ sorry }
  comm := fun _ _ ↦ sorry

/-- The canonical comparison agrees with every resolution-dependent presentation. -/
theorem comparison_eq_comparisonWithResolutions {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (P_X : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules X.toRingedSpace))
    (P_S : HomotopyCategory.KFlat.ResolutionFunctor
      (RingedSpace.Modules S.toRingedSpace)) :
    comparison f E G = comparisonWithResolutions f E G P_X P_S := sorry

/-- The component at `F` of the canonical projection-formula comparison. -/
noncomputable def comparisonApp {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (F : S.Modules) :
    (source f E G).obj F ⟶ (target f E G).obj F :=
  (comparison f E G).app.app F

/-- Evaluation of the canonical bundled comparison gives its named component. -/
theorem comparison_app {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (F : S.Modules) :
    (comparison f E G).app.app F = comparisonApp f E G F := sorry

/-- The canonical comparison components are natural in the coefficient module. -/
theorem comparisonApp_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    {F F' : S.Modules} (φ : F ⟶ F') :
    (source f E G).map φ ≫ comparisonApp f E G F' =
      comparisonApp f E G F ≫ (target f E G).map φ := sorry

/-- The canonical comparison components commute with connecting morphisms. -/
theorem comparisonApp_boundary {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends
      (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization
      (C := RingedSpace.Modules S.toRingedSpace)]
    [DerivedTensor.Right.Has (C := RingedSpace.Modules S.toRingedSpace)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    {T : ShortComplex S.Modules} (hT : T.ShortExact) :
    CommSq (comparisonApp f E G T.X₃)
      ((source f E G).δ hT) ((target f E G).δ hT)
      ((comparisonApp f E G T.X₁)⟦(1 : ℤ)⟧') := sorry

/-- The degree-`i` map induced by a boundary-compatible comparison of the source and target
delta functors. -/
noncomputable def cohomologyMap {S : Scheme.{u}}
    {D₁ D₂ : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})}
    (c : D₁ ⟶ D₂) (F : S.Modules) (i : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        (D₁.obj F) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        (D₂.obj F) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map (c.app.app F)

/-- `cohomologyMap` is obtained by applying degree-`i` homology to the comparison component. -/
theorem cohomologyMap_def {S : Scheme.{u}}
    {D₁ D₂ : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})}
    (c : D₁ ⟶ D₂) (F : S.Modules) (i : ℤ) :
    cohomologyMap c F i =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map (c.app.app F) := sorry

/-- The cohomology comparison is natural in the coefficient module. -/
theorem cohomologyMap_naturality {S : Scheme.{u}}
    {D₁ D₂ : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})}
    (c : D₁ ⟶ D₂) {F F' : S.Modules}
    (φ : F ⟶ F') (i : ℤ) :
    CommSq
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        (D₁.map φ))
      (cohomologyMap c F i) (cohomologyMap c F' i)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        (D₂.map φ)) := sorry

/-- The boundary morphism from degree `i` on the third object to degree `i + 1` on the first. -/
noncomputable def boundaryMap {S : Scheme.{u}} (D : DeltaFunctor S.Modules
    (DerivedCategory AddCommGrpCat.{u})) {T : ShortComplex S.Modules}
    (hT : T.ShortExact) (i : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj (D.obj T.X₃) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i + 1)).obj (D.obj T.X₁) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map (D.δ hT) ≫
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftIso
      (1 : ℤ) i (i + 1) (add_comm 1 i)).hom.app (D.obj T.X₁)

/-- The boundary map is homology applied to the delta-functor connecting morphism. -/
theorem boundaryMap_def {S : Scheme.{u}} (D : DeltaFunctor S.Modules
    (DerivedCategory AddCommGrpCat.{u})) {T : ShortComplex S.Modules}
    (hT : T.ShortExact) (i : ℤ) :
    boundaryMap D hT i =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map (D.δ hT) ≫
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftIso
          (1 : ℤ) i (i + 1) (add_comm 1 i)).hom.app (D.obj T.X₁) := sorry

/-- A comparison of the source and target delta functors commutes with the connecting maps
from degree `i` to degree `i + 1`. -/
theorem cohomologyMap_boundary
    {S : Scheme.{u}}
    {D₁ D₂ : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})}
    (c : D₁ ⟶ D₂)
    (T : ShortComplex S.Modules) (hT : T.ShortExact) (i : ℤ) :
    CommSq (cohomologyMap c T.X₃ i)
      (boundaryMap D₁ hT i)
      (boundaryMap D₂ hT i)
      (cohomologyMap c T.X₁ (i + 1)) := sorry

/-- Under the standard finiteness, perfectness, flatness, and proper-support hypotheses, the
canonical boundary-compatible projection-formula comparison induces an isomorphism on every
cohomology group with quasicoherent coefficients. -/
theorem cohomologyComparison_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (G : CochainComplex X.Modules ℤ)
    (hG_bounded : CochainComplex.bounded X.Modules G)
    [∀ n : ℤ, (G.X n).IsCoherent]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f
      (RingedSpace.ModuleDerived.cohomologySheaf (DerivedCategory.Q.obj G) n)]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (F : S.Modules) [F.IsQuasicoherent] (i : ℤ) :
    IsIso (cohomologyMap (comparison f E G) F i) := sorry

end ProjectionFormula
end ModuleDerived
end Scheme
end AlgebraicGeometry
