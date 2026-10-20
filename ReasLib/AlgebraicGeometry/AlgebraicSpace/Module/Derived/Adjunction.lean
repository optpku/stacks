/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction

/-! # Unbounded derived pullback-pushforward adjunction on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

private def pullbackPushforwardLiftComponent {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (E : Functor.RightExtension (DerivedCategory.Qh (C := X.Modules))
      ((Functor.Homotopy.toDerived (Modules.pullback f)) ⋙
        Modules.moduleDerivedPushforward f))
    (A : CochainComplex X.Modules ℤ) :
    E.left.obj (DerivedCategory.Q.obj A) ⟶
      (Functor.LeftDerived.Homotopy.functor (Modules.pullback f) ⋙
        Modules.moduleDerivedPushforward f).obj (DerivedCategory.Q.obj A) :=
  E.left.map ((Modules.CellModels.inputAugmentationIso A).inv ≫
      (DerivedCategory.quotientCompQhIso X.Modules).inv.app
        (SheafOfModules.CellReplacement.model A)) ≫
    E.hom.app ((HomotopyCategory.quotient X.Modules (up ℤ)).obj
      (SheafOfModules.CellReplacement.model A)) ≫
    (Modules.moduleDerivedPushforward f).map
      ((Functor.Homotopy.cochainIso (Modules.pullback f)).hom.app
          (SheafOfModules.CellReplacement.model A) ≫
        ((Modules.CellModels.pullbackUsingCells_fac f).app A).inv ≫
        (ModuleDerived.pullbackIsoTotalLeftDerived f).hom.app (DerivedCategory.Q.obj A))

private def pushforwardPullbackDescComponent {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (E : Functor.LeftExtension (DerivedCategory.Qh (C := Y.Modules))
      ((Functor.Homotopy.toDerived (Modules.pushforward f)) ⋙
        Functor.LeftDerived.Homotopy.functor (Modules.pullback f)))
    (A : CochainComplex Y.Modules ℤ) :
    (Modules.moduleDerivedPushforward f ⋙
      Functor.LeftDerived.Homotopy.functor (Modules.pullback f)).obj
        (DerivedCategory.Q.obj A) ⟶ E.right.obj (DerivedCategory.Q.obj A) :=
  (Functor.LeftDerived.Homotopy.functor (Modules.pullback f)).map
      ((@Functor.KInjectiveModel.isoOfModel.{u} _ _ _ _ _ _ _ _ _
          (Modules.pushforward f) _ (Modules.moduleDerivedPushforward f)
          (Modules.moduleDerivedPushforward.unit f)
          (Modules.moduleDerivedPushforward.isRightDerived f)).inv.app (DerivedCategory.Q.obj A) ≫
        (Functor.KInjectiveModel.fac.{u} (Modules.pushforward f)).hom.app A ≫
        (Functor.Homotopy.cochainIso (Modules.pushforward f)).inv.app
          ((CochainComplex.KInjectiveResolution.Construction.replacement.{u} Y.Modules).obj A)) ≫
    E.hom.app ((HomotopyCategory.quotient Y.Modules (up ℤ)).obj
      ((CochainComplex.KInjectiveResolution.Construction.replacement.{u} Y.Modules).obj A)) ≫
    E.right.map ((DerivedCategory.quotientCompQhIso Y.Modules).hom.app
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{u} Y.Modules).obj A) ≫
      (Functor.KInjectiveModel.inputAugmentationIso.{u} A).inv)

/-- Homotopy-level module pullback and pushforward form an absolute derived pair:
their total derived functors retain the two composite universal properties. -/
instance modulePullbackPushforwardHasPair {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    @Adjunction.TotalDerived.HasPair _ _ _ _ _ _ _ _
      ((Modules.pullback f).mapHomotopyCategory (up ℤ))
      ((Modules.pushforward f).mapHomotopyCategory (up ℤ))
      (HomotopyCategory.quasiIso X.Modules (up ℤ))
      (HomotopyCategory.quasiIso Y.Modules (up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh inferInstance inferInstance
      (ModuleDerived.instHasLeftDerivedFunctor_toDerived_pullback f)
      (Functor.RightDerived.KInjective.hasDerived (Modules.pushforward f)) := by
  let LG := Functor.LeftDerived.Homotopy.functor (Modules.pullback f)
  let RF := Modules.moduleDerivedPushforward f
  let QX := DerivedCategory.Qh (C := X.Modules)
  let QY := DerivedCategory.Qh (C := Y.Modules)
  let leftComparison : QX ⋙ (LG ⋙ RF) ⟶
      Functor.Homotopy.toDerived (Modules.pullback f) ⋙ RF :=
    (Functor.associator QX LG RF).inv ≫
      Functor.whiskerRight (Functor.LeftDerived.Homotopy.counit (Modules.pullback f)) RF
  let rightComparison : Functor.Homotopy.toDerived (Modules.pushforward f) ⋙ LG ⟶
      QY ⋙ (RF ⋙ LG) :=
    Functor.whiskerRight (Functor.RightDerived.Homotopy.unit (Modules.pushforward f)) LG ≫
      (Functor.associator QY RF LG).hom
  let leftExtension := Functor.RightExtension QX
    (Functor.Homotopy.toDerived (Modules.pullback f) ⋙ RF)
  let rightExtension := Functor.LeftExtension QY
    (Functor.Homotopy.toDerived (Modules.pushforward f) ⋙ LG)
  let leftNatural (E : leftExtension) : Prop :=
    ∀ {A B : CochainComplex X.Modules ℤ} (a : A ⟶ B),
      (DerivedCategory.Q ⋙ E.left).map a ≫ pullbackPushforwardLiftComponent f E B =
        pullbackPushforwardLiftComponent f E A ≫ (DerivedCategory.Q ⋙ (LG ⋙ RF)).map a
  let rightNatural (E : rightExtension) : Prop :=
    ∀ {A B : CochainComplex Y.Modules ℤ} (a : A ⟶ B),
      (DerivedCategory.Q ⋙ (RF ⋙ LG)).map a ≫ pushforwardPullbackDescComponent f E B =
        pushforwardPullbackDescComponent f E A ≫ (DerivedCategory.Q ⋙ E.right).map a
  let leftLift (E : leftExtension) (h : leftNatural E) : E.left ⟶ LG ⋙ RF :=
    Localization.liftNatTrans (DerivedCategory.Q (C := X.Modules))
      (HomologicalComplex.quasiIso X.Modules (up ℤ))
      (DerivedCategory.Q ⋙ E.left) (DerivedCategory.Q ⋙ (LG ⋙ RF)) E.left (LG ⋙ RF)
      { app := pullbackPushforwardLiftComponent f E, naturality := fun _ _ a ↦ h a }
  let rightDesc (E : rightExtension) (h : rightNatural E) : RF ⋙ LG ⟶ E.right :=
    Localization.liftNatTrans (DerivedCategory.Q (C := Y.Modules))
      (HomologicalComplex.quasiIso Y.Modules (up ℤ))
      (DerivedCategory.Q ⋙ (RF ⋙ LG)) (DerivedCategory.Q ⋙ E.right) (RF ⋙ LG) E.right
      { app := pushforwardPullbackDescComponent f E, naturality := fun _ _ a ↦ h a }
  have laws :
      (∀ E, leftNatural E) ∧
      (∀ E, rightNatural E) ∧
      (∀ E h, Functor.whiskerLeft QX (leftLift E h) ≫ leftComparison = E.hom) ∧
      (∀ E h, rightComparison ≫ Functor.whiskerLeft QY (rightDesc E h) = E.hom) ∧
      (∀ E h (m : E.left ⟶ LG ⋙ RF),
        Functor.whiskerLeft QX m ≫ leftComparison = E.hom → m = leftLift E h) ∧
      (∀ E h (m : RF ⋙ LG ⟶ E.right),
        rightComparison ≫ Functor.whiskerLeft QY m = E.hom → m = rightDesc E h) := by
    sorry
  let leftWitness : (Functor.RightExtension.mk (LG ⋙ RF) leftComparison).IsUniversal :=
    IsTerminal.ofUniqueHom
      (fun E ↦ CostructuredArrow.homMk (leftLift E (laws.1 E)) (laws.2.2.1 E _))
      (fun E m ↦ CostructuredArrow.hom_ext _ _
        (laws.2.2.2.2.1 E _ m.left (CostructuredArrow.w m)))
  let rightWitness : (Functor.LeftExtension.mk (RF ⋙ LG) rightComparison).IsUniversal :=
    IsInitial.ofUniqueHom
      (fun E ↦ StructuredArrow.homMk (rightDesc E (laws.2.1 E)) (laws.2.2.2.1 E _))
      (fun E m ↦ StructuredArrow.hom_ext _ _
        (laws.2.2.2.2.2 E _ m.right (StructuredArrow.w m)))
  exact @Adjunction.TotalDerived.HasPair.mk _ _ _ _ _ _ _ _
    ((Modules.pullback f).mapHomotopyCategory (up ℤ))
    ((Modules.pushforward f).mapHomotopyCategory (up ℤ))
    (HomotopyCategory.quasiIso X.Modules (up ℤ))
    (HomotopyCategory.quasiIso Y.Modules (up ℤ)) QX QY inferInstance inferInstance
    (ModuleDerived.instHasLeftDerivedFunctor_toDerived_pullback f)
    (Functor.RightDerived.KInjective.hasDerived (Modules.pushforward f))
    { isRightKanExtension := { nonempty_isUniversal := ⟨leftWitness⟩ } }
    { isLeftKanExtension := { nonempty_isUniversal := ⟨rightWitness⟩ } }

/-- Unbounded derived module pullback is left adjoint to derived module pushforward. -/
def Modules.derivedPullbackPushforwardAdjunction {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    Functor.LeftDerived.Homotopy.functor (Modules.pullback f) ⊣
      Modules.moduleDerivedPushforward f :=
  @Adjunction.TotalDerived.HasPair.derived _ _ _ _ _ _ _ _
    ((Modules.pullback f).mapHomotopyCategory (up ℤ))
    ((Modules.pushforward f).mapHomotopyCategory (up ℤ))
    (Adjunction.mapHomotopyCategoryAdjunction (Modules.pullbackPushforwardAdjunction f))
    (HomotopyCategory.quasiIso X.Modules (up ℤ))
    (HomotopyCategory.quasiIso Y.Modules (up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh inferInstance inferInstance
    (ModuleDerived.instHasLeftDerivedFunctor_toDerived_pullback f)
    (Functor.RightDerived.KInjective.hasDerived (Modules.pushforward f))
    (modulePullbackPushforwardHasPair f)

/-- The derived module adjunction is obtained by deriving the homotopy-level adjunction. -/
theorem modulePullbackDerivedPushforwardAdjunction_eq {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    Modules.derivedPullbackPushforwardAdjunction f =
      @Adjunction.TotalDerived.HasPair.derived _ _ _ _ _ _ _ _
        ((Modules.pullback f).mapHomotopyCategory (up ℤ))
        ((Modules.pushforward f).mapHomotopyCategory (up ℤ))
        (Adjunction.mapHomotopyCategoryAdjunction (Modules.pullbackPushforwardAdjunction f))
        (HomotopyCategory.quasiIso X.Modules (up ℤ))
        (HomotopyCategory.quasiIso Y.Modules (up ℤ))
        DerivedCategory.Qh DerivedCategory.Qh inferInstance inferInstance
        (ModuleDerived.instHasLeftDerivedFunctor_toDerived_pullback f)
        (Functor.RightDerived.KInjective.hasDerived (Modules.pushforward f))
        (modulePullbackPushforwardHasPair f) := rfl

/-- Concrete unbounded derived module pullback is left adjoint to derived module pushforward. -/
def derivedPullbackPushforwardAdjunction {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (φ : Y ⟶ X) :
    ModuleDerived.pullback φ ⊣ Modules.moduleDerivedPushforward φ :=
  (Modules.derivedPullbackPushforwardAdjunction φ).ofNatIsoLeft
    (ModuleDerived.pullbackIsoTotalLeftDerived φ).symm

/-- The concrete derived adjunction is transported from the total-derived adjunction
along the canonical comparison with concrete derived pullback. -/
theorem derivedPullbackPushforwardAdjunction_eq {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (φ : Y ⟶ X) :
    derivedPullbackPushforwardAdjunction φ =
      (Modules.derivedPullbackPushforwardAdjunction φ).ofNatIsoLeft
        (ModuleDerived.pullbackIsoTotalLeftDerived φ).symm := sorry

end AlgebraicGeometry.AlgebraicSpace
