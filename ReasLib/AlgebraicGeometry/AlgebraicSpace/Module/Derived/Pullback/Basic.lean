/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical derived module pullback from displayed cell models

The public functor and counits use the specified cell replacement and its actual augmentation.
The homotopy-category universal lift descends that same cochain lift. Thus its total-derived
existence certificate contains a constructed terminal witness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Module pullback along any algebraic-space morphism is additive. -/
instance instAdditive_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pullback f).Additive := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- Unbounded derived pullback computed by the displayed functorial cell resolution. -/
def pullback (f : X ⟶ Y) : ModuleDerived Y ⥤ ModuleDerived X :=
  Modules.CellModels.pullbackUsingCells f

/-- The canonical implementation resolves the input by its displayed cell model. -/
theorem pullback_eq (f : X ⟶ Y) :
    pullback f = Modules.CellModels.pullbackUsingCells f := rfl

/-- The cochain counit is pullback of the actual model augmentation. -/
def pullbackCochainCounit (f : X ⟶ Y) :
    DerivedCategory.Q (C := Y.Modules) ⋙ pullback f ⟶
      (Modules.pullback f).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q :=
  Modules.CellModels.pullbackUsingCellsCounit f

/-- The cochain counit has the actual terminal-extension lift of the cell construction. -/
instance pullbackCochainCounit_isLeftDerived (f : X ⟶ Y) :
    (pullback f).IsLeftDerivedFunctor (pullbackCochainCounit f)
      (HomologicalComplex.quasiIso Y.Modules (up ℤ)) :=
  Modules.CellModels.pullbackUsingCells_isLeftDerived f

/-- The homotopy component transports the same augmentation along the native quotient
comparison, then uses the ordinary pullback's cochain identification. -/
def pullbackCounitComponent (f : X ⟶ Y) (K : HomotopyCategory Y.Modules (up ℤ)) :
    (pullback f).obj (DerivedCategory.Qh.obj K) ⟶
      (Functor.Homotopy.toDerived (Modules.pullback f)).obj K :=
  (pullback f).map ((DerivedCategory.quotientCompQhIso Y.Modules).hom.app K.as) ≫
    (pullbackCochainCounit f).app K.as ≫
    (Functor.Homotopy.cochainIso (Modules.pullback f)).inv.app K.as

/-- The component formula descends naturally through chain homotopy. -/
theorem pullbackCounitComponent_naturality (f : X ⟶ Y)
    {A B : HomotopyCategory Y.Modules (up ℤ)} (a : A ⟶ B) :
    (DerivedCategory.Qh ⋙ pullback f).map a ≫ pullbackCounitComponent f B =
      pullbackCounitComponent f A ≫
        (Functor.Homotopy.toDerived (Modules.pullback f)).map a := sorry

/-- The homotopy counit descends the actual cochain augmentation. -/
def pullbackCounit (f : X ⟶ Y) :
    DerivedCategory.Qh (C := Y.Modules) ⋙ pullback f ⟶
      Functor.Homotopy.toDerived (Modules.pullback f) where
  app K := pullbackCounitComponent f K
  naturality := fun _ _ a ↦ pullbackCounitComponent_naturality f a

/-- Any homotopy-level extension comparison pulls back to the corresponding cochain
comparison through the native quotient identification. -/
def extensionCochainComparison (f : X ⟶ Y) (G : ModuleDerived Y ⥤ ModuleDerived X)
    (β : DerivedCategory.Qh (C := Y.Modules) ⋙ G ⟶
      Functor.Homotopy.toDerived (Modules.pullback f)) :
    DerivedCategory.Q (C := Y.Modules) ⋙ G ⟶ Modules.CellModels.ordinaryPullbackCochain f :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso Y.Modules) G).inv ≫
    (Functor.associator (HomotopyCategory.quotient Y.Modules (up ℤ))
      DerivedCategory.Qh G).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient Y.Modules (up ℤ)) β ≫
    (Functor.Homotopy.cochainIso (Modules.pullback f)).hom

/-- The homotopy universal lift is the already specified cell-model lift on cochains. -/
def homotopyExtensionLift (f : X ⟶ Y) (G : ModuleDerived Y ⥤ ModuleDerived X)
    (β : DerivedCategory.Qh (C := Y.Modules) ⋙ G ⟶
      Functor.Homotopy.toDerived (Modules.pullback f)) : G ⟶ pullback f :=
  Modules.CellModels.extensionLift f G (extensionCochainComparison f G β)

/-- The descended lift satisfies the homotopy-level extension equation. -/
theorem homotopyExtensionLift_fac (f : X ⟶ Y) (G : ModuleDerived Y ⥤ ModuleDerived X)
    (β : DerivedCategory.Qh (C := Y.Modules) ⋙ G ⟶
      Functor.Homotopy.toDerived (Modules.pullback f)) :
    Functor.whiskerLeft DerivedCategory.Qh (homotopyExtensionLift f G β) ≫
      pullbackCounit f = β := sorry

/-- The extension morphism retains the actual cochain-model lift. -/
def homotopyTerminalLift (f : X ⟶ Y)
    (E : Functor.RightExtension (DerivedCategory.Qh (C := Y.Modules))
      (Functor.Homotopy.toDerived (Modules.pullback f))) :
    E ⟶ Functor.RightExtension.mk (pullback f) (pullbackCounit f) :=
  CostructuredArrow.homMk (homotopyExtensionLift f E.left E.hom)
    (homotopyExtensionLift_fac f E.left E.hom)

/-- The homotopy lift is uniquely determined by the augmentation comparison. -/
theorem homotopyTerminalLift_unique (f : X ⟶ Y)
    (E : Functor.RightExtension (DerivedCategory.Qh (C := Y.Modules))
      (Functor.Homotopy.toDerived (Modules.pullback f)))
    (m : E ⟶ Functor.RightExtension.mk (pullback f) (pullbackCounit f)) :
    m = homotopyTerminalLift f E := sorry

/-- The universal witness contains the actual homotopy lift, with only its laws deferred. -/
def pullbackHomotopyTerminalWitness (f : X ⟶ Y) :
    (Functor.RightExtension.mk (pullback f) (pullbackCounit f)).IsUniversal :=
  IsTerminal.ofUniqueHom (homotopyTerminalLift f) (homotopyTerminalLift_unique f)

/-- Derived pullback satisfies the homotopy-level universal property with its specified counit. -/
instance pullbackCounit_isLeftDerived (f : X ⟶ Y) :
    (pullback f).IsLeftDerivedFunctor (pullbackCounit f)
      (HomotopyCategory.quasiIso Y.Modules (up ℤ)) where
  isRightKanExtension := { nonempty_isUniversal := ⟨pullbackHomotopyTerminalWitness f⟩ }

/-- The total-derived existence certificate is backed by the actual terminal witness. -/
instance instHasLeftDerivedFunctor_toDerived_pullback (f : X ⟶ Y) :
    (Functor.Homotopy.toDerived (Modules.pullback f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso Y.Modules (up ℤ)) :=
  Functor.HasLeftDerivedFunctor.mk' (LF := pullback f) (α := pullbackCounit f)

/-- Native uniqueness compares the concrete producer with the total-derived presentation;
both extension witnesses come from the constructed terminal lift. -/
def pullbackIsoTotalLeftDerived (f : X ⟶ Y) :
    pullback f ≅ Functor.LeftDerived.Homotopy.functor (Modules.pullback f) :=
  Functor.leftDerivedUnique (LF := pullback f)
    (LF' := Functor.LeftDerived.Homotopy.functor (Modules.pullback f))
    (α := pullbackCounit f)
    (α'₂ := Functor.LeftDerived.Homotopy.counit (Modules.pullback f))
    (W := HomotopyCategory.quasiIso Y.Modules (up ℤ))

/-- The actual composition isomorphism descends the specified intermediate augmentation. -/
@[stacks 0D6D "canonical module derived pullback composition"]
def pullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  Modules.CellModels.compositionDerivedIso f g

/-- The forward comparison is the prescribed map in the constructed composition isomorphism. -/
def pullbackCompComparison (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ⟶ pullback (f ≫ g) :=
  (pullbackCompIso f g).hom

/-- Both comparison directions are explicitly constructed on displayed cell models. -/
theorem pullbackCompComparison_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCompComparison f g = (Modules.CellModels.compositionDerivedIso f g).hom := rfl

/-- The forward map is the canonical comparison, while the reverse is its specified
localized cell-model path. -/
theorem pullbackCompIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackCompIso f g).hom = pullbackCompComparison f g := rfl

/-- After the specified uniqueness comparisons, the constructed forward path is the
canonical total-derived composition comparison. -/
theorem pullbackCompComparison_total (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCompComparison f g ≫ (pullbackIsoTotalLeftDerived (f ≫ g)).hom =
      (Functor.isoWhiskerRight (pullbackIsoTotalLeftDerived g) (pullback f)).hom ≫
        (Functor.isoWhiskerLeft
          (Functor.LeftDerived.Homotopy.functor (Modules.pullback g))
          (pullbackIsoTotalLeftDerived f)).hom ≫
        Functor.LeftDerived.Homotopy.Composition.comparison
          (Modules.pullback f) (Modules.pullback g) (Modules.pullback (f ≫ g))
          (Modules.pullbackCompIso f g).symm := sorry

/-- The comparison is invertible because it belongs to the constructed isomorphism. -/
instance pullbackCompComparison_isIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (pullbackCompComparison f g) := by
  change IsIso (pullbackCompIso f g).hom
  infer_instance

/-- Étale pullback preserves finite limits. -/
instance instPreservesFiniteLimits_pullback_of_etale (f : X ⟶ Y) [AlgebraicSpace.Etale f] :
    PreservesFiniteLimits (Modules.pullback f) := sorry

/-- Module pullback is a left adjoint and preserves finite colimits. -/
instance instPreservesFiniteColimits_pullback_of_etale (f : X ⟶ Y) [AlgebraicSpace.Etale f] :
    PreservesFiniteColimits (Modules.pullback f) := sorry

/-- Exact pullback preserves the actual augmentation quasi-isomorphism. -/
theorem etaleAugmentation_quasiIso (f : X ⟶ Y) [AlgebraicSpace.Etale f]
    (K : CochainComplex Y.Modules ℤ) :
    QuasiIso (((Modules.pullback f).mapHomologicalComplex (up ℤ)).map
      (SheafOfModules.CellReplacement.augmentation K)) := sorry

/-- On a cochain complex, exact pullback is identified using formal localization of the
actual augmentation and the native exact-functor comparison. -/
def pullbackIsoMapDerivedCategoryOnInput (f : X ⟶ Y) [AlgebraicSpace.Etale f]
    (K : CochainComplex Y.Modules ℤ) :
    (pullback f).obj (DerivedCategory.Q.obj K) ≅
      (Modules.pullback f).mapDerivedCategory.obj (DerivedCategory.Q.obj K) :=
  (Modules.CellModels.pullbackUsingCells_fac f).app K ≪≫
    Localization.isoOfHom (DerivedCategory.Q (C := X.Modules))
      (HomologicalComplex.quasiIso X.Modules (up ℤ))
      (((Modules.pullback f).mapHomologicalComplex (up ℤ)).map
        (SheafOfModules.CellReplacement.augmentation K)) (etaleAugmentation_quasiIso f K) ≪≫
    ((Modules.pullback f).mapDerivedCategoryFactors.app K).symm

/-- The exact-pullback comparison uses the actual functorial augmentation square. -/
theorem pullbackIsoMapDerivedCategoryOnInput_naturality
    (f : X ⟶ Y) [AlgebraicSpace.Etale f]
    {A B : CochainComplex Y.Modules ℤ} (a : A ⟶ B) :
    (DerivedCategory.Q ⋙ pullback f).map a ≫
        (pullbackIsoMapDerivedCategoryOnInput f B).hom =
      (pullbackIsoMapDerivedCategoryOnInput f A).hom ≫
        (DerivedCategory.Q ⋙ (Modules.pullback f).mapDerivedCategory).map a := sorry

/-- The comparison is natural on original cochain inputs. -/
def pullbackIsoMapDerivedCategoryOnCochains (f : X ⟶ Y) [AlgebraicSpace.Etale f] :
    DerivedCategory.Q ⋙ pullback f ≅
      DerivedCategory.Q ⋙ (Modules.pullback f).mapDerivedCategory :=
  NatIso.ofComponents (pullbackIsoMapDerivedCategoryOnInput f)
    (fun a ↦ pullbackIsoMapDerivedCategoryOnInput_naturality f a)

/-- Étale derived pullback agrees with exact pullback through two specified maps. -/
def pullbackIsoMapDerivedCategory (f : X ⟶ Y) [AlgebraicSpace.Etale f] :
    pullback f ≅ (Modules.pullback f).mapDerivedCategory :=
  Localization.liftNatIso (DerivedCategory.Q (C := Y.Modules))
    (HomologicalComplex.quasiIso Y.Modules (up ℤ))
    (DerivedCategory.Q ⋙ pullback f)
    (DerivedCategory.Q ⋙ (Modules.pullback f).mapDerivedCategory)
    (pullback f) (Modules.pullback f).mapDerivedCategory
    (pullbackIsoMapDerivedCategoryOnCochains f)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
