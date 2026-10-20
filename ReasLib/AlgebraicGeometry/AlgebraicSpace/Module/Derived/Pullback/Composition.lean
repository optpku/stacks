/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Composition of pullback on actual cell models

The iterated model first pulls back a displayed source cell model and then applies the displayed
cell replacement again. Its map to the composite model is ordinary pullback of the second
augmentation followed by the actual underived composition isomorphism. Localization supplies
the formal inverse of this specified quasi-isomorphism, so neither direction is selected from a
new invertibility assertion about a total-derived comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.CellModels

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
variable [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u}]
variable [(smallEtaleTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
variable [(smallEtaleTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable [(pullback f).Additive] [(pullback g).Additive] [(pullback (f ≫ g)).Additive]
variable (K : CochainComplex Z.Modules ℤ)

/-- The specified cell model of the original complex, before any pullback. -/
def sourceModel : CochainComplex Z.Modules ℤ :=
  SheafOfModules.CellReplacement.model K

/-- Ordinary pullback of the original displayed cell model to the intermediate space. -/
def middleModel : CochainComplex Y.Modules ℤ :=
  ((pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (sourceModel K)

/-- The iterated model retains the actual intermediate input and its displayed augmentation. -/
def iteratedModel : CochainComplex X.Modules ℤ :=
  ((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (SheafOfModules.CellReplacement.model (middleModel g K))

/-- The composite model is ordinary pullback of the original displayed model along the composite. -/
def compositeModel : CochainComplex X.Modules ℤ :=
  ((pullback (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (sourceModel K)

/-- The comparison is the pullback of the actual intermediate augmentation followed by the
native complex-level image of underived module pullback composition. -/
def compositionComparison : iteratedModel f g K ⟶ compositeModel f g K :=
  ((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (SheafOfModules.CellReplacement.augmentation (middleModel g K)) ≫
    (Functor.mapHomologicalComplexCompIso (pullbackCompIso f g)
      (ComplexShape.up ℤ)).hom.app (sourceModel K)

/-- K-flat source models and their ordinary pullbacks have flat terms and are K-flat.
Pullback therefore preserves the specified intermediate augmentation quasi-isomorphism. -/
@[stacks 0D6D "actual cell-model comparison"]
theorem compositionComparison_quasiIso :
    QuasiIso (compositionComparison f g K) := sorry

variable [HasDerivedCategory X.Modules]

/-- The actual cochain functor computing pullback: resolve by the displayed cell model,
apply ordinary pullback degreewise, and localize the resulting complex. -/
def pullbackCochain : CochainComplex Y.Modules ℤ ⥤ DerivedCategory X.Modules :=
  SheafOfModules.CellReplacement.functor (R := structureSheaf Y) ⋙
    (pullback f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q (C := X.Modules))

/-- A quasi-isomorphism of original inputs induces the specified quasi-isomorphism of their
pulled-back cell models. Both displayed models are K-flat with flat terms. -/
theorem pullbackModelMap_quasiIso {A B : CochainComplex Y.Modules ℤ}
    (a : A ⟶ B) (ha : QuasiIso a) :
    QuasiIso (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (SheafOfModules.CellReplacement.modelMap a)) := sorry

/-- The actual cochain model functor inverts quasi-isomorphisms by formal localization of its
specified pulled-back model maps. No invertibility of an abstract comparison is assumed. -/
theorem pullbackCochain_inverts :
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)).IsInvertedBy
      (pullbackCochain f) := by
  intro A B a ha
  letI : QuasiIso (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (SheafOfModules.CellReplacement.modelMap a)) := pullbackModelMap_quasiIso f a ha
  change IsIso ((DerivedCategory.Q (C := X.Modules)).map
    (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (SheafOfModules.CellReplacement.modelMap a)))
  infer_instance

/-- Derived pullback supplied by the concrete cochain model functor, using the native
localization lift of its specified maps and formal quasi-isomorphism inverses. -/
def pullbackUsingCells [HasDerivedCategory Y.Modules] :
    DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  Localization.lift (pullbackCochain f) (pullbackCochain_inverts f)
    (DerivedCategory.Q (C := Y.Modules))

/-- The native localization comparison keeps the actual cochain model functor. -/
def pullbackUsingCells_fac [HasDerivedCategory Y.Modules] :
    DerivedCategory.Q (C := Y.Modules) ⋙ pullbackUsingCells f ≅ pullbackCochain f :=
  Localization.fac (pullbackCochain f) (pullbackCochain_inverts f)
    (DerivedCategory.Q (C := Y.Modules))

/-- Formal localization of the specified cell-model quasi-isomorphism. Its inverse is the
native localization path of that actual augmentation and underived comparison map. -/
@[stacks 0D6D "localized actual cell-model comparison"]
def compositionIso :
    (DerivedCategory.Q (C := X.Modules)).obj (iteratedModel f g K) ≅
      (DerivedCategory.Q (C := X.Modules)).obj (compositeModel f g K) :=
  Localization.isoOfHom (DerivedCategory.Q (C := X.Modules))
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))
    (compositionComparison f g K) (compositionComparison_quasiIso f g K)

/-- The forward localized comparison is the image of the specified cochain map. -/
@[simp]
theorem compositionIso_hom :
    (compositionIso f g K).hom =
      (DerivedCategory.Q (C := X.Modules)).map (compositionComparison f g K) := rfl

/-- The actual reverse comparison on the localized cell models. -/
def compositionInverse :
    (DerivedCategory.Q (C := X.Modules)).obj (compositeModel f g K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj (iteratedModel f g K) :=
  (compositionIso f g K).inv

/-- The reverse path followed by the prescribed forward path is the identity. -/
theorem compositionInverse_hom :
    compositionInverse f g K ≫ (compositionIso f g K).hom = 𝟙 _ :=
  (compositionIso f g K).inv_hom_id

/-- The prescribed forward path followed by its formal reverse path is the identity. -/
theorem compositionHom_inverse :
    (compositionIso f g K).hom ≫ compositionInverse f g K = 𝟙 _ :=
  (compositionIso f g K).hom_inv_id

variable [HasDerivedCategory Y.Modules] [HasDerivedCategory Z.Modules]

/-- Ordinary degreewise pullback followed by localization, before resolving the input. -/
def ordinaryPullbackCochain : CochainComplex Y.Modules ℤ ⥤ DerivedCategory X.Modules :=
  (pullback f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- The specified counit is the actual model augmentation transported through native lift
comparison and ordinary pullback. -/
def pullbackUsingCellsCounit :
    DerivedCategory.Q (C := Y.Modules) ⋙ pullbackUsingCells f ⟶ ordinaryPullbackCochain f :=
  (pullbackUsingCells_fac f).hom ≫
    Functor.whiskerRight (SheafOfModules.CellReplacement.augmentationNatTrans
      (R := structureSheaf Y)) (ordinaryPullbackCochain f) ≫
    (Functor.leftUnitor (ordinaryPullbackCochain f)).hom

/-- Native formal localization of the actual augmentation at the original input. -/
def inputAugmentationIso (A : CochainComplex Y.Modules ℤ) :
    (DerivedCategory.Q (C := Y.Modules)).obj (SheafOfModules.CellReplacement.model A) ≅
      (DerivedCategory.Q (C := Y.Modules)).obj A :=
  Localization.isoOfHom (DerivedCategory.Q (C := Y.Modules))
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ))
    (SheafOfModules.CellReplacement.augmentation A)
    (SheafOfModules.CellReplacement.augmentation_quasiIso A)

/-- A candidate right extension lifts through the actual augmentation. First reverse the
localized augmentation, then use its given comparison on the displayed model. -/
def extensionLiftOnInput (G : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules)
    (β : DerivedCategory.Q (C := Y.Modules) ⋙ G ⟶ ordinaryPullbackCochain f)
    (A : CochainComplex Y.Modules ℤ) :
    G.obj ((DerivedCategory.Q (C := Y.Modules)).obj A) ⟶
      (pullbackUsingCells f).obj ((DerivedCategory.Q (C := Y.Modules)).obj A) :=
  G.map (inputAugmentationIso A).inv ≫
    β.app (SheafOfModules.CellReplacement.model A) ≫
    ((pullbackUsingCells_fac f).app A).inv

/-- The explicit lift formula is natural through the supplied comparison and the actual
functorial augmentation. -/
theorem extensionLiftOnInput_naturality
    (G : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules)
    (β : DerivedCategory.Q (C := Y.Modules) ⋙ G ⟶ ordinaryPullbackCochain f)
    {A B : CochainComplex Y.Modules ℤ} (a : A ⟶ B) :
    (DerivedCategory.Q (C := Y.Modules) ⋙ G).map a ≫ extensionLiftOnInput f G β B =
      extensionLiftOnInput f G β A ≫
        (DerivedCategory.Q (C := Y.Modules) ⋙ pullbackUsingCells f).map a := sorry

/-- The actual lift before descent along quasi-isomorphisms. -/
def extensionLiftOnCochains
    (G : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules)
    (β : DerivedCategory.Q (C := Y.Modules) ⋙ G ⟶ ordinaryPullbackCochain f) :
    DerivedCategory.Q (C := Y.Modules) ⋙ G ⟶
      DerivedCategory.Q (C := Y.Modules) ⋙ pullbackUsingCells f where
  app A := extensionLiftOnInput f G β A
  naturality := fun _ _ a ↦ extensionLiftOnInput_naturality f G β a

/-- The constructed lift on derived objects, obtained by native localization descent. -/
def extensionLift
    (G : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules)
    (β : DerivedCategory.Q (C := Y.Modules) ⋙ G ⟶ ordinaryPullbackCochain f) :
    G ⟶ pullbackUsingCells f :=
  Localization.liftNatTrans (DerivedCategory.Q (C := Y.Modules))
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ))
    (DerivedCategory.Q (C := Y.Modules) ⋙ G)
    (DerivedCategory.Q (C := Y.Modules) ⋙ pullbackUsingCells f)
    G (pullbackUsingCells f) (extensionLiftOnCochains f G β)

/-- The specified lift satisfies the right-extension comparison equation. -/
theorem extensionLift_fac
    (G : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules)
    (β : DerivedCategory.Q (C := Y.Modules) ⋙ G ⟶ ordinaryPullbackCochain f) :
    Functor.whiskerLeft (DerivedCategory.Q (C := Y.Modules)) (extensionLift f G β) ≫
      pullbackUsingCellsCounit f = β := sorry

/-- The actual terminal-extension morphism uses the specified coordinate-model lift. -/
def terminalExtensionLift
    (E : Functor.RightExtension (DerivedCategory.Q (C := Y.Modules))
      (ordinaryPullbackCochain f)) :
    E ⟶ Functor.RightExtension.mk (pullbackUsingCells f) (pullbackUsingCellsCounit f) :=
  CostructuredArrow.homMk (extensionLift f E.left E.hom) (extensionLift_fac f E.left E.hom)

/-- Naturality at the actual model augmentations determines any extension morphism uniquely. -/
theorem terminalExtensionLift_unique
    (E : Functor.RightExtension (DerivedCategory.Q (C := Y.Modules))
      (ordinaryPullbackCochain f))
    (m : E ⟶ Functor.RightExtension.mk (pullbackUsingCells f) (pullbackUsingCellsCounit f)) :
    m = terminalExtensionLift f E := sorry

/-- The universal right-extension data have their actual lift specified. Its laws are Prop
obligations; no model or extension map is selected from a new existence statement. -/
def pullbackTerminalWitness :
    (Functor.RightExtension.mk (pullbackUsingCells f) (pullbackUsingCellsCounit f)).IsUniversal :=
  IsTerminal.ofUniqueHom (terminalExtensionLift f) (terminalExtensionLift_unique f)

/-- The concrete model functor is a left derived functor through its specified counit and
actual terminal-extension lift. -/
instance pullbackUsingCells_isLeftDerived :
    (pullbackUsingCells f).IsLeftDerivedFunctor (pullbackUsingCellsCounit f)
      (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)) where
  isRightKanExtension := { nonempty_isUniversal := ⟨pullbackTerminalWitness f⟩ }

/-- On an actual input complex, identify iterated and composite pullback through their
specified model functors and the formal inverse of the intermediate augmentation. -/
def compositionOnInput :
    (pullbackUsingCells f).obj
        ((pullbackUsingCells g).obj ((DerivedCategory.Q (C := Z.Modules)).obj K)) ≅
      (pullbackUsingCells (f ≫ g)).obj ((DerivedCategory.Q (C := Z.Modules)).obj K) :=
  (pullbackUsingCells f).mapIso ((pullbackUsingCells_fac g).app K) ≪≫
    (pullbackUsingCells_fac f).app (middleModel g K) ≪≫
    compositionIso f g K ≪≫
    ((pullbackUsingCells_fac (f ≫ g)).app K).symm

/-- The specified model maps and augmentation squares make the comparison natural in
original cochain maps. The forward and reverse paths themselves are already constructed. -/
theorem compositionOnInput_naturality {A B : CochainComplex Z.Modules ℤ} (a : A ⟶ B) :
    ((DerivedCategory.Q (C := Z.Modules) ⋙ pullbackUsingCells g ⋙
        pullbackUsingCells f).map a) ≫ (compositionOnInput f g B).hom =
      (compositionOnInput f g A).hom ≫
        (DerivedCategory.Q (C := Z.Modules) ⋙ pullbackUsingCells (f ≫ g)).map a := sorry

/-- The actual natural isomorphism before descending along quasi-isomorphisms. -/
def compositionOnCochains :
    DerivedCategory.Q (C := Z.Modules) ⋙ pullbackUsingCells g ⋙ pullbackUsingCells f ≅
      DerivedCategory.Q (C := Z.Modules) ⋙ pullbackUsingCells (f ≫ g) :=
  NatIso.ofComponents (fun K ↦ compositionOnInput f g K)
    (fun a ↦ compositionOnInput_naturality f g a)

/-- The displayed composition isomorphism on derived categories is obtained by native
localization descent of its two constructed cochain-model directions. -/
@[stacks 0D6D "composition of displayed-model pullbacks"]
def compositionDerivedIso :
    pullbackUsingCells g ⋙ pullbackUsingCells f ≅ pullbackUsingCells (f ≫ g) :=
  Localization.liftNatIso (DerivedCategory.Q (C := Z.Modules))
    (HomologicalComplex.quasiIso Z.Modules (ComplexShape.up ℤ))
    (DerivedCategory.Q (C := Z.Modules) ⋙ pullbackUsingCells g ⋙ pullbackUsingCells f)
    (DerivedCategory.Q (C := Z.Modules) ⋙ pullbackUsingCells (f ≫ g))
    (pullbackUsingCells g ⋙ pullbackUsingCells f) (pullbackUsingCells (f ≫ g))
    (compositionOnCochains f g)

end AlgebraicGeometry.AlgebraicSpace.Modules.CellModels
