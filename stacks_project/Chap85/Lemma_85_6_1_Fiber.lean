/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Fiber
public import stacks_project.Chap85.Lemma_85_3_5

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})

variable [UnivLE.{max u v, w}]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.Grothendieck.fiberStageMorphism F J O :
  ∀ n, ToposHom (fiberComponentRingedSite F J O n) (fiberTotalRingedSite F J O))

#check (CategoryTheory.Grothendieck.fiberStageMorphism_toTopos F J O :
  ∀ n, (fiberStageMorphism F J O n).toTopos = fiberMorphism F J n)

#check (CategoryTheory.Grothendieck.fiberRingedToposMap F J O :
  ∀ {m n : SimplexCategory} (_ : m ⟶ n),
    ToposHom (fiberComponentRingedSite F J O n) (fiberComponentRingedSite F J O m))

#check (CategoryTheory.Grothendieck.fiberRingedToposMap_toTopos F J O :
  ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (fiberRingedToposMap F J O φ).toTopos = toposMap F J φ)

#check (CategoryTheory.Grothendieck.fiberModuleLowerShriek.adjunction F J O :
  ∀ n, fiberModuleLowerShriek F J O n ⊣ Cocontinuous.moduleInverseImage (ι F (op n)) O)

#check (CategoryTheory.Grothendieck.fiberModuleInverseImageIsoModulePullback F J O :
  ∀ n, Cocontinuous.moduleInverseImage (ι F (op n)) O ≅
    (fiberStageMorphism F J O n).modulePullback)

#check (CategoryTheory.Grothendieck.fiberStageMorphism_modulePullback_isRightAdjoint F J O :
  ∀ n, ((fiberStageMorphism F J O n).modulePullback).IsRightAdjoint)

variable (n : SimplexCategory)

#check ((CategoryTheory.Grothendieck.fiberModuleLowerShriek.adjunction F J O n).ofNatIsoRight
    (CategoryTheory.Grothendieck.fiberModuleInverseImageIsoModulePullback F J O n) :
  fiberModuleLowerShriek F J O n ⊣ (fiberStageMorphism F J O n).modulePullback)

#check (CategoryTheory.Grothendieck.fiberModuleLowerShriek_componentCoproductHom_isIso F J O :
  ∀ (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)),
    IsIso (fiberModuleLowerShriek_componentCoproductHom F J O n m G))

end CategoryTheory.Grothendieck
