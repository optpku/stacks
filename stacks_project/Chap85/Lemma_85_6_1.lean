/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap85.Lemma_85_6_1_Ringed
public import stacks_project.Chap85.Lemma_85_6_1_LowerShriek
public import stacks_project.Chap85.Lemma_85_6_1_Fiber

/-!
# Lemma 85.6.1

A sheaf of rings on a simplicial total site gives canonical ringed component
inclusions. Their module pullbacks have canonical left adjoints with the
componentwise coproduct formula, in both presentations of a simplicial site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

/- Lemma 85.6.1. Canonical ringed component inclusions, their module lower shriek,
and the coproduct formula over all simplex operators. -/
@[stacks 0D72] #check (CategoryTheory.SimplicialSites.moduleLowerShriek_componentCoproductHom_isIso :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [IsMorphismDiagram C J]
    [UnivLE.{max u v, w}]
    (O : Sheaf (topology C J) RingCat.{w})
    [(topology C J).HasSheafCompose (forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
    [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
    [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
    [HasWeakSheafify (topology C J) (Type w)]
    (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)),
    IsIso (moduleLowerShriek_componentCoproductHom C J O n m G))

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]

#check (CategoryTheory.SimplicialSites.stageMorphism C J O :
  ∀ n, ToposHom (componentRingedSite C J O n) (totalRingedSite C J O))

#check (CategoryTheory.SimplicialSites.stageMorphism_toTopos C J O :
  ∀ n, (stageMorphism C J O n).toTopos = ofStageMorphism C J n)

#check (CategoryTheory.SimplicialSites.ringedToposMap C J O :
  ∀ {m n : SimplexCategory} (_ : m ⟶ n),
    ToposHom (componentRingedSite C J O n) (componentRingedSite C J O m))

#check (CategoryTheory.SimplicialSites.ringedToposMap_toTopos C J O :
  ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (ringedToposMap C J O φ).toTopos = toposMap C J φ)

#check (CategoryTheory.SimplicialSites.moduleLowerShriek.adjunction C J O :
  ∀ n, moduleLowerShriek C J O n ⊣ Cocontinuous.moduleInverseImage (ofStage C n) O)

#check (CategoryTheory.SimplicialSites.moduleInverseImageIsoModulePullback C J O :
  ∀ n, Cocontinuous.moduleInverseImage (ofStage C n) O ≅
    (stageMorphism C J O n).modulePullback)

#check (CategoryTheory.SimplicialSites.stageMorphism_modulePullback_isRightAdjoint C J O :
  ∀ n, ((stageMorphism C J O n).modulePullback).IsRightAdjoint)

variable (n : SimplexCategory)

#check ((CategoryTheory.SimplicialSites.moduleLowerShriek.adjunction C J O n).ofNatIsoRight
    (CategoryTheory.SimplicialSites.moduleInverseImageIsoModulePullback C J O n) :
  moduleLowerShriek C J O n ⊣ (stageMorphism C J O n).modulePullback)

end CategoryTheory.SimplicialSites

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
