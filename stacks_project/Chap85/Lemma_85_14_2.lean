/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.Descent
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.FiberRestriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram.{u, v, w} C J]
include instMorphismDiagram instWeakSheafify instLeftKan
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/- Lemma 85.14.2 (1): an object of D(O) on the total site of a diagram of
morphisms of sites determines its canonical simplicial derived-module system. -/
@[stacks 0D9P] #check (CategoryTheory.SimplicialSites.toDerivedModuleSystem C J O :
  ∀ K : Hom.ModuleDerived.{w} (totalRingedSite C J O),
    RingedSite.Simplicial.DerivedModuleSystemOnComponents C J O)

/- Lemma 85.14.2 (2): a cartesian derived module on the total site of a diagram
of morphisms of sites determines a cartesian system. -/
@[stacks 0D9P] #check (CategoryTheory.SimplicialSites.toDerivedModuleSystem_isCartesian C J O :
  ∀ K : Hom.ModuleDerived.{w} (totalRingedSite C J O),
    ModuleDerived.IsCartesian C J O K →
      RingedSite.Simplicial.DerivedModuleSystem.IsCartesian
        (CategoryTheory.SimplicialSites.toDerivedModuleSystem C J O K))

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

variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

/- Lemma 85.14.2 (3): an object of D(O) on the total site of a fiberwise
simplicial site determines its canonical simplicial derived-module system. -/
@[stacks 0D9P] #check (CategoryTheory.Grothendieck.toDerivedModuleSystem F J O :
  ∀ K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O),
    CategoryTheory.Grothendieck.DerivedModuleSystemOnComponents F J O)

/- Lemma 85.14.2 (4): a cartesian derived module on the total site of a
fiberwise simplicial site determines a cartesian system. -/
@[stacks 0D9P] #check (CategoryTheory.Grothendieck.toDerivedModuleSystem_isCartesian F J O :
  ∀ K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O),
    ModuleDerived.IsCartesian F J O K →
      RingedSite.Simplicial.DerivedModuleSystem.IsCartesian
        (CategoryTheory.Grothendieck.toDerivedModuleSystem F J O K))

end CategoryTheory.Grothendieck
