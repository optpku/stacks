/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import stacks_project.Chap85.Definition_85_12_1_Fiberwise
import ReasLib.CategoryTheory.Sites.Family.Simplicial.Cartesian
import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Quasicoherent
import ReasLib.CategoryTheory.Sites.Simplicial.CartesianHomology
import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.CartesianHomology
import StacksCheckRecall

/-!
# Definition 85.12.1

Cartesian sheaves, modules, and unbounded derived objects in both presentations
of a simplicial site are characterized by their canonical restriction comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor RingedSite

universe u v w

noncomputable section

section Covariant

open SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram C J]
include instMorphismDiagram instWeakSheafify instLeftKan

/- Definition 85.12.1 (1), case A: sheaves of sets. -/
@[stacks 07TF] #check (CategoryTheory.SimplicialSites.isCartesian_iff C J :
  ∀ G : Sheaf (SimplicialSites.topology C J) (Type w),
    SimplicialSites.IsCartesian C J G ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (SimplicialSites.transition C J φ G))

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/- Definition 85.12.1 (1), case A: sheaves of abelian groups. -/
@[stacks 07TF] #check (CategoryTheory.SimplicialSites.abelian_isCartesian_iff C J :
  ∀ G : Sheaf (SimplicialSites.topology C J) AddCommGrpCat.{w},
    SimplicialSites.Abelian.IsCartesian C J G ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (SimplicialSites.abelianTransition C J φ G))

variable [HasSheafify (SimplicialSites.topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Definition 85.12.1 (3), case A: unbounded derived abelian sheaves. -/
@[stacks 07TF] #check (CategoryTheory.SimplicialSites.AbelianDerived.isCartesian_iff C J :
  ∀ K : DerivedCategory (Sheaf (SimplicialSites.topology C J) AddCommGrpCat.{w}),
    SimplicialSites.AbelianDerived.IsCartesian C J K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (SimplicialSites.derivedTransition C J φ K))

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

/- Definition 85.12.1 (2), case A: modules over the total ring sheaf. -/
@[stacks 07TF] #check (CategoryTheory.SimplicialSites.Module.isCartesian_iff C J O :
  ∀ M : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf,
    SimplicialSites.Module.IsCartesian C J O M ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (SimplicialSites.moduleTransition C J O φ M))

/- Definition 85.12.1 (4), case A: unbounded derived modules. -/
@[stacks 07TF] #check (CategoryTheory.SimplicialSites.ModuleDerived.isCartesian_iff C J O :
  ∀ K : Hom.ModuleDerived.{w} (totalRingedSite C J O),
    SimplicialSites.ModuleDerived.IsCartesian C J O K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (SimplicialSites.moduleDerivedTransition C J O φ K))

end Covariant

section Fiberwise

open Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [h_fiberwise : IsFiberwiseSite F J]
include h_fiberwise
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]

/- Definition 85.12.1 (1), case B: sheaves of sets. -/
@[stacks 07TF] #check (CategoryTheory.Grothendieck.Sheaf.isCartesian_iff F J (Type w) :
  ∀ G : Sheaf (Grothendieck.topology F J) (Type w),
    Grothendieck.Sheaf.IsCartesian F J (Type w) G ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (Grothendieck.Sheaf.sheafTransition F J (Type w) φ G))

variable [HasWeakSheafify (Grothendieck.topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Definition 85.12.1 (1), case B: sheaves of abelian groups. -/
@[stacks 07TF] #check (CategoryTheory.Grothendieck.Sheaf.isCartesian_iff F J AddCommGrpCat.{w} :
  ∀ G : Sheaf (Grothendieck.topology F J) AddCommGrpCat.{w},
    Grothendieck.Sheaf.IsCartesian F J AddCommGrpCat.{w} G ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (Grothendieck.Sheaf.sheafTransition F J AddCommGrpCat.{w} φ G))

variable [HasSheafify (Grothendieck.topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Definition 85.12.1 (3), case B: unbounded derived abelian sheaves. -/
@[stacks 07TF] #check (CategoryTheory.Grothendieck.AbelianDerived.isCartesian_iff F J :
  ∀ K : DerivedCategory (Sheaf (Grothendieck.topology F J) AddCommGrpCat.{w}),
    Grothendieck.AbelianDerived.IsCartesian F J K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (Grothendieck.derivedTransition F J φ K))

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

/- Definition 85.12.1 (2), case B: modules over the total ring sheaf. -/
@[stacks 07TF] #check (CategoryTheory.Grothendieck.Module.isCartesian_iff F J O :
  ∀ M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf,
    Grothendieck.Module.IsCartesian F J O M ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (Grothendieck.moduleTransition F J O φ M))

/- Definition 85.12.1 (4), case B: unbounded derived modules. -/
@[stacks 07TF] #check (CategoryTheory.Grothendieck.ModuleDerived.isCartesian_iff F J O :
  ∀ K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O),
    Grothendieck.ModuleDerived.IsCartesian F J O K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (Grothendieck.moduleDerivedTransition F J O φ K))

end Fiberwise
