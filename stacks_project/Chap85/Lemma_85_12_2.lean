/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Coface
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Coface
public import ReasLib.CategoryTheory.Sites.Grothendieck.Coface
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCoface
import StacksCheckRecall

/-!
# Lemma 85.12.2

In both presentations of a simplicial site, cartesianness of sheaves and unbounded
derived objects is detected by the canonical comparisons along coface operators.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite RingedSite

noncomputable section

universe u v w

section Covariant

open SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram C J]
include instMorphismDiagram instWeakSheafify instLeftKan

/- Lemma 85.12.2 (1), case A: sheaves of sets. -/
@[stacks 07TG] #check (CategoryTheory.SimplicialSites.Sheaf.isCartesian_iff_delta C J :
  ∀ G : Sheaf (SimplicialSites.topology C J) (Type w),
    SimplicialSites.IsCartesian C J G ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (SimplicialSites.transition C J (SimplexCategory.δ j) G))

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/- Lemma 85.12.2 (2), case A: sheaves of abelian groups. -/
@[stacks 07TG] #check (CategoryTheory.SimplicialSites.abelian_isCartesian_iff_delta C J :
  ∀ G : Sheaf (SimplicialSites.topology C J) AddCommGrpCat.{w},
    SimplicialSites.Abelian.IsCartesian C J G ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (SimplicialSites.abelianTransition C J (SimplexCategory.δ j) G))

variable [HasSheafify (SimplicialSites.topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Lemma 85.12.2 (3), case A: unbounded derived abelian sheaves. -/
@[stacks 07TG] #check (CategoryTheory.SimplicialSites.AbelianDerived.isCartesian_iff_delta C J :
  ∀ K : DerivedCategory (Sheaf (SimplicialSites.topology C J) AddCommGrpCat.{w}),
    SimplicialSites.AbelianDerived.IsCartesian C J K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (SimplicialSites.derivedTransition C J (SimplexCategory.δ j) K))

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

/- Lemma 85.12.2 (4), case A: modules over the total ring sheaf. -/
@[stacks 07TG] #check (CategoryTheory.SimplicialSites.Module.isCartesian_iff_delta C J O :
  ∀ M : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf,
    SimplicialSites.Module.IsCartesian C J O M ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (SimplicialSites.moduleTransition C J O (SimplexCategory.δ j) M))

/- Lemma 85.12.2 (5), case A: unbounded derived modules. -/
@[stacks 07TG] #check (CategoryTheory.SimplicialSites.ModuleDerived.isCartesian_iff_delta C J O :
  ∀ K : Hom.ModuleDerived.{w} (totalRingedSite C J O),
    SimplicialSites.ModuleDerived.IsCartesian C J O K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (SimplicialSites.moduleDerivedTransition C J O (SimplexCategory.δ j) K))

end Covariant

section Fiberwise

open Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [h_fiberwise : IsFiberwiseSite F J]
include h_fiberwise
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]

/- Lemma 85.12.2 (6), case B: sheaves of sets. -/
@[stacks 07TG] #check (CategoryTheory.Grothendieck.Sheaf.isCartesian_iff_delta F J :
  ∀ G : Sheaf (Grothendieck.topology F J) (Type w),
    Grothendieck.Sheaf.IsCartesian F J (Type w) G ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.Sheaf.sheafTransition F J (Type w) (SimplexCategory.δ j) G))

variable [HasWeakSheafify (Grothendieck.topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Lemma 85.12.2 (7), case B: sheaves of abelian groups. -/
@[stacks 07TG] #check (CategoryTheory.Grothendieck.abelian_isCartesian_iff_delta F J :
  ∀ G : Sheaf (Grothendieck.topology F J) AddCommGrpCat.{w},
    Grothendieck.Sheaf.IsCartesian F J AddCommGrpCat.{w} G ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.Sheaf.sheafTransition F J AddCommGrpCat.{w} (SimplexCategory.δ j) G))

variable [HasSheafify (Grothendieck.topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Lemma 85.12.2 (8), case B: unbounded derived abelian sheaves. -/
@[stacks 07TG] #check (CategoryTheory.Grothendieck.AbelianDerived.isCartesian_iff_delta F J :
  ∀ K : DerivedCategory (Sheaf (Grothendieck.topology F J) AddCommGrpCat.{w}),
    Grothendieck.AbelianDerived.IsCartesian F J K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.derivedTransition F J (SimplexCategory.δ j) K))

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

/- Lemma 85.12.2 (9), case B: modules over the total ring sheaf. -/
@[stacks 07TG] #check (CategoryTheory.Grothendieck.Module.isCartesian_iff_delta F J O :
  ∀ M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf,
    Grothendieck.Module.IsCartesian F J O M ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.moduleTransition F J O (SimplexCategory.δ j) M))

/- Lemma 85.12.2 (10), case B: unbounded derived modules. -/
@[stacks 07TG] #check (CategoryTheory.Grothendieck.ModuleDerived.isCartesian_iff_delta F J O :
  ∀ K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O),
    Grothendieck.ModuleDerived.IsCartesian F J O K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.moduleDerivedTransition F J O (SimplexCategory.δ j) K))

end Fiberwise
