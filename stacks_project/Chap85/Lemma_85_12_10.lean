/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberQuasicoherent
import StacksCheckRecall

/-!
# Lemma 85.12.10

In Situation 85.3.3, an `O`-module on `C_total` is quasi-coherent if and only if
it is cartesian and every stage restriction `F_n` is a quasi-coherent `O_n`-module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O f).structureMap).IsRightAdjoint]
variable [∀ U : totalSite C, ((topology C J).over U).HasSheafCompose
    (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ U : totalSite C, HasWeakSheafify ((topology C J).over U) AddCommGrpCat.{w}]
variable [∀ U : totalSite C, ((topology C J).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (U : C.obj n),
    (((J n).toGrothendieck).over U).HasSheafCompose
      (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ (n : SimplexCategory) (U : C.obj n),
    HasWeakSheafify (((J n).toGrothendieck).over U) AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (U : C.obj n),
    (((J n).toGrothendieck).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/- Lemma 85.12.10 (1)
A module on the total site is quasi-coherent exactly when it is cartesian and
all its stage restrictions are quasi-coherent. -/
@[stacks 0D7M] #check (CategoryTheory.SimplicialSites.module_isQuasicoherent_iff C J O :
  ∀ F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf,
    F.IsQuasicoherent ↔
      Module.IsCartesian C J O F ∧
        ∀ n : SimplexCategory, ((moduleComponent C J O n).obj F).IsQuasicoherent)

#check (CategoryTheory.SimplicialSites.instModuleIsCartesian_of_isQuasicoherent C J O :
  ∀ (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [F.IsQuasicoherent], Module.IsCartesian C J O F)

#check (CategoryTheory.SimplicialSites.instModuleComponent_isQuasicoherent C J O :
  ∀ (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [F.IsQuasicoherent] (n : SimplexCategory),
    ((moduleComponent C J O n).obj F).IsQuasicoherent)

#check (CategoryTheory.SimplicialSites.instIsQuasicoherent_of_isCartesian C J O :
  ∀ (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [Module.IsCartesian C J O F]
    [∀ n : SimplexCategory, ((moduleComponent C J O n).obj F).IsQuasicoherent],
    F.IsQuasicoherent)

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
variable [∀ U : Grothendieck F, ((topology F J).over U).HasSheafCompose
    (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ U : Grothendieck F, HasWeakSheafify ((topology F J).over U) AddCommGrpCat.{w}]
variable [∀ U : Grothendieck F, ((topology F J).over U).WEqualsLocallyBijective
    AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (U : F.obj (op n)),
    (((J (op n)).toGrothendieck).over U).HasSheafCompose
      (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ (n : SimplexCategory) (U : F.obj (op n)),
    HasWeakSheafify (((J (op n)).toGrothendieck).over U) AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (U : F.obj (op n)),
    (((J (op n)).toGrothendieck).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/- Lemma 85.12.10 (2)
A module on the fiberwise total site is quasi-coherent exactly when it is cartesian
and all its fiber restrictions are quasi-coherent. -/
@[stacks 0D7M] #check (CategoryTheory.Grothendieck.module_isQuasicoherent_iff F J O :
  ∀ M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf,
    M.IsQuasicoherent ↔
      Module.IsCartesian F J O M ∧
        ∀ n : SimplexCategory, ((moduleComponent F J O n).obj M).IsQuasicoherent)

#check (CategoryTheory.Grothendieck.instModuleIsCartesian_of_isQuasicoherent F J O :
  ∀ (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [M.IsQuasicoherent], Module.IsCartesian F J O M)

#check (CategoryTheory.Grothendieck.instModuleComponent_isQuasicoherent F J O :
  ∀ (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [M.IsQuasicoherent] (n : SimplexCategory),
    ((moduleComponent F J O n).obj M).IsQuasicoherent)

#check (CategoryTheory.Grothendieck.instIsQuasicoherent_of_isCartesian F J O :
  ∀ (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [Module.IsCartesian F J O M]
    [∀ n : SimplexCategory, ((moduleComponent F J O n).obj M).IsQuasicoherent],
    M.IsQuasicoherent)

end CategoryTheory.Grothendieck
