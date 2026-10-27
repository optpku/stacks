/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.ShriekTensor
public import ReasLib.CategoryTheory.Sites.Grothendieck.ShriekTensor
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ShriekTensor
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberShriekTensor
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

section Abelian

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasPointwiseLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]


/- Lemma 85.12.9 (1). A derived abelian sheaf is cartesian exactly when
all canonical lower-shriek integer-tensor comparisons are invertible. -/
@[stacks 0D9E] #check
  (CategoryTheory.SimplicialSites.AbelianDerived.isCartesian_iff_shriekTensor C J :
    ∀ K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}),
      CategoryTheory.SimplicialSites.AbelianDerived.IsCartesian C J K ↔
        ∀ n : SimplexCategory,
          IsIso (CategoryTheory.SimplicialSites.AbelianDerived.shriekTensorComparison C J n K))

end Abelian

section Modules

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable (O : Sheaf (topology C J) CommRingCat.{w})
variable [(topology C J).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology C J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose
    (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J (Sheaf.ringSheafOfComm O) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived
    (stageMorphism C J (Sheaf.ringSheafOfComm O) n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived
      (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ)]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]


variable (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
  ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))

/- Lemma 85.12.9 (2). Under flat simplex structure-ring maps, a derived
module is cartesian exactly when all canonical lower-shriek tensor comparisons are invertible. -/
@[stacks 0D9E] #check
  (CategoryTheory.SimplicialSites.ModuleDerived.isCartesian_iff_shriekTensor C J O h_flat :
    ∀ K : Hom.ModuleDerived.{w} (totalRingedSite C J (Sheaf.ringSheafOfComm O)),
      CategoryTheory.SimplicialSites.ModuleDerived.IsCartesian C J (Sheaf.ringSheafOfComm O) K ↔
        ∀ n : SimplexCategory,
          IsIso (CategoryTheory.SimplicialSites.ModuleDerived.shriekTensorComparison C J O h_flat n K))

end Modules

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

section Abelian

variable (C : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsFiberwiseSite C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ Type w,
    (ι C (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ Type w,
    (ι C (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj (op n))ᵒᵖ ⥤ Type w),
    ((C.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι C (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι C (op n)).op.HasPointwiseLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι C (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/- Lemma 85.12.9 (3). A derived abelian sheaf is cartesian exactly when
all canonical lower-shriek integer-tensor comparisons are invertible. -/
@[stacks 0D9E] #check
  (CategoryTheory.Grothendieck.AbelianDerived.isCartesian_iff_shriekTensor C J :
    ∀ K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}),
      CategoryTheory.Grothendieck.AbelianDerived.IsCartesian C J K ↔
        ∀ n : SimplexCategory,
          IsIso (CategoryTheory.Grothendieck.AbelianDerived.shriekTensorComparison C J n K))

end Abelian

section Modules

variable (C : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsFiberwiseSite C J]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ Type w,
    (ι C (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj (op n))ᵒᵖ ⥤ Type w),
    ((C.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable (O : Sheaf (topology C J) CommRingCat.{w})
variable [(topology C J).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology C J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose
    (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism C J (Sheaf.ringSheafOfComm O) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap C J (Sheaf.ringSheafOfComm O) φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived
    (fiberStageMorphism C J (Sheaf.ringSheafOfComm O) n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived
      (fiberRingedToposMap C J (Sheaf.ringSheafOfComm O) φ)]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
  ToposHom.IsFlat (fiberRingedToposMap C J (Sheaf.ringSheafOfComm O) φ))

/- Lemma 85.12.9 (4). Under flat simplex structure-ring maps, a derived
module is cartesian exactly when all canonical lower-shriek tensor comparisons are invertible. -/
@[stacks 0D9E] #check
  (CategoryTheory.Grothendieck.ModuleDerived.isCartesian_iff_shriekTensor C J O h_flat :
    ∀ K : Hom.ModuleDerived.{w} (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)),
      CategoryTheory.Grothendieck.ModuleDerived.IsCartesian C J (Sheaf.ringSheafOfComm O) K ↔
        ∀ n : SimplexCategory,
          IsIso (CategoryTheory.Grothendieck.ModuleDerived.shriekTensorComparison C J O h_flat n K))

end Modules

end CategoryTheory.Grothendieck

