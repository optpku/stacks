/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.Cartesian.Abelian
public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian.Abelian
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cartesian.WeakSerre
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesian.WeakSerre

/-!
# Lemma 85.12.6

In both presentations of Situation 85.3.3, cartesian abelian sheaves form a weak
Serre subcategory and are closed under colimits. Cartesian modules over a ring
sheaf form a weak Serre subcategory when every coface morphism of ringed topoi
is flat; their closure under colimits does not require flatness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Opposite RingedSite

universe u v w u' v'

namespace CategoryTheory.SimplicialSites.Sheaf

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

section WeakSerre

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]

/- Lemma 85.12.6
Cartesian abelian sheaves and modules form weak Serre subcategories, and their
colimits are cartesian, in both presentations of Situation 85.3.3. -/
@[stacks 0D7J] #check (CategoryTheory.SimplicialSites.Sheaf.cartesianProperty_isWeakSerreClass C J :
    IsWeakSerreClass (fun G : Sheaf (topology C J) AddCommGrpCat.{w} ↦ IsCartesian C J G))

end WeakSerre

variable (D : Type u') [Category.{v'} D]

#check (CategoryTheory.SimplicialSites.Sheaf.cartesianProperty_isClosedUnderColimitsOfShape C J D :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (fun G : Sheaf (topology C J) AddCommGrpCat.{w} ↦ IsCartesian C J G) D)

end CategoryTheory.SimplicialSites.Sheaf

namespace CategoryTheory.Grothendieck.Sheaf

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

section WeakSerre

#check (CategoryTheory.Grothendieck.Sheaf.cartesianProperty_isWeakSerreClass F J :
    IsWeakSerreClass (cartesianProperty F J AddCommGrpCat.{w}))

end WeakSerre

variable (D : Type u') [Category.{v'} D]

#check (CategoryTheory.Grothendieck.Sheaf.cartesianProperty_isClosedUnderColimitsOfShape F J D :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (cartesianProperty F J AddCommGrpCat.{w}) D)

end CategoryTheory.Grothendieck.Sheaf

namespace CategoryTheory.SimplicialSites.Module

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]

section WeakSerre

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ {n : ℕ} (j : Fin (n + 2)),
    ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ j))]

#check (CategoryTheory.SimplicialSites.Module.cartesianProperty_isWeakSerreClass C J O :
    IsWeakSerreClass (fun M : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf ↦
      IsCartesian C J O M))

end WeakSerre

variable (D : Type u') [Category.{v'} D]

#check (CategoryTheory.SimplicialSites.Module.cartesianProperty_isClosedUnderColimitsOfShape C J O D :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (fun M : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf ↦
        IsCartesian C J O M) D)

end CategoryTheory.SimplicialSites.Module

namespace CategoryTheory.Grothendieck.Module

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

section WeakSerre

variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ {n : ℕ} (j : Fin (n + 2)),
    ToposHom.IsFlat (fiberRingedToposMap F J O (SimplexCategory.δ j))]

#check (CategoryTheory.Grothendieck.Module.cartesianProperty_isWeakSerreClass F J O :
    IsWeakSerreClass (fun M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf ↦
      IsCartesian F J O M))

end WeakSerre

variable (D : Type u') [Category.{v'} D]

#check (CategoryTheory.Grothendieck.Module.cartesianProperty_isClosedUnderColimitsOfShape F J O D :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (fun M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf ↦
        IsCartesian F J O M) D)

end CategoryTheory.Grothendieck.Module
