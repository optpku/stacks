module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cech
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCech

/-!
# Lemma 85.10.2

In Situation 85.3.3 let `O` be a sheaf of rings. Let `F` be a sheaf of
`O`-modules. There is a canonical complex
`0 → Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1) → ⋯` which is exact in
degrees `-1`, `0` and exact everywhere if `F` is an injective `O`-module.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology HomologicalComplex Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]

/- Lemma 85.10.2: the canonical augmented Čech cochain is exact
in degrees `-1` and `0`. -/
@[stacks 0D9C] #check (CategoryTheory.SimplicialSites.moduleCechCochain_exactAt_negOne_zero C J O :
  ∀ (F : SheafOfModules.{w} O),
    (CategoryTheory.SimplicialSites.moduleCechCochain C J O F).ExactAt (-1) ∧
      (CategoryTheory.SimplicialSites.moduleCechCochain C J O F).ExactAt 0)

/- Lemma 85.10.2: the canonical augmented Čech cochain of an injective module
is acyclic. -/
@[stacks 0D9C] #check (CategoryTheory.SimplicialSites.moduleCechCochain_acyclic_of_injective C J O :
  ∀ (F : SheafOfModules.{w} O) [Injective F],
    (CategoryTheory.SimplicialSites.moduleCechCochain C J O F).Acyclic)

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
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
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]

/- Lemma 85.10.2: the canonical augmented Čech cochain is exact
in degrees `-1` and `0`. -/
@[stacks 0D9C] #check (CategoryTheory.Grothendieck.fiberModuleCechCochain_exactAt_negOne_zero F J O :
  ∀ (M : SheafOfModules.{w} O),
    (CategoryTheory.Grothendieck.fiberModuleCechCochain F J O M).ExactAt (-1) ∧
      (CategoryTheory.Grothendieck.fiberModuleCechCochain F J O M).ExactAt 0)

/- Lemma 85.10.2: the canonical augmented Čech cochain of an injective module
is acyclic. -/
@[stacks 0D9C] #check (CategoryTheory.Grothendieck.fiberModuleCechCochain_acyclic_of_injective F J O :
  ∀ (M : SheafOfModules.{w} O) [Injective M],
    (CategoryTheory.Grothendieck.fiberModuleCechCochain F J O M).Acyclic)

end CategoryTheory.Grothendieck
