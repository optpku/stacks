/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberPostnikov
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Postnikov

/-!
# Lemma 85.14.4

In Situation 85.3.3, with a sheaf of rings `O` on `C_total` and an object `K`
of `D(O)`, the objects `X_n = (g_{n!} O_n) ⊗^L_O K` and
`Y_n = (g_{n!} O_n → ⋯ → g_{0!} O_0)[-n] ⊗^L_O K` form a sequential Postnikov
system for `⋯ → X_2 → X_1 → X_0`, and `K` is the sequential homotopy colimit
of `Y_n[n]` in `D(O)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory DerivedCategory
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [UnivLE.{max u v, w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) CommRingCat.{w})
variable [(topology C J).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J (Sheaf.ringSheafOfComm O) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (K : RingedSiteDerived (topology C J) O)

/- Lemma 85.14.4: distinguished triangles on the covariant total site. -/
@[stacks 0D9Q] #check (CategoryTheory.SimplicialSites.modulePostnikov_distinguished C J O K :
    ∀ n : ℕ,
    Triangle.mk ((modulePostnikovTower C J O K).toX (n + 1))
      ((modulePostnikovTower C J O K).toNext n)
      ((modulePostnikovTower C J O K).connecting n) ∈
        distTriang (RingedSiteDerived (topology C J) O))

/- Lemma 85.14.4: homotopy colimit of the shifted stages on the covariant total site. -/
@[stacks 0D9Q] #check (CategoryTheory.SimplicialSites.modulePostnikov_isHomotopyColimit C J O K :
    HomotopyColimit.IsOf (modulePostnikovShifted C J O K) K)

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [UnivLE.{max u v, w}]
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) CommRingCat.{w})
variable [(topology F J).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose
    (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (Opposite.op n))ᵒᵖ ⥤ Type w,
    (ι F (Opposite.op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (Opposite.op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J (Sheaf.ringSheafOfComm O) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J (Sheaf.ringSheafOfComm O) φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (K : RingedSiteDerived (topology F J) O)

/- Lemma 85.14.4: distinguished triangles on the fiberwise total site. -/
@[stacks 0D9Q] #check (CategoryTheory.Grothendieck.fiberModulePostnikov_distinguished F J O K :
    ∀ n : ℕ,
    Triangle.mk ((fiberModulePostnikovTower F J O K).toX (n + 1))
      ((fiberModulePostnikovTower F J O K).toNext n)
      ((fiberModulePostnikovTower F J O K).connecting n) ∈
        distTriang (RingedSiteDerived (topology F J) O))

/- Lemma 85.14.4: homotopy colimit of the shifted stages on the fiberwise total site. -/
@[stacks 0D9Q] #check (CategoryTheory.Grothendieck.fiberModulePostnikov_isHomotopyColimit F J O K :
    HomotopyColimit.IsOf (fiberModulePostnikovShifted F J O K) K)

end CategoryTheory.Grothendieck
