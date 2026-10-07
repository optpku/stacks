module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_14_4_Fiberwise
public import stacks_project.Chap85.Lemma_85_14_4_Tower

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

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
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
variable [UnivLE.{max u v, w}]
variable [HasRightDerivedTensor (totalModules C J O)]
variable (K : totalDerived C J O)

/-- Lemma 85.14.4 (1): in Situation 85.3.3 case A, with a sheaf of rings `O` on
`C_total` and `K` an object of `D(O)`, the objects
`X_n = (g_{n!} O_n) ⊗^L_O K` and
`Y_n = (g_{n!} O_n → ⋯ → g_{0!} O_0)[-n] ⊗^L_O K`, together with the canonical
maps of the alternating-face resolution, form a sequential Postnikov system for
`⋯ → X_2 → X_1 → X_0` in `D(O)`. -/
@[stacks 0D9Q]
theorem modulePostnikov_distinguished (n : ℕ) :
    Triangle.mk ((modulePostnikovTower C J O K).toX (n + 1))
      ((modulePostnikovTower C J O K).toNext n)
      ((modulePostnikovTower C J O K).connecting n) ∈
        distTriang (totalDerived C J O) :=
  sorry

/-- Lemma 85.14.4 (2): in Situation 85.3.3 case A, `K` is a sequential homotopy
colimit of `Y_n[n]` in `D(O)`. -/
@[stacks 0D9Q]
theorem modulePostnikov_isHomotopyColimit :
    HomotopyColimit.IsOf (modulePostnikovShifted C J O K) K :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
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
variable [UnivLE.{max u v, w}]
variable [HasRightDerivedTensor (fiberTotalModules F J O)]
variable (K : fiberTotalDerived F J O)

/-- Lemma 85.14.4 (3): in Situation 85.3.3 case B, with a sheaf of rings `O` on
`C_total` and `K` an object of `D(O)`, the objects
`X_n = (g_{n!} O_n) ⊗^L_O K` and
`Y_n = (g_{n!} O_n → ⋯ → g_{0!} O_0)[-n] ⊗^L_O K`, together with the canonical
maps of the alternating-face resolution, form a sequential Postnikov system for
`⋯ → X_2 → X_1 → X_0` in `D(O)`. -/
@[stacks 0D9Q]
theorem fiberModulePostnikov_distinguished (n : ℕ) :
    Triangle.mk ((fiberModulePostnikovTower F J O K).toX (n + 1))
      ((fiberModulePostnikovTower F J O K).toNext n)
      ((fiberModulePostnikovTower F J O K).connecting n) ∈
        distTriang (fiberTotalDerived F J O) :=
  sorry

/-- Lemma 85.14.4 (4): in Situation 85.3.3 case B, `K` is a sequential homotopy
colimit of `Y_n[n]` in `D(O)`. -/
@[stacks 0D9Q]
theorem fiberModulePostnikov_isHomotopyColimit :
    HomotopyColimit.IsOf (fiberModulePostnikovShifted F J O K) K :=
  sorry

end CategoryTheory.Grothendieck
