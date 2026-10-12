/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_10_2_Complex
public import stacks_project.Chap85.Lemma_85_10_2_Fiberwise

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

/-- Lemma 85.10.2 (1): in Situation 85.3.3 case A, the canonical complex
`0 → Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1) → ⋯` obtained by applying
`Hom(-, F)` to the resolution of `O` is exact in degrees `-1` and `0`. -/
@[stacks 0D9C]
theorem moduleCechCochain_exactAt_negOne_zero (F : SheafOfModules.{w} O) :
    (moduleCechCochain C J O F).ExactAt (-1) ∧
      (moduleCechCochain C J O F).ExactAt 0 :=
  sorry

/-- Lemma 85.10.2 (2): in Situation 85.3.3 case A, if `F` is an injective
`O`-module, then the complex `0 → Γ(C_total, F) → Γ(C_0, F_0) → ⋯` is exact
in every degree. -/
@[stacks 0D9C]
theorem moduleCechCochain_acyclic_of_injective (F : SheafOfModules.{w} O)
    [Injective F] :
    (moduleCechCochain C J O F).Acyclic :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
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

/-- Lemma 85.10.2 (3): in Situation 85.3.3 case B, the canonical complex
`0 → Γ(C_total, M) → Γ(C_0, M_0) → Γ(C_1, M_1) → ⋯` obtained by applying
`Hom(-, M)` to the resolution of `O` is exact in degrees `-1` and `0`. -/
@[stacks 0D9C]
theorem fiberModuleCechCochain_exactAt_negOne_zero (M : SheafOfModules.{w} O) :
    (fiberModuleCechCochain F J O M).ExactAt (-1) ∧
      (fiberModuleCechCochain F J O M).ExactAt 0 :=
  sorry

/-- Lemma 85.10.2 (4): in Situation 85.3.3 case B, if `M` is an injective
`O`-module, then the complex `0 → Γ(C_total, M) → Γ(C_0, M_0) → ⋯` is exact
in every degree. -/
@[stacks 0D9C]
theorem fiberModuleCechCochain_acyclic_of_injective (M : SheafOfModules.{w} O)
    [Injective M] :
    (fiberModuleCechCochain F J O M).Acyclic :=
  sorry

end CategoryTheory.Grothendieck
