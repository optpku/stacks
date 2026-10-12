/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_3_5
public import stacks_project.Chap85.Lemma_85_8_1_Complex
public import stacks_project.Chap85.Lemma_85_8_1_Fiberwise

/-!
# Lemma 85.8.1

In Situation 85.3.3 the alternating-face complex of abelian sheaves
`… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ` on `C_total` is a resolution of the
constant sheaf with value `ℤ`.
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
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

/-- Lemma 85.8.1 (1): in Situation 85.3.3 case A, the complex
`… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ` of abelian sheaves on `C_total`, with
differentials the alternating face sums, is a resolution of the constant sheaf
`ℤ` on `C_total`. -/
@[stacks 09WI, instance]
instance augmentation_quasiIso :
    QuasiIso
      (augmentation C J :
        complex C J ⟶
          (ChainComplex.single₀ _).obj (constantIntegerSheaf (topology C J))) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.8.1 (2): in Situation 85.3.3 case B, the complex
`… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ` of abelian sheaves on `C_total`, with
differentials the alternating face sums, is a resolution of the constant sheaf
`ℤ` on `C_total`. -/
@[stacks 09WI, instance]
instance fiberAugmentation_quasiIso :
    QuasiIso
      (fiberAugmentation F J :
        fiberComplex F J ⟶
          (ChainComplex.single₀ _).obj (constantIntegerSheaf (topology F J))) :=
  sorry

end CategoryTheory.Grothendieck
