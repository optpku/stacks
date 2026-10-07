module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_3_5
public import stacks_project.Chap85.Lemma_85_9_1_Complex
public import stacks_project.Chap85.Lemma_85_9_1_Fiberwise
public import stacks_project.Chap85.Lemma_85_9_1_Pullback

/-!
# Lemma 85.9.1

In Situation 85.3.3 let `a0` be an augmentation towards a site `D` as in
Remark 85.4.1. For any abelian sheaf `G` on `D` the alternating-face complex
`… → g_{2!}(a_2⁻¹ G) → g_{1!}(a_1⁻¹ G) → g_{0!}(a_0⁻¹ G) → a⁻¹ G → 0` of
abelian sheaves on `C_total` is exact.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology HomologicalComplex Opposite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable (G : Sheaf K.toGrothendieck AddCommGrpCat.{w})
include h_morphism
include h_aug

/-- Lemma 85.9.1 (1): in Situation 85.3.3 case A, with an augmentation towards a
site `D` as in Remark 85.4.1, the complex
`… → g_{2!}(a_2⁻¹ G) → g_{1!}(a_1⁻¹ G) → g_{0!}(a_0⁻¹ G)` of abelian sheaves on
`C_total`, with differentials the alternating face sums, is a resolution of
`a⁻¹ G`. -/
@[stacks 0D78, instance]
instance inverseImageAugmentation_quasiIso :
    QuasiIso
      (inverseImageAugmentation C J K u0 G :
        inverseImageComplex C J K u0 G ⟶
          (ChainComplex.single₀ _).obj
            ((IsAugmentation.abelianInverseImage C J K u0).obj G)) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [IsFiberwiseSite F J]
variable [IsAugmentation F J K u0]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable (G : Sheaf K.toGrothendieck AddCommGrpCat.{w})

/-- Lemma 85.9.1 (2): in Situation 85.3.3 case B, with an augmentation towards a
site `D` as in Remark 85.4.1, the complex
`… → g_{2!}(a_2⁻¹ G) → g_{1!}(a_1⁻¹ G) → g_{0!}(a_0⁻¹ G)` of abelian sheaves on
`C_total`, with differentials the alternating face sums, is a resolution of
`a⁻¹ G`. -/
@[stacks 0D78, instance]
instance fiberInverseImageAugmentation_quasiIso :
    QuasiIso
      (fiberInverseImageAugmentation F J K u0 G :
        fiberInverseImageComplex F J K u0 G ⟶
          (ChainComplex.single₀ _).obj
            ((IsAugmentation.abelianInverseImage F J K u0).obj G)) :=
  sorry

end CategoryTheory.Grothendieck
