module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_9_2_Complex
public import stacks_project.Chap85.Lemma_85_9_2_Fiberwise

/-!
# Lemma 85.9.2

In Situation 85.3.3 let `a0` be an augmentation towards a site `D` as in
Remark 85.4.1. For an abelian sheaf `F` on `C_total` there is a canonical
complex `0 → a_* F → a_{0,*} F_0 → a_{1,*} F_1 → ⋯` on `D` which is exact in
degrees `-1`, `0` and exact everywhere if `F` is injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex Opposite
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
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck AddCommGrpCat.{w})]
include h_morphism
include h_aug

/-- Lemma 85.9.2 (1): in Situation 85.3.3 case A, with an augmentation towards a
site `D` as in Remark 85.4.1, let `F` be an abelian sheaf on `C_total`. The
canonical complex `0 → a_* F → a_{0,*} F_0 → a_{1,*} F_1 → ⋯` of abelian sheaves
on `D` is exact in degrees `-1` and `0`. -/
@[stacks 0D79]
theorem augmentationCechCochain_exactAt_negOne_zero
    (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)) :
    (augmentationCechCochain C J K u0 F).ExactAt n :=
  sorry

/-- Lemma 85.9.2 (2): in Situation 85.3.3 case A, if `F` is injective then the
canonical complex `0 → a_* F → a_{0,*} F_0 → a_{1,*} F_1 → ⋯` is exact in every
degree. -/
@[stacks 0D79]
theorem augmentationCechCochain_acyclic_of_injective
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) [Injective F] :
    (augmentationCechCochain C J K u0 F).Acyclic :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [IsFiberwiseSite F J]
variable [IsAugmentation F J K u0]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck AddCommGrpCat.{w})]

/-- Lemma 85.9.2 (3): in Situation 85.3.3 case B, with an augmentation towards a
site `D` as in Remark 85.4.1, let `G` be an abelian sheaf on `C_total`. The
canonical complex `0 → a_* G → a_{0,*} G_0 → a_{1,*} G_1 → ⋯` of abelian sheaves
on `D` is exact in degrees `-1` and `0`. -/
@[stacks 0D79]
theorem fiberAugmentationCechCochain_exactAt_negOne_zero
    (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)) :
    (fiberAugmentationCechCochain F J K u0 G).ExactAt n :=
  sorry

/-- Lemma 85.9.2 (4): in Situation 85.3.3 case B, if `G` is injective then the
canonical complex `0 → a_* G → a_{0,*} G_0 → a_{1,*} G_1 → ⋯` is exact in every
degree. -/
@[stacks 0D79]
theorem fiberAugmentationCechCochain_acyclic_of_injective
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) [Injective G] :
    (fiberAugmentationCechCochain F J K u0 G).Acyclic :=
  sorry

end CategoryTheory.Grothendieck
