/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import stacks_project.Chap85.Lemma_85_3_5_Coproduct
public import stacks_project.Chap85.Lemma_85_12_3_Pullback

/-!
# Alternating-face complex of `g_{n!}(a_n⁻¹ G)` on a morphism diagram of sites

In Situation 85.3.3 case A, with an augmentation towards a site `D` as in
Remark 85.4.1, the simplicial abelian sheaf `n ↦ g_{n!}(a_n⁻¹ G)` on the total
site, its augmentation to `a⁻¹ G`, and the associated alternating-face chain
complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
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
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable (G : Sheaf K.toGrothendieck AddCommGrpCat.{w})
include h_morphism
include h_aug

/-- Identity-on-sections identification of the degree-`n` restriction of `a⁻¹ G`
with `a_n⁻¹ G`. -/
def restrictAbelianInverseImageIso (n : SimplexCategory) :
    (stageRestrict C J AddCommGrpCat.{w} n).obj
      ((IsAugmentation.abelianInverseImage C J K u0).obj G) ≅
    (IsAugmentation.abelianStageInverseImage C J K u0 n).obj G where
  hom := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
  inv := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `restrictAbelianInverseImageIso` is identity on sections. -/
theorem restrictAbelianInverseImageIso_hom_app (n : SimplexCategory)
    (U : (C.obj n)ᵒᵖ) :
    ((restrictAbelianInverseImageIso C J K u0 G n).hom.hom.app U) = 𝟙 _ :=
  sorry

/-- The inverse map of `restrictAbelianInverseImageIso` is identity on sections. -/
theorem restrictAbelianInverseImageIso_inv_app (n : SimplexCategory)
    (U : (C.obj n)ᵒᵖ) :
    ((restrictAbelianInverseImageIso C J K u0 G n).inv.hom.app U) = 𝟙 _ :=
  sorry

/-- The structure map `g_{m!}(a_m⁻¹ G) ⟶ g_{n!}(a_n⁻¹ G)` induced by a simplex
operator `φ : n ⟶ m`. -/
def lowerShriekInverseImage_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (abelianLowerShriek C J m).obj
      ((IsAugmentation.abelianStageInverseImage C J K u0 m).obj G) ⟶
    (abelianLowerShriek C J n).obj
      ((IsAugmentation.abelianStageInverseImage C J K u0 n).obj G) :=
  ((abelianLowerShriek_adjunction C J m).homEquiv
      ((IsAugmentation.abelianStageInverseImage C J K u0 m).obj G)
      ((abelianLowerShriek C J n).obj
        ((IsAugmentation.abelianStageInverseImage C J K u0 n).obj G))).symm
    ((IsAugmentation.abelianStageInverseImage_comp C J K u0 φ).inv.app G ≫
      abelianLowerShriek_component C J φ
        ((IsAugmentation.abelianStageInverseImage C J K u0 n).obj G))

/-- Identity simplex operators induce identity structure maps of
`n ↦ g_{n!}(a_n⁻¹ G)`. -/
theorem lowerShriekInverseImage_map_id (n : SimplexCategory) :
    lowerShriekInverseImage_map C J K u0 G (𝟙 n) =
      𝟙 ((abelianLowerShriek C J n).obj
        ((IsAugmentation.abelianStageInverseImage C J K u0 n).obj G)) :=
  sorry

/-- Structure maps of `n ↦ g_{n!}(a_n⁻¹ G)` are functorial in simplex operators. -/
theorem lowerShriekInverseImage_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    lowerShriekInverseImage_map C J K u0 G (ψ ≫ φ) =
      lowerShriekInverseImage_map C J K u0 G φ ≫
        lowerShriekInverseImage_map C J K u0 G ψ :=
  sorry

/-- Opposite identity operators act as identity maps of `n ↦ g_{n!}(a_n⁻¹ G)`. -/
theorem lowerShriekInverseImage_map_id_op (n : SimplexCategoryᵒᵖ) :
    lowerShriekInverseImage_map C J K u0 G (𝟙 n.unop) =
      𝟙 ((abelianLowerShriek C J n.unop).obj
        ((IsAugmentation.abelianStageInverseImage C J K u0 n.unop).obj G)) :=
  sorry

/-- Opposite composition of simplex operators acts as composition of structure maps. -/
theorem lowerShriekInverseImage_map_comp_op {n m p : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (g : m ⟶ p) :
    lowerShriekInverseImage_map C J K u0 G (f ≫ g).unop =
      lowerShriekInverseImage_map C J K u0 G f.unop ≫
        lowerShriekInverseImage_map C J K u0 G g.unop :=
  sorry

/-- The simplicial abelian sheaf `n ↦ g_{n!}(a_n⁻¹ G)` on the total site. -/
def lowerShriekInverseImage :
    SimplicialObject (Sheaf (topology C J) AddCommGrpCat.{w}) where
  obj n :=
    (abelianLowerShriek C J n.unop).obj
      ((IsAugmentation.abelianStageInverseImage C J K u0 n.unop).obj G)
  map f := lowerShriekInverseImage_map C J K u0 G f.unop
  map_id := lowerShriekInverseImage_map_id_op C J K u0 G
  map_comp := lowerShriekInverseImage_map_comp_op C J K u0 G

/-- The value of `lowerShriekInverseImage` at `n` is `g_{n!}(a_n⁻¹ G)`. -/
theorem lowerShriekInverseImage_obj (n : SimplexCategory) :
    (lowerShriekInverseImage C J K u0 G).obj (op n) =
      (abelianLowerShriek C J n).obj
        ((IsAugmentation.abelianStageInverseImage C J K u0 n).obj G) :=
  sorry

/-- The source face map `d_i : g_{(n+1)!}(a_{n+1}⁻¹ G) ⟶ g_{n!}(a_n⁻¹ G)`. -/
def inverseImageFace (n : ℕ) (i : Fin (n + 2)) :
    (lowerShriekInverseImage C J K u0 G).obj (op ⦋n + 1⦌) ⟶
      (lowerShriekInverseImage C J K u0 G).obj (op ⦋n⦌) :=
  (lowerShriekInverseImage C J K u0 G).δ i

/-- The face map `inverseImageFace i` is the simplicial operator `δ i`. -/
theorem inverseImageFace_eq (n : ℕ) (i : Fin (n + 2)) :
    inverseImageFace C J K u0 G n i = (lowerShriekInverseImage C J K u0 G).δ i :=
  sorry

/-- The component of the augmentation `g_{n!}(a_n⁻¹ G) ⟶ a⁻¹ G` at a simplex `n`. -/
def inverseImageAugmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (lowerShriekInverseImage C J K u0 G).obj n ⟶
      (IsAugmentation.abelianInverseImage C J K u0).obj G :=
  ((abelianLowerShriek_adjunction C J n.unop).homEquiv
      ((IsAugmentation.abelianStageInverseImage C J K u0 n.unop).obj G)
      ((IsAugmentation.abelianInverseImage C J K u0).obj G)).symm
    (restrictAbelianInverseImageIso C J K u0 G n.unop).inv

/-- Naturality of the degreewise augmentation `g_{n!}(a_n⁻¹ G) ⟶ a⁻¹ G`. -/
theorem inverseImageAugmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (lowerShriekInverseImage C J K u0 G).map f ≫
          inverseImageAugmented_hom_app C J K u0 G m =
        inverseImageAugmented_hom_app C J K u0 G n ≫
          ((SimplicialObject.const _).obj
            ((IsAugmentation.abelianInverseImage C J K u0).obj G)).map f :=
  sorry

/-- The natural transformation `n ↦ g_{n!}(a_n⁻¹ G) ⟶ const (a⁻¹ G)`. -/
def inverseImageAugmented_hom :
    lowerShriekInverseImage C J K u0 G ⟶
      (SimplicialObject.const _).obj
        ((IsAugmentation.abelianInverseImage C J K u0).obj G) where
  app := inverseImageAugmented_hom_app C J K u0 G
  naturality := inverseImageAugmented_hom_naturality C J K u0 G

/-- The augmented simplicial object of `g_{n!}(a_n⁻¹ G)` over `a⁻¹ G`. -/
def inverseImageAugmented :
    SimplicialObject.Augmented (Sheaf (topology C J) AddCommGrpCat.{w}) where
  left := lowerShriekInverseImage C J K u0 G
  right := (IsAugmentation.abelianInverseImage C J K u0).obj G
  hom := inverseImageAugmented_hom C J K u0 G

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]

/-- The alternating-face chain complex `… → g_{2!}(a_2⁻¹ G) → g_{1!}(a_1⁻¹ G) →
g_{0!}(a_0⁻¹ G)`. -/
abbrev inverseImageComplex :
    ChainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℕ :=
  (alternatingFaceMapComplex _).obj
    (SimplicialObject.Augmented.drop.obj (inverseImageAugmented C J K u0 G))

/-- Degree `n` of `inverseImageComplex` is the abelian sheaf `g_{n!}(a_n⁻¹ G)`. -/
theorem inverseImageComplex_X (n : ℕ) :
    (inverseImageComplex C J K u0 G).X n =
      (abelianLowerShriek C J ⦋n⦌).obj
        ((IsAugmentation.abelianStageInverseImage C J K u0 ⦋n⦌).obj G) :=
  sorry

/-- Differentials of `inverseImageComplex` are the alternating sums of face maps. -/
theorem inverseImageComplex_d_eq (n : ℕ) :
    (inverseImageComplex C J K u0 G).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • inverseImageFace C J K u0 G n i :=
  sorry

/-- The canonical chain-map augmentation from `inverseImageComplex` to `a⁻¹ G`
concentrated in degree zero. -/
def inverseImageAugmentation :
    inverseImageComplex C J K u0 G ⟶
      (ChainComplex.single₀ _).obj
        ((IsAugmentation.abelianInverseImage C J K u0).obj G) :=
  AlternatingFaceMapComplex.ε.app (inverseImageAugmented C J K u0 G)

/-- The degree-zero component of `inverseImageAugmentation` is the simplicial
augmentation at `⦋0⦌`. -/
theorem inverseImageAugmentation_f_zero :
    (inverseImageAugmentation C J K u0 G).f 0 =
      (inverseImageAugmented C J K u0 G).hom.app (op ⦋0⦌) :=
  sorry

end CategoryTheory.SimplicialSites
