/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationAbelian

/-!
# Augmented alternating-face resolutions on fiberwise simplicial sites
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [IsFiberwiseSite F J]
variable [IsAugmentation F J K u0]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable (G : Sheaf K.toGrothendieck AddCommGrpCat.{w})

/-- The structure map `g_{m!}(a_m⁻¹ G) ⟶ g_{n!}(a_n⁻¹ G)` induced by a fiberwise simplex operator
`φ : n ⟶ m`. -/
def fiberLowerShriekInverseImage_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberAbelianLowerShriek F J m).obj
      ((IsAugmentation.abelianStageInverseImage F J K u0 m).obj G) ⟶
    (fiberAbelianLowerShriek F J n).obj
      ((IsAugmentation.abelianStageInverseImage F J K u0 n).obj G) :=
  ((fiberAbelianLowerShriek_adjunction F J m).homEquiv
      ((IsAugmentation.abelianStageInverseImage F J K u0 m).obj G)
      ((fiberAbelianLowerShriek F J n).obj
        ((IsAugmentation.abelianStageInverseImage F J K u0 n).obj G))).symm
    ((IsAugmentation.abelianStageInverseImage_comp F J K u0 φ).inv.app G ≫
      fiberAbelianLowerShriek_component F J φ
        ((IsAugmentation.abelianStageInverseImage F J K u0 n).obj G))

/-- Identity simplex operators induce identity structure maps. -/
theorem fiberLowerShriekInverseImage_map_id (n : SimplexCategory) :
    fiberLowerShriekInverseImage_map F J K u0 G (𝟙 n) =
      𝟙 ((fiberAbelianLowerShriek F J n).obj
        ((IsAugmentation.abelianStageInverseImage F J K u0 n).obj G)) := sorry

/-- Structure maps of `n ↦ g_{n!}(a_n⁻¹ G)` are functorial in fiberwise simplex operators. -/
theorem fiberLowerShriekInverseImage_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    fiberLowerShriekInverseImage_map F J K u0 G (ψ ≫ φ) =
      fiberLowerShriekInverseImage_map F J K u0 G φ ≫
        fiberLowerShriekInverseImage_map F J K u0 G ψ := sorry

/-- The simplicial abelian sheaf `n ↦ g_{n!}(a_n⁻¹ G)` on the total fiberwise site. -/
def fiberLowerShriekInverseImage :
    SimplicialObject (Sheaf (topology F J) AddCommGrpCat.{w}) where
  obj n :=
    (fiberAbelianLowerShriek F J n.unop).obj
      ((IsAugmentation.abelianStageInverseImage F J K u0 n.unop).obj G)
  map f := fiberLowerShriekInverseImage_map F J K u0 G f.unop
  map_id n := fiberLowerShriekInverseImage_map_id F J K u0 G n.unop
  map_comp f g := fiberLowerShriekInverseImage_map_comp F J K u0 G g.unop f.unop

/-- The value of `fiberLowerShriekInverseImage` at `n` is `g_{n!}(a_n⁻¹ G)`. -/
theorem fiberLowerShriekInverseImage_obj (n : SimplexCategory) :
    (fiberLowerShriekInverseImage F J K u0 G).obj (op n) =
      (fiberAbelianLowerShriek F J n).obj
        ((IsAugmentation.abelianStageInverseImage F J K u0 n).obj G) := sorry

/-- The face map `d_i : g_{(n+1)!}(a_{n+1}⁻¹ G) ⟶ g_{n!}(a_n⁻¹ G)`. -/
def fiberInverseImageFace (n : ℕ) (i : Fin (n + 2)) :
    (fiberLowerShriekInverseImage F J K u0 G).obj (op ⦋n + 1⦌) ⟶
      (fiberLowerShriekInverseImage F J K u0 G).obj (op ⦋n⦌) :=
  (fiberLowerShriekInverseImage F J K u0 G).δ i

/-- The component of the fiberwise augmentation `g_{n!}(a_n⁻¹ G) ⟶ a⁻¹ G` at a simplex `n`. -/
def fiberInverseImageAugmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (fiberLowerShriekInverseImage F J K u0 G).obj n ⟶
      (IsAugmentation.abelianInverseImage F J K u0).obj G :=
  ((fiberAbelianLowerShriek_adjunction F J n.unop).homEquiv
      ((IsAugmentation.abelianStageInverseImage F J K u0 n.unop).obj G)
      ((IsAugmentation.abelianInverseImage F J K u0).obj G)).symm
    (IsAugmentation.restrictAbelianInverseImageIso F J K u0 G n.unop).inv

/-- Naturality of the degreewise fiberwise augmentation `g_{n!}(a_n⁻¹ G) ⟶ a⁻¹ G`. -/
private theorem fiberInverseImageAugmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (fiberLowerShriekInverseImage F J K u0 G).map f ≫
          fiberInverseImageAugmented_hom_app F J K u0 G m =
        fiberInverseImageAugmented_hom_app F J K u0 G n ≫
          ((SimplicialObject.const _).obj
            ((IsAugmentation.abelianInverseImage F J K u0).obj G)).map f := sorry

/-- The natural transformation `n ↦ g_{n!}(a_n⁻¹ G) ⟶ const (a⁻¹ G)`. -/
def fiberInverseImageAugmented_hom :
    fiberLowerShriekInverseImage F J K u0 G ⟶
      (SimplicialObject.const _).obj
        ((IsAugmentation.abelianInverseImage F J K u0).obj G) where
  app := fiberInverseImageAugmented_hom_app F J K u0 G
  naturality := fiberInverseImageAugmented_hom_naturality F J K u0 G

/-- The augmented simplicial object of `g_{n!}(a_n⁻¹ G)` over `a⁻¹ G`. -/
def fiberInverseImageAugmented :
    SimplicialObject.Augmented (Sheaf (topology F J) AddCommGrpCat.{w}) where
  left := fiberLowerShriekInverseImage F J K u0 G
  right := (IsAugmentation.abelianInverseImage F J K u0).obj G
  hom := fiberInverseImageAugmented_hom F J K u0 G

variable [HasSheafify (topology F J) AddCommGrpCat.{w}]

/-- The alternating-face chain complex `… → g_{2!}(a_2⁻¹ G) → g_{1!}(a_1⁻¹ G) → g_{0!}(a_0⁻¹ G)`. -/
abbrev fiberInverseImageComplex :
    ChainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℕ :=
  (alternatingFaceMapComplex _).obj
    (SimplicialObject.Augmented.drop.obj (fiberInverseImageAugmented F J K u0 G))

/-- Degree `n` of `fiberInverseImageComplex` is the abelian sheaf `g_{n!}(a_n⁻¹ G)`. -/
theorem fiberInverseImageComplex_X (n : ℕ) :
    (fiberInverseImageComplex F J K u0 G).X n =
      (fiberAbelianLowerShriek F J ⦋n⦌).obj
        ((IsAugmentation.abelianStageInverseImage F J K u0 ⦋n⦌).obj G) := sorry

/-- Differentials of `fiberInverseImageComplex` are the alternating sums of face maps. -/
theorem fiberInverseImageComplex_d_eq (n : ℕ) :
    (fiberInverseImageComplex F J K u0 G).d (n + 1) n =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • fiberInverseImageFace F J K u0 G n i := sorry

/-- The canonical chain-map augmentation from `fiberInverseImageComplex` to `a⁻¹ G` concentrated
in degree zero. -/
def fiberInverseImageAugmentation :
    fiberInverseImageComplex F J K u0 G ⟶
      (ChainComplex.single₀ _).obj
        ((IsAugmentation.abelianInverseImage F J K u0).obj G) :=
  AlternatingFaceMapComplex.ε.app (fiberInverseImageAugmented F J K u0 G)

/-- The canonical augmentation of the fiberwise alternating-face complex of abelian inverse images
is a quasi-isomorphism. -/
instance fiberInverseImageAugmentation_quasiIso :
    QuasiIso
      (fiberInverseImageAugmentation F J K u0 G :
        fiberInverseImageComplex F J K u0 G ⟶
          (ChainComplex.single₀ _).obj
            ((IsAugmentation.abelianInverseImage F J K u0).obj G)) := sorry

end CategoryTheory.Grothendieck
