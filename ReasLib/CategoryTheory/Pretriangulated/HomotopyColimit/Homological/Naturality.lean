/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Homological.Image
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Homological Image Comparisons

The image cocone and comparison are natural independently in a morphism of
telescope presentations and in a natural transformation of target functors.
These equations are intended to eliminate repeated colimit extensionality
arguments in applications.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

noncomputable section

namespace CategoryTheory.HomotopyColimit.Presentation

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A]

namespace Hom

variable {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
variable {P : Presentation S X} {Q : Presentation T Y}

/-- Applying a functor to a morphism of presentations gives the stagewise naturality
equation between the two image cocones. -/
@[reassoc, stacks 0CRI]
theorem imageCocone_naturality (φ : Hom α P Q) (H : D ⥤ A) (n : ℕ) :
    (imageCocone P H).ι.app n ≫ H.map φ.hom =
      H.map (α.app n) ≫ (imageCocone Q H).ι.app n := sorry

/-- The morphism of image cocones induced by a morphism of telescope presentations. -/
@[stacks 0CRI]
def imageCoconeHom (φ : Hom α P Q) (H : D ⥤ A) :
    imageCocone P H ⟶
      (Cocone.precompose (Functor.whiskerRight α H)).obj (imageCocone Q H) :=
  H.mapCoconeMorphism φ.coconeHom ≫ (Functor.mapCoconePrecompose H).hom

/-- The point map of the induced image-cocone morphism is the image of the underlying
presentation map. -/
@[simp]
theorem imageCoconeHom_hom (φ : Hom α P Q) (H : D ⥤ A) :
    (imageCoconeHom φ H).hom = H.map φ.hom := sorry

/-- The canonical image comparisons are natural in a morphism of telescope presentations. -/
@[reassoc, stacks 0CRI]
theorem imageComparison_naturality (φ : Hom α P Q) (H : D ⥤ A)
    [HasColimit (S ⋙ H)] [HasColimit (T ⋙ H)] :
    colimMap (Functor.whiskerRight α H) ≫ imageComparison Q H =
      imageComparison P H ≫ H.map φ.hom := sorry

end Hom

namespace ImageCocone

variable {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
variable {H G : D ⥤ A}

/-- The image cocone is natural in a natural transformation of target functors. -/
@[reassoc, stacks 0CRK]
theorem natTrans_naturality (η : H ⟶ G) (n : ℕ) :
    (imageCocone P H).ι.app n ≫ η.app X =
      (Functor.whiskerLeft K η).app n ≫ (imageCocone P G).ι.app n := sorry

/-- A target natural transformation satisfies the image-cocone morphism equation. -/
theorem map_w (η : H ⟶ G) (n : ℕ) :
    (imageCocone P H).ι.app n ≫ η.app X =
      ((Cocone.precompose (Functor.whiskerLeft K η)).obj (imageCocone P G)).ι.app n := sorry

/-- The morphism of image cocones induced by a natural transformation of target functors. -/
@[stacks 0CRK]
def map (η : H ⟶ G) :
    imageCocone P H ⟶
      (Cocone.precompose (Functor.whiskerLeft K η)).obj (imageCocone P G) where
  hom := η.app X
  w := map_w P η

/-- The point map of the image-cocone morphism induced by `η` is `η.app X`. -/
@[simp]
theorem map_hom (η : H ⟶ G) : (map P η).hom = η.app X := sorry

end ImageCocone

namespace ImageComparison

variable {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
variable {H G : D ⥤ A}

/-- The canonical image comparison is natural in a natural transformation of target
functors. -/
@[reassoc, stacks 0CRK]
theorem natTrans_naturality (η : H ⟶ G)
    [HasColimit (K ⋙ H)] [HasColimit (K ⋙ G)] :
    colimMap (Functor.whiskerLeft K η) ≫ imageComparison P G =
      imageComparison P H ≫ η.app X := sorry

end ImageComparison

end CategoryTheory.HomotopyColimit.Presentation

end
