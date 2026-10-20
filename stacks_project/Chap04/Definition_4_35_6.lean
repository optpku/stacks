/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
import StacksCheckRecall

@[expose] public section

universe u v w vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Definition 4.35.6 (1): categories fibred in groupoids over `C` are represented by the
canonical full subbicategory `FiberedCategoryOver.Groupoids C` of based categories whose
projection is fibred in groupoids. -/
@[stacks 02XS "(1)"]
#check (FiberedCategoryOver.Groupoids.{u, v, w, vS} C :
  Type max (w + 1) (vS + 1) u v)

/- Definition 4.35.6 (2): `1`-morphisms are the inherited homs of
`FiberedCategoryOver.Groupoids C`, equivalently based functors over `C`; no parallel morphism
carrier is introduced. -/
@[stacks 02XS "(2)"]
#check (fun (X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) ↦ (X ⟶ Y) :
  FiberedCategoryOver.Groupoids.{u, v, w, vS} C →
    FiberedCategoryOver.Groupoids.{u, v, w, vS} C → Type max w vS)

variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
variable (F G : X ⟶ Y)

/- Definition 4.35.6 (3): a `2`-morphism between `F` and `G` is the inherited morphism in the
hom-category, represented by a vertical based natural transformation. -/
@[stacks 02XS "(3)"]
#check ((F ⟶ G) : Type max w vS)

/- Definition 4.35.6 (4): the hom-categories are groupoids, so
`FiberedCategoryOver.Groupoids C` is canonically a `(2,1)`-category without applying `Pith`. -/
@[stacks 02XS "(4)"]
#check (inferInstance :
  Bicategory.IsLocallyGroupoid (FiberedCategoryOver.Groupoids.{u, v, w, vS} C))

end CategoryTheory
