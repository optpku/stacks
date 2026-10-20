/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Pullback of quasi-coherent modules

The canonical pullback of module sheaves on categories fibred in groupoids
over the big fppf site restricts to their quasi-coherent full subcategories.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/-- Pullback of modules along a morphism of categories fibred in groupoids
sends quasi-coherent sheaves to quasi-coherent sheaves. -/
theorem modulePullback_le_inverseImage :
    quasiCoherentModuleProperty Y ≤
      (quasiCoherentModuleProperty X).inverseImage (modulePullback f) :=
  sorry

namespace QCoh

/-- Restriction of module pullback to quasi-coherent modules. -/
def pullback : QCoh Y ⥤ QCoh X :=
  ObjectProperty.FullSubcategory.restrict (modulePullback f)
    (modulePullback_le_inverseImage f)

/-- The underlying module sheaf of quasi-coherent pullback is module pullback. -/
theorem pullback_obj (G : QCoh Y) :
    ((pullback f).obj G).obj = (modulePullback f).obj G.obj :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
