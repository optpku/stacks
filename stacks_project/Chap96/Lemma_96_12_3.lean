/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap96.Lemma_96_12_3_Pullback

/-!
# Lemma 96.12.3

The pullback functor `f^* = f⁻¹` along a 1-morphism of categories fibred in
groupoids preserves locally quasi-coherent étale modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} (f : X ⟶ Y)
variable (G : etaleModules Y)
variable [IsLocallyQuasiCoherent G]

/-- Lemma 96.12.3: a 1-morphism `f : X ⟶ Y` of categories fibred in groupoids
over `(Sch/S)_fppf` induces `f^* = f⁻¹ : Mod(Y_étale, O_Y) ⟶ Mod(X_étale, O_X)`,
which sends locally quasi-coherent étale `O_Y`-modules to locally quasi-coherent
étale `O_X`-modules. -/
@[stacks 06WL]
instance moduleInverseImage_isLocallyQuasiCoherent :
    IsLocallyQuasiCoherent ((moduleInverseImage f).obj G) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
