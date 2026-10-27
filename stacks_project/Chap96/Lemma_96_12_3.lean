/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent.Pullback
import StacksCheckRecall

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

/- Lemma 96.12.3: The pullback functor `f^* = f⁻¹` along a 1-morphism of
categories fibred in groupoids preserves locally quasi-coherent étale modules. -/
@[stacks 06WL] #check
  (AlgebraicGeometry.GroupoidsOver.moduleInverseImage_isLocallyQuasiCoherent :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
      (G : GroupoidsOver.etaleModules Y) [GroupoidsOver.IsLocallyQuasiCoherent G],
      GroupoidsOver.IsLocallyQuasiCoherent ((GroupoidsOver.etaleModuleInverseImage f).obj G))
