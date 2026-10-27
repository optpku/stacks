/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.HigherDirectImage.FlatBaseChange
import StacksCheckRecall

/-!
# Flat base change of étale higher direct images

Along a quasi-compact and quasi-separated morphism of algebraic stacks, étale
higher direct images of locally quasi-coherent modules with the flat base
change property again have the flat base change property.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Lemma 103.7.3: if `f : X ⟶ Y` is a quasi-compact and quasi-separated morphism
of algebraic stacks and `F` is a locally quasi-coherent étale `𝒪_X`-module
with the flat base change property, then the étale higher direct image
`R^i f_* F`, computed with enlarged coefficients, has the flat base change
property. -/
@[stacks 0765] #check
  (AlgebraicGeometry.AlgebraicStack.hasFlatBaseChange_higherDirectImage :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (F : GroupoidsOver.etaleModules X) [IsLocallyQuasiCoherent F]
    [HasFlatBaseChange F] (i : ℕ),
      HasFlatBaseChangeLift Y (GroupoidsOver.moduleHigherDirectImage f F i))
