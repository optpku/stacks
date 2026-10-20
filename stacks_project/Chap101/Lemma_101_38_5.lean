/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.38.5: Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact morphism of algebraic
stacks. Then formation of the scheme-theoretic image commutes with flat base
change. -/
@[stacks 0CMK] #check
  (AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage.of_twoFibreProduct_flat :
    ∀ {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y]
      [AlgebraicStack Y'] [AlgebraicStack Z]
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
      (g : Y' ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat g]
      (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage f toImage ι]
      (α : toImage ≫ ι ≅ f),
      AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
        (AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage.pullbackToImage
          f toImage ι g α)
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} ι g))
