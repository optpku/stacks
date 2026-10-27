/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage.Kunneth
import StacksCheckRecall

/-! Easy Künneth formula for quasi-coherent structure sheaves. -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory
noncomputable section
universe u

/- Lemma 106.16.5: the canonical Künneth morphism is an isomorphism. -/
@[stacks 0GRN] #check (AlgebraicGeometry.GroupoidsOver.QCoh.kunnethMap_isIso :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (a : Y ⟶ X) (b : Z ⟶ X)
    (ha : FiberedCategoryOver.Groupoids.relativelyRepresentable a)
    (hb : FiberedCategoryOver.Groupoids.relativelyRepresentable b)
    [AlgebraicStack.QuasiCompact a] [AlgebraicStack.QuasiSeparated a]
    [AlgebraicStack.Flat a]
    [AlgebraicStack.QuasiCompact b] [AlgebraicStack.QuasiSeparated b]
    [AlgebraicStack.Flat b]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)]
    [AlgebraicStack.QuasiCompact (AlgebraicGeometry.GroupoidsOver.QCoh.fibreProductHom a b)]
    [AlgebraicStack.QuasiSeparated (AlgebraicGeometry.GroupoidsOver.QCoh.fibreProductHom a b)],
    IsIso (AlgebraicGeometry.GroupoidsOver.QCoh.kunnethMap a b))

