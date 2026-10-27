/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Map
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Functoriality

/-!
# Equivalence of residual gerbes from a kernel-pair comparison

An equivalence of kernel pairs for a field-valued representative induces an
equivalence between residual gerbes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- If a morphism of algebraic stacks carries `x` to `y` and its kernel-pair
comparison is an equivalence for a field-valued representative of `x`, then
every morphism between the residual gerbes whose square with the inclusions
commutes up to 2-isomorphism is an equivalence. -/
@[stacks 0DTI]
theorem map_isEquivalence {S : Scheme.{u}} {X Y Zx Zy : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Zx] [AlgebraicStack Zy]
    (f : X ⟶ Y) {x : Points X} {y : Points Y} (ιx : Zx ⟶ X) (ιy : Zy ⟶ Y)
    [IsResidualGerbe ιx x] [IsResidualGerbe ιy y]
    (h_image : Points.map f x = y) (p : FieldValuedPoint X)
    (hp : Points.mk p = x)
    (h_iso : (toBasedFunctor (kernelPairMap p.hom f)).IsEquivalence)
    (g : Zx ⟶ Zy) (hg : Nonempty (g ≫ ιy ≅ ιx ≫ f)) :
    (toBasedFunctor g).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
