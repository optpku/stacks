/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction
public import stacks_project.Chap94.Lemma_94_16_1_KernelPair
public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe

/-!
# Residual-gerbe maps from a kernel-pair isomorphism

A morphism of algebraic stacks induces an isomorphism of residual gerbes
when the kernel pair of some field-valued representative is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The comparison of kernel pairs induced by postcomposition with `f`,
sending `U ×_X U` to `U ×_Y U`. -/
def kernelPairMap {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    (p : U ⟶ X) (f : X ⟶ Y) :
    kernelPair p ⟶ kernelPair (p ≫ f) :=
  TwoFibreProduct.map.{u + 1, u, u + 1, u}
    (CospanTransform.mk (𝟙 U) (𝟙 U) f (λ_ (p ≫ f)) (λ_ (p ≫ f)))

/-- `kernelPairMap p f` is the two-fibre-product map of the postcomposition
cospan with vertex maps `𝟙 U`, `𝟙 U`, and `f`. -/
theorem kernelPairMap_eq {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    (p : U ⟶ X) (f : X ⟶ Y) :
    kernelPairMap p f =
      TwoFibreProduct.map.{u + 1, u, u + 1, u}
        (CospanTransform.mk (𝟙 U) (𝟙 U) f (λ_ (p ≫ f)) (λ_ (p ≫ f))) :=
  sorry

namespace IsResidualGerbe

/-- Lemma 100.11.14: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`x ∈ |X|` with image `y ∈ |Y|`. Assume residual gerbes `ιx : Zx ⟶ X` and
`ιy : Zy ⟶ Y` of `x` and `y` exist, and that some field-valued point
`p : Spec(k) ⟶ X` in the class of `x` has
`kernelPairMap p.hom f : Spec(k) ×_X Spec(k) ⟶ Spec(k) ×_Y Spec(k)` an
isomorphism. Then any 1-morphism `g : Zx ⟶ Zy` filling the residual-gerbe
square is an isomorphism. -/
@[stacks 0DTI]
theorem map_isEquivalence {S : Scheme.{u}} {X Y Zx Zy : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Zx] [AlgebraicStack Zy]
    (f : X ⟶ Y) {x : Points X} {y : Points Y} (ιx : Zx ⟶ X) (ιy : Zy ⟶ Y)
    [IsResidualGerbe ιx x] [IsResidualGerbe ιy y]
    (h_image : Points.map f x = y) (p : FieldValuedPoint X)
    (hp : Points.mk p = x)
    (h_iso : (toBasedFunctor (kernelPairMap p.hom f)).IsEquivalence)
    (g : Zx ⟶ Zy) (hg : Nonempty (g ≫ ιy ≅ ιx ≫ f)) :
    (toBasedFunctor g).IsEquivalence :=
  sorry

end IsResidualGerbe

end AlgebraicGeometry.AlgebraicStack
