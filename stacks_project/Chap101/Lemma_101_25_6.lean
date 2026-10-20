/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat.Valuation
import StacksCheckRecall

/-!
# Lifting valuation rings through flat morphisms of algebraic stacks

A flat morphism of algebraic stacks lifts a valuation-ring point of the target
after an extension of valuation rings, provided the closed point of the source
spectrum lands in the image of the map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.25.6: Let `f : X ⟶ Y` be a flat morphism of algebraic stacks.
Let `Spec(A) ⟶ Y` be a morphism where `A` is a valuation ring. If the closed
point of `Spec(A)` maps to a point of `|Y|` in the image of `|X| ⟶ |Y|`, then
there exists a 2-commutative diagram `Spec(A') ⟶ X` over `Spec(A) ⟶ Y` where
`A → A'` is an extension of valuation rings in the sense of
`IsExtensionOfValuationRings` (More on Algebra, Definition 15.124.1). -/
@[stacks 0DN5] #check
  (AlgebraicGeometry.AlgebraicStack.Flat.exists_isExtensionOfValuationRings :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} [Flat f] {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (σ : Spec (.of A) ⟶ S) (g : GroupoidsOver.slice (Over.mk σ) ⟶ Y)
    (h_image : Points.map g (Points.ofSlice (IsLocalRing.closedPoint A)) ∈
      Set.range (Points.map f)),
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : ValuationRing A')
      (_ : Algebra A A') (_ : IsExtensionOfValuationRings A A')
      (lift :
        GroupoidsOver.slice
            (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ σ)) ⟶
          X),
      Nonempty
        (FiberedCategoryOver.Groupoids.overMap
            (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A A'))) rfl) ≫ g ≅
          lift ≫ f))

end AlgebraicGeometry.AlgebraicStack
