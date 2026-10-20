/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Comparison
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.RingTheory.Valuation.Extension

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

namespace AlgebraicGeometry.AlgebraicStack.Flat

/-- A valuation-ring point of the target of a flat morphism of algebraic stacks
lifts after an extension of valuation rings whenever its closed point lies in
the image of the map on points. The lift forms a 2-commutative square with the
canonical morphism of spectra. -/
@[stacks 0DN5]
theorem exists_isExtensionOfValuationRings {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} [Flat f] {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (σ : Spec (.of A) ⟶ S) (g : GroupoidsOver.slice (Over.mk σ) ⟶ Y)
    (h_image : Points.map g (Points.ofSlice (IsLocalRing.closedPoint A)) ∈
      Set.range (Points.map f)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : ValuationRing A')
      (_ : Algebra A A') (_ : IsExtensionOfValuationRings A A')
      (lift :
        GroupoidsOver.slice
            (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ σ)) ⟶
          X),
      Nonempty
        (FiberedCategoryOver.Groupoids.overMap
            (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A A'))) rfl) ≫ g ≅
          lift ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Flat
