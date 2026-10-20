/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiPrecoverage

/-!
# Precoverages defined by morphism properties on algebraic spaces

Jointly surjective families satisfying a morphism property form a precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The precoverage of jointly surjective `P`-families of morphisms of algebraic
spaces over `S`. -/
def precoverage {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S)) :
    Precoverage (AlgebraicSpace S) :=
  jointlySurjectivePrecoverage S ⊓ MorphismProperty.precoverage P

/-- An indexed family belongs to `precoverage P` if and only if every morphism
satisfies `P` and the images of the induced maps on points cover `|X|`. -/
theorem ofArrows_mem_precoverage_iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) :
    Presieve.ofArrows Xᵢ f ∈ precoverage P X ↔
      (∀ i, P (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
