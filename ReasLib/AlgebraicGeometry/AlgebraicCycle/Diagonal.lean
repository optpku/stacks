/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Fundamental
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product

/-!
# Diagonal cycles

This file defines the cycle of the diagonal of a variety over a field and records its
dimension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- The diagonal cycle of a variety is the pushforward of its fundamental cycle along the
diagonal morphism. -/
noncomputable def diagonal {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] : AlgebraicCycle (X ⨯ X).left ℤ :=
  AlgebraicCycle.map
    (pullback.diagonal X.hom ≫ (Over.prodLeftIsoPullback X X).inv)
    (X.hom.relativeDimensionFunction (fun _ ↦ 0))
    ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0))
    (@AlgebraicCycle.fundamental X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (X.dimension : ℤ))

/-- The diagonal cycle is the pushforward of the fundamental cycle along the diagonal. -/
theorem diagonal_def {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] :
    diagonal X =
      AlgebraicCycle.map
        (pullback.diagonal X.hom ≫ (Over.prodLeftIsoPullback X X).inv)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0))
        (@AlgebraicCycle.fundamental X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (X.dimension : ℤ)) := sorry

/-- The diagonal cycle has degree equal to the dimension of the variety. -/
theorem diagonal_mem_dimensionSubgroup {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] :
    diagonal X ∈ dimensionSubgroup
      ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0))
      (X.dimension : ℤ) := sorry

end AlgebraicGeometry.AlgebraicCycle
